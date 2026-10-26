import V185TrunkScan23Chunk0835

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_4948032 : List Nat := [2, 1, 1, 2, 2, 4, 3, 2, 1, 5]
def baseStart_4948032 : Nat := 118140960795 + 4948032 * 2 ^ 59
def prefixEnd_4948032 : Nat := 4983230072969 + 3 ^ 40 * 4948032 * 2
def baseEnd_4948032 : Nat := 846906236609230011914807

theorem tailTrace_4948032 : CollatzResearch.WordTrace tailWord_4948032 prefixEnd_4948032 846906236609230011914807 := by
  unfold tailWord_4948032
  simp only [CollatzResearch.WordTrace]
  refine ⟨90234776605066297716159175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120313035473421730288212233 90234776605066297716159175)
  ·
    refine ⟨135352164907599446574238763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90234776605066297716159175 135352164907599446574238763)
    ·
      refine ⟨203028247361399169861358145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 135352164907599446574238763 203028247361399169861358145)
      ·
        refine ⟨152271185521049377396018609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 203028247361399169861358145 152271185521049377396018609)
        ·
          refine ⟨114203389140787033047013957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 152271185521049377396018609 114203389140787033047013957)
          ·
            refine ⟨21413135463897568696315117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 114203389140787033047013957 21413135463897568696315117)
            ·
              refine ⟨8029925798961588261118169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21413135463897568696315117 8029925798961588261118169)
              ·
                refine ⟨6022444349221191195838627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8029925798961588261118169 6022444349221191195838627)
                ·
                  refine ⟨9033666523831786793757941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6022444349221191195838627 9033666523831786793757941)
                  ·
                    refine ⟨846906236609230011914807, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9033666523831786793757941 846906236609230011914807)
                    ·
                      rfl

theorem cell23_4948032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 3, 2, 1, 5].length) (baseStart_4948032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4948032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4948032 prefixEnd_4948032 := by exact prefixLift 4948032
  have htrace : WordTrace (prefixWord ++ tailWord_4948032) baseStart_4948032 baseEnd_4948032 := by
    simpa [prefixWord, tailWord_4948032, baseEnd_4948032] using wordTrace_append hprefix tailTrace_4948032
  have hstable : (prefixWord ++ tailWord_4948032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4948032).length < 2 ^ (prefixWord ++ tailWord_4948032).sum := by decide
  have hdescent : baseEnd_4948032 < baseStart_4948032 := by decide
  rcases family_descends (prefixWord ++ tailWord_4948032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4948039 : List Nat := [1, 1, 4, 1, 3, 1, 4, 1, 2, 3, 2]
def baseStart_4948039 : Nat := 118140960795 + 4948039 * 2 ^ 59
def prefixEnd_4948039 : Nat := 4983230072969 + 3 ^ 40 * 4948039 * 2
def baseEnd_4948039 : Nat := 2540722304192271508356889

theorem tailTrace_4948039 : CollatzResearch.WordTrace tailWord_4948039 prefixEnd_4948039 2540722304192271508356889 := by
  unfold tailWord_4948039
  simp only [CollatzResearch.WordTrace]
  refine ⟨180469808521107235627823171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120313205680738157085215447 180469808521107235627823171)
  ·
    refine ⟨270704712781660853441734757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 180469808521107235627823171 270704712781660853441734757)
    ·
      refine ⟨50757133646561410020325267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 270704712781660853441734757 50757133646561410020325267)
      ·
        refine ⟨76135700469842115030487901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50757133646561410020325267 76135700469842115030487901)
        ·
          refine ⟨28550887676190793136432963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 76135700469842115030487901 28550887676190793136432963)
          ·
            refine ⟨42826331514286189704649445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28550887676190793136432963 42826331514286189704649445)
            ·
              refine ⟨8029937158928660569621771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 42826331514286189704649445 8029937158928660569621771)
              ·
                refine ⟨12044905738392990854432657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8029937158928660569621771 12044905738392990854432657)
                ·
                  refine ⟨9033679303794743140824493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12044905738392990854432657 9033679303794743140824493)
                  ·
                    refine ⟨3387629738923028677809185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9033679303794743140824493 3387629738923028677809185)
                    ·
                      refine ⟨2540722304192271508356889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3387629738923028677809185 2540722304192271508356889)
                      ·
                        rfl

theorem cell23_4948039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 4, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 4, 1, 2, 3, 2].length) (baseStart_4948039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4948039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4948039 prefixEnd_4948039 := by exact prefixLift 4948039
  have htrace : WordTrace (prefixWord ++ tailWord_4948039) baseStart_4948039 baseEnd_4948039 := by
    simpa [prefixWord, tailWord_4948039, baseEnd_4948039] using wordTrace_append hprefix tailTrace_4948039
  have hstable : (prefixWord ++ tailWord_4948039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4948039).length < 2 ^ (prefixWord ++ tailWord_4948039).sum := by decide
  have hdescent : baseEnd_4948039 < baseStart_4948039 := by decide
  rcases family_descends (prefixWord ++ tailWord_4948039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4948065 : List Nat := [1, 2, 3, 1, 1, 2, 1, 1, 5, 2, 4]
def baseStart_4948065 : Nat := 118140960795 + 4948065 * 2 ^ 59
def prefixEnd_4948065 : Nat := 4983230072969 + 3 ^ 40 * 4948065 * 2
def baseEnd_4948065 : Nat := 2540735654689288406631769

theorem tailTrace_4948065 : CollatzResearch.WordTrace tailWord_4948065 prefixEnd_4948065 2540735654689288406631769 := by
  unfold tailWord_4948065
  simp only [CollatzResearch.WordTrace]
  refine ⟨180470756819013042068269649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120313837879342028045513099 180470756819013042068269649)
  ·
    refine ⟨135353067614259781551202237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 180470756819013042068269649 135353067614259781551202237)
    ·
      refine ⟨50757400355347418081700839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 135353067614259781551202237 50757400355347418081700839)
      ·
        refine ⟨76136100533021127122551259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50757400355347418081700839 76136100533021127122551259)
        ·
          refine ⟨114204150799531690683826889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76136100533021127122551259 114204150799531690683826889)
          ·
            refine ⟨85653113099648768012870167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 114204150799531690683826889 85653113099648768012870167)
            ·
              refine ⟨128479669649473152019305251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 85653113099648768012870167 128479669649473152019305251)
              ·
                refine ⟨192719504474209728028957877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 128479669649473152019305251 192719504474209728028957877)
                ·
                  refine ⟨18067453544457162002714801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 192719504474209728028957877 18067453544457162002714801)
                  ·
                    refine ⟨13550590158342871502036101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18067453544457162002714801 13550590158342871502036101)
                    ·
                      refine ⟨2540735654689288406631769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13550590158342871502036101 2540735654689288406631769)
                      ·
                        rfl

theorem cell23_4948065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 1, 5, 2, 4].length) (baseStart_4948065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4948065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4948065 prefixEnd_4948065 := by exact prefixLift 4948065
  have htrace : WordTrace (prefixWord ++ tailWord_4948065) baseStart_4948065 baseEnd_4948065 := by
    simpa [prefixWord, tailWord_4948065, baseEnd_4948065] using wordTrace_append hprefix tailTrace_4948065
  have hstable : (prefixWord ++ tailWord_4948065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4948065).length < 2 ^ (prefixWord ++ tailWord_4948065).sum := by decide
  have hdescent : baseEnd_4948065 < baseStart_4948065 := by decide
  rcases family_descends (prefixWord ++ tailWord_4948065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4948082 : List Nat := [3, 2, 1, 2, 2, 2, 1, 3, 1, 2, 4]
def baseStart_4948082 : Nat := 118140960795 + 4948082 * 2 ^ 59
def prefixEnd_4948082 : Nat := 4983230072969 + 3 ^ 40 * 4948082 * 2
def baseEnd_4948082 : Nat := 2540744383860414840119191

theorem tailTrace_4948082 : CollatzResearch.WordTrace tailWord_4948082 prefixEnd_4948082 2540744383860414840119191 := by
  unfold tailWord_4948082
  simp only [CollatzResearch.WordTrace]
  refine ⟨45117844214987863492909625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 120314251239967635981092333 45117844214987863492909625)
  ·
    refine ⟨33838383161240897619682219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45117844214987863492909625 33838383161240897619682219)
    ·
      refine ⟨50757574741861346429523329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33838383161240897619682219 50757574741861346429523329)
      ·
        refine ⟨38068181056396009822142497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50757574741861346429523329 38068181056396009822142497)
        ·
          refine ⟨28551135792297007366606873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38068181056396009822142497 28551135792297007366606873)
          ·
            refine ⟨21413351844222755524955155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28551135792297007366606873 21413351844222755524955155)
            ·
              refine ⟨32120027766334133287432733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21413351844222755524955155 32120027766334133287432733)
              ·
                refine ⟨12045010412375299982787275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32120027766334133287432733 12045010412375299982787275)
                ·
                  refine ⟨18067515618562949974180913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12045010412375299982787275 18067515618562949974180913)
                  ·
                    refine ⟨13550636713922212480635685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18067515618562949974180913 13550636713922212480635685)
                    ·
                      refine ⟨2540744383860414840119191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13550636713922212480635685 2540744383860414840119191)
                      ·
                        rfl

theorem cell23_4948082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 1, 3, 1, 2, 4].length) (baseStart_4948082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4948082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4948082 prefixEnd_4948082 := by exact prefixLift 4948082
  have htrace : WordTrace (prefixWord ++ tailWord_4948082) baseStart_4948082 baseEnd_4948082 := by
    simpa [prefixWord, tailWord_4948082, baseEnd_4948082] using wordTrace_append hprefix tailTrace_4948082
  have hstable : (prefixWord ++ tailWord_4948082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4948082).length < 2 ^ (prefixWord ++ tailWord_4948082).sum := by decide
  have hdescent : baseEnd_4948082 < baseStart_4948082 := by decide
  rcases family_descends (prefixWord ++ tailWord_4948082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4948086 : List Nat := [5, 1, 1, 2, 1, 2, 1, 1, 5, 2, 2]
def baseStart_4948086 : Nat := 118140960795 + 4948086 * 2 ^ 59
def prefixEnd_4948086 : Nat := 4983230072969 + 3 ^ 40 * 4948086 * 2
def baseEnd_4948086 : Nat := 2540746437783032824469173

theorem tailTrace_4948086 : CollatzResearch.WordTrace tailWord_4948086 prefixEnd_4948086 2540746437783032824469173 := by
  unfold tailWord_4948086
  simp only [CollatzResearch.WordTrace]
  refine ⟨11279470171996060165924007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 120314348501291308436522741 11279470171996060165924007)
  ·
    refine ⟨16919205257994090248886011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11279470171996060165924007 16919205257994090248886011)
    ·
      refine ⟨25378807886991135373329017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16919205257994090248886011 25378807886991135373329017)
      ·
        refine ⟨19034105915243351529996763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25378807886991135373329017 19034105915243351529996763)
        ·
          refine ⟨28551158872865027294995145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19034105915243351529996763 28551158872865027294995145)
          ·
            refine ⟨21413369154648770471246359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28551158872865027294995145 21413369154648770471246359)
            ·
              refine ⟨32120053731973155706869539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21413369154648770471246359 32120053731973155706869539)
              ·
                refine ⟨48180080597959733560304309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32120053731973155706869539 48180080597959733560304309)
                ·
                  refine ⟨4516882556058725021278529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 48180080597959733560304309 4516882556058725021278529)
                  ·
                    refine ⟨3387661917044043765958897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4516882556058725021278529 3387661917044043765958897)
                    ·
                      refine ⟨2540746437783032824469173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3387661917044043765958897 2540746437783032824469173)
                      ·
                        rfl

theorem cell23_4948086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 1, 1, 5, 2, 2].length) (baseStart_4948086 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4948086 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4948086 prefixEnd_4948086 := by exact prefixLift 4948086
  have htrace : WordTrace (prefixWord ++ tailWord_4948086) baseStart_4948086 baseEnd_4948086 := by
    simpa [prefixWord, tailWord_4948086, baseEnd_4948086] using wordTrace_append hprefix tailTrace_4948086
  have hstable : (prefixWord ++ tailWord_4948086).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4948086).length < 2 ^ (prefixWord ++ tailWord_4948086).sum := by decide
  have hdescent : baseEnd_4948086 < baseStart_4948086 := by decide
  rcases family_descends (prefixWord ++ tailWord_4948086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4948092 : List Nat := [2, 2, 2, 1, 1, 5, 3, 7]
def baseStart_4948092 : Nat := 118140960795 + 4948092 * 2 ^ 59
def prefixEnd_4948092 : Nat := 4983230072969 + 3 ^ 40 * 4948092 * 2
def baseEnd_4948092 : Nat := 94101834024702214851635

theorem tailTrace_4948092 : CollatzResearch.WordTrace tailWord_4948092 prefixEnd_4948092 94101834024702214851635 := by
  unfold tailWord_4948092
  simp only [CollatzResearch.WordTrace]
  refine ⟨90235870794957612839751265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120314494393276817119668353 90235870794957612839751265)
  ·
    refine ⟨67676903096218209629813449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90235870794957612839751265 67676903096218209629813449)
    ·
      refine ⟨50757677322163657222360087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67676903096218209629813449 50757677322163657222360087)
      ·
        refine ⟨76136515983245485833540131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50757677322163657222360087 76136515983245485833540131)
        ·
          refine ⟨114204773974868228750310197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76136515983245485833540131 114204773974868228750310197)
          ·
            refine ⟨10706697560143896445341581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 114204773974868228750310197 10706697560143896445341581)
            ·
              refine ⟨4015011585053961167003093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10706697560143896445341581 4015011585053961167003093)
              ·
                refine ⟨94101834024702214851635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4015011585053961167003093 94101834024702214851635)
                ·
                  rfl

theorem cell23_4948092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 5, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 5, 3, 7].length) (baseStart_4948092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4948092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4948092 prefixEnd_4948092 := by exact prefixLift 4948092
  have htrace : WordTrace (prefixWord ++ tailWord_4948092) baseStart_4948092 baseEnd_4948092 := by
    simpa [prefixWord, tailWord_4948092, baseEnd_4948092] using wordTrace_append hprefix tailTrace_4948092
  have hstable : (prefixWord ++ tailWord_4948092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4948092).length < 2 ^ (prefixWord ++ tailWord_4948092).sum := by decide
  have hdescent : baseEnd_4948092 < baseStart_4948092 := by decide
  rcases family_descends (prefixWord ++ tailWord_4948092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4948106 : List Nat := [3, 1, 2, 3, 1, 2, 4, 1, 1, 2, 3]
def baseStart_4948106 : Nat := 118140960795 + 4948106 * 2 ^ 59
def prefixEnd_4948106 : Nat := 4983230072969 + 3 ^ 40 * 4948106 * 2
def baseEnd_4948106 : Nat := 2540756707396122746219081

theorem tailTrace_4948106 : CollatzResearch.WordTrace tailWord_4948106 prefixEnd_4948106 2540756707396122746219081 := by
  unfold tailWord_4948106
  simp only [CollatzResearch.WordTrace]
  refine ⟨45118063052966126517628043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 120314834807909670713674781 45118063052966126517628043)
  ·
    refine ⟨67677094579449189776442065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45118063052966126517628043 67677094579449189776442065)
    ·
      refine ⟨50757820934586892332331549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67677094579449189776442065 50757820934586892332331549)
      ·
        refine ⟨19034182850470084624624331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 50757820934586892332331549 19034182850470084624624331)
        ·
          refine ⟨28551274275705126936936497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19034182850470084624624331 28551274275705126936936497)
          ·
            refine ⟨21413455706778845202702373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28551274275705126936936497 21413455706778845202702373)
            ·
              refine ⟨4015022945021033475506695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21413455706778845202702373 4015022945021033475506695)
              ·
                refine ⟨6022534417531550213260043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4015022945021033475506695 6022534417531550213260043)
                ·
                  refine ⟨9033801626297325319890065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6022534417531550213260043 9033801626297325319890065)
                  ·
                    refine ⟨6775351219722993989917549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9033801626297325319890065 6775351219722993989917549)
                    ·
                      refine ⟨2540756707396122746219081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6775351219722993989917549 2540756707396122746219081)
                      ·
                        rfl

theorem cell23_4948106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 4, 1, 1, 2, 3].length) (baseStart_4948106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4948106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4948106 prefixEnd_4948106 := by exact prefixLift 4948106
  have htrace : WordTrace (prefixWord ++ tailWord_4948106) baseStart_4948106 baseEnd_4948106 := by
    simpa [prefixWord, tailWord_4948106, baseEnd_4948106] using wordTrace_append hprefix tailTrace_4948106
  have hstable : (prefixWord ++ tailWord_4948106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4948106).length < 2 ^ (prefixWord ++ tailWord_4948106).sum := by decide
  have hdescent : baseEnd_4948106 < baseStart_4948106 := by decide
  rcases family_descends (prefixWord ++ tailWord_4948106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4948146 : List Nat := [3, 2, 1, 1, 1, 3, 4, 2, 1, 3, 2]
def baseStart_4948146 : Nat := 118140960795 + 4948146 * 2 ^ 59
def prefixEnd_4948146 : Nat := 4983230072969 + 3 ^ 40 * 4948146 * 2
def baseEnd_4948146 : Nat := 2540777246622302589718897

theorem tailTrace_4948146 : CollatzResearch.WordTrace tailWord_4948146 prefixEnd_4948146 2540777246622302589718897 := by
  unfold tailWord_4948146
  simp only [CollatzResearch.WordTrace]
  refine ⟨45118427782929898225492073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 120315807421146395267978861 45118427782929898225492073)
  ·
    refine ⟨33838820837197423669119055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45118427782929898225492073 33838820837197423669119055)
    ·
      refine ⟨50758231255796135503678583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33838820837197423669119055 50758231255796135503678583)
      ·
        refine ⟨76137346883694203255517875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50758231255796135503678583 76137346883694203255517875)
        ·
          refine ⟨114206020325541304883276813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76137346883694203255517875 114206020325541304883276813)
          ·
            refine ⟨42827257622077989331228805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 114206020325541304883276813 42827257622077989331228805)
            ·
              refine ⟨8030110804139622999605401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 42827257622077989331228805 8030110804139622999605401)
              ·
                refine ⟨6022583103104717249704051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8030110804139622999605401 6022583103104717249704051)
                ·
                  refine ⟨9033874654657075874556077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6022583103104717249704051 9033874654657075874556077)
                  ·
                    refine ⟨3387702995496403452958529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9033874654657075874556077 3387702995496403452958529)
                    ·
                      refine ⟨2540777246622302589718897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3387702995496403452958529 2540777246622302589718897)
                      ·
                        rfl

theorem cell23_4948146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 4, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 4, 2, 1, 3, 2].length) (baseStart_4948146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4948146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4948146 prefixEnd_4948146 := by exact prefixLift 4948146
  have htrace : WordTrace (prefixWord ++ tailWord_4948146) baseStart_4948146 baseEnd_4948146 := by
    simpa [prefixWord, tailWord_4948146, baseEnd_4948146] using wordTrace_append hprefix tailTrace_4948146
  have hstable : (prefixWord ++ tailWord_4948146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4948146).length < 2 ^ (prefixWord ++ tailWord_4948146).sum := by decide
  have hdescent : baseEnd_4948146 < baseStart_4948146 := by decide
  rcases family_descends (prefixWord ++ tailWord_4948146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4948165 : List Nat := [1, 3, 1, 1, 1, 1, 4, 2, 9]
def baseStart_4948165 : Nat := 118140960795 + 4948165 * 2 ^ 59
def prefixEnd_4948165 : Nat := 4983230072969 + 3 ^ 40 * 4948165 * 2
def baseEnd_4948165 : Nat := 282309666972748668375701

theorem tailTrace_4948165 : CollatzResearch.WordTrace tailWord_4948165 prefixEnd_4948165 282309666972748668375701 := by
  unfold tailWord_4948165
  simp only [CollatzResearch.WordTrace]
  refine ⟨180474404118650759146909949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120316269412433839431273299 180474404118650759146909949)
  ·
    refine ⟨67677901544494034680091231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 180474404118650759146909949 67677901544494034680091231)
    ·
      refine ⟨101516852316741052020136847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67677901544494034680091231 101516852316741052020136847)
      ·
        refine ⟨152275278475111578030205271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101516852316741052020136847 152275278475111578030205271)
        ·
          refine ⟨228412917712667367045307907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 152275278475111578030205271 228412917712667367045307907)
          ·
            refine ⟨342619376569001050567961861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 228412917712667367045307907 342619376569001050567961861)
            ·
              refine ⟨64241133106687696981492849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 342619376569001050567961861 64241133106687696981492849)
              ·
                refine ⟨48180849830015772736119637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 64241133106687696981492849 48180849830015772736119637)
                ·
                  refine ⟨282309666972748668375701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 48180849830015772736119637 282309666972748668375701)
                  ·
                    rfl

theorem cell23_4948165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 4, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 4, 2, 9].length) (baseStart_4948165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4948165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4948165 prefixEnd_4948165 := by exact prefixLift 4948165
  have htrace : WordTrace (prefixWord ++ tailWord_4948165) baseStart_4948165 baseEnd_4948165 := by
    simpa [prefixWord, tailWord_4948165, baseEnd_4948165] using wordTrace_append hprefix tailTrace_4948165
  have hstable : (prefixWord ++ tailWord_4948165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4948165).length < 2 ^ (prefixWord ++ tailWord_4948165).sum := by decide
  have hdescent : baseEnd_4948165 < baseStart_4948165 := by decide
  rcases family_descends (prefixWord ++ tailWord_4948165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4948175 : List Nat := [1, 1, 2, 1, 1, 3, 3, 1, 1, 2, 7]
def baseStart_4948175 : Nat := 118140960795 + 4948175 * 2 ^ 59
def prefixEnd_4948175 : Nat := 4983230072969 + 3 ^ 40 * 4948175 * 2
def baseEnd_4948175 : Nat := 2540792137561282976256263

theorem tailTrace_4948175 : CollatzResearch.WordTrace tailWord_4948175 prefixEnd_4948175 2540792137561282976256263 := by
  unfold tailWord_4948175
  simp only [CollatzResearch.WordTrace]
  refine ⟨180474768848614530854773979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120316512565743020569849319 180474768848614530854773979)
  ·
    refine ⟨270712153272921796282160969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 180474768848614530854773979 270712153272921796282160969)
    ·
      refine ⟨203034114954691347211620727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 270712153272921796282160969 203034114954691347211620727)
      ·
        refine ⟨304551172432037020817431091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 203034114954691347211620727 304551172432037020817431091)
        ·
          refine ⟨456826758648055531226146637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 304551172432037020817431091 456826758648055531226146637)
          ·
            refine ⟨171310034493020824209804989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 456826758648055531226146637 171310034493020824209804989)
            ·
              refine ⟨64241262934882809078676871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 171310034493020824209804989 64241262934882809078676871)
              ·
                refine ⟨96361894402324213618015307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 64241262934882809078676871 96361894402324213618015307)
                ·
                  refine ⟨144542841603486320427022961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 96361894402324213618015307 144542841603486320427022961)
                  ·
                    refine ⟨108407131202614740320267221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 144542841603486320427022961 108407131202614740320267221)
                    ·
                      refine ⟨2540792137561282976256263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 108407131202614740320267221 2540792137561282976256263)
                      ·
                        rfl

theorem cell23_4948175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 3, 1, 1, 2, 7].length) (baseStart_4948175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4948175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4948175 prefixEnd_4948175 := by exact prefixLift 4948175
  have htrace : WordTrace (prefixWord ++ tailWord_4948175) baseStart_4948175 baseEnd_4948175 := by
    simpa [prefixWord, tailWord_4948175, baseEnd_4948175] using wordTrace_append hprefix tailTrace_4948175
  have hstable : (prefixWord ++ tailWord_4948175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4948175).length < 2 ^ (prefixWord ++ tailWord_4948175).sum := by decide
  have hdescent : baseEnd_4948175 < baseStart_4948175 := by decide
  rcases family_descends (prefixWord ++ tailWord_4948175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4948192 : List Nat := [2, 1, 1, 3, 1, 3, 2, 1, 1, 5, 3]
def baseStart_4948192 : Nat := 118140960795 + 4948192 * 2 ^ 59
def prefixEnd_4948192 : Nat := 4983230072969 + 3 ^ 40 * 4948192 * 2
def baseEnd_4948192 : Nat := 2540800866732409409743685

theorem tailTrace_4948192 : CollatzResearch.WordTrace tailWord_4948192 prefixEnd_4948192 2540800866732409409743685 := by
  unfold tailWord_4948192
  simp only [CollatzResearch.WordTrace]
  refine ⟨90237694444776471379071415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120316925926368628505428553 90237694444776471379071415)
  ·
    refine ⟨135356541667164707068607123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90237694444776471379071415 135356541667164707068607123)
    ·
      refine ⟨203034812500747060602910685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 135356541667164707068607123 203034812500747060602910685)
      ·
        refine ⟨76138054687780147726091507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 203034812500747060602910685 76138054687780147726091507)
        ·
          refine ⟨114207082031670221589137261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76138054687780147726091507 114207082031670221589137261)
          ·
            refine ⟨42827655761876333095926473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 114207082031670221589137261 42827655761876333095926473)
            ·
              refine ⟨32120741821407249821944855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42827655761876333095926473 32120741821407249821944855)
              ·
                refine ⟨48181112732110874732917283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32120741821407249821944855 48181112732110874732917283)
                ·
                  refine ⟨72271669098166312099375925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 48181112732110874732917283 72271669098166312099375925)
                  ·
                    refine ⟨6775468977953091759316493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 72271669098166312099375925 6775468977953091759316493)
                    ·
                      refine ⟨2540800866732409409743685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6775468977953091759316493 2540800866732409409743685)
                      ·
                        rfl

theorem cell23_4948192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 2, 1, 1, 5, 3].length) (baseStart_4948192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4948192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4948192 prefixEnd_4948192 := by exact prefixLift 4948192
  have htrace : WordTrace (prefixWord ++ tailWord_4948192) baseStart_4948192 baseEnd_4948192 := by
    simpa [prefixWord, tailWord_4948192, baseEnd_4948192] using wordTrace_append hprefix tailTrace_4948192
  have hstable : (prefixWord ++ tailWord_4948192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4948192).length < 2 ^ (prefixWord ++ tailWord_4948192).sum := by decide
  have hdescent : baseEnd_4948192 < baseStart_4948192 := by decide
  rcases family_descends (prefixWord ++ tailWord_4948192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4948259 : List Nat := [1, 1, 1, 4, 2, 2, 3, 2, 3, 4]
def baseStart_4948259 : Nat := 118140960795 + 4948259 * 2 ^ 59
def prefixEnd_4948259 : Nat := 4983230072969 + 3 ^ 40 * 4948259 * 2
def baseEnd_4948259 : Nat := 846945089978753549201959

theorem tailTrace_4948259 : CollatzResearch.WordTrace tailWord_4948259 prefixEnd_4948259 846945089978753549201959 := by
  unfold tailWord_4948259
  simp only [CollatzResearch.WordTrace]
  refine ⟨180477832580310213200831831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120318555053540142133887887 180477832580310213200831831)
  ·
    refine ⟨270716748870465319801247747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 180477832580310213200831831 270716748870465319801247747)
    ·
      refine ⟨406075123305697979701871621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 270716748870465319801247747 406075123305697979701871621)
      ·
        refine ⟨76139085619818371194100929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 406075123305697979701871621 76139085619818371194100929)
        ·
          refine ⟨57104314214863778395575697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 76139085619818371194100929 57104314214863778395575697)
          ·
            refine ⟨42828235661147833796681773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57104314214863778395575697 42828235661147833796681773)
            ·
              refine ⟨16060588372930437673755665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 42828235661147833796681773 16060588372930437673755665)
              ·
                refine ⟨12045441279697828255316749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16060588372930437673755665 12045441279697828255316749)
                ·
                  refine ⟨4517040479886685595743781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12045441279697828255316749 4517040479886685595743781)
                  ·
                    refine ⟨846945089978753549201959, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4517040479886685595743781 846945089978753549201959)
                    ·
                      rfl

theorem cell23_4948259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 3, 2, 3, 4].length) (baseStart_4948259 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4948259 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4948259 prefixEnd_4948259 := by exact prefixLift 4948259
  have htrace : WordTrace (prefixWord ++ tailWord_4948259) baseStart_4948259 baseEnd_4948259 := by
    simpa [prefixWord, tailWord_4948259, baseEnd_4948259] using wordTrace_append hprefix tailTrace_4948259
  have hstable : (prefixWord ++ tailWord_4948259).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4948259).length < 2 ^ (prefixWord ++ tailWord_4948259).sum := by decide
  have hdescent : baseEnd_4948259 < baseStart_4948259 := by decide
  rcases family_descends (prefixWord ++ tailWord_4948259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4948263 : List Nat := [1, 1, 8, 1, 1, 1, 1, 1, 1, 7]
def baseStart_4948263 : Nat := 118140960795 + 4948263 * 2 ^ 59
def prefixEnd_4948263 : Nat := 4983230072969 + 3 ^ 40 * 4948263 * 2
def baseEnd_4948263 : Nat := 846945774619626210651953

theorem tailTrace_4948263 : CollatzResearch.WordTrace tailWord_4948263 prefixEnd_4948263 846945774619626210651953 := by
  unfold tailWord_4948263
  simp only [CollatzResearch.WordTrace]
  refine ⟨180477978472295721883977443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120318652314863814589318295 180477978472295721883977443)
  ·
    refine ⟨270716967708443582825966165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 180477978472295721883977443 270716967708443582825966165)
    ·
      refine ⟨3172464465333323236241791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 270716967708443582825966165 3172464465333323236241791)
      ·
        refine ⟨4758696697999984854362687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3172464465333323236241791 4758696697999984854362687)
        ·
          refine ⟨7138045046999977281544031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4758696697999984854362687 7138045046999977281544031)
          ·
            refine ⟨10707067570499965922316047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7138045046999977281544031 10707067570499965922316047)
            ·
              refine ⟨16060601355749948883474071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10707067570499965922316047 16060601355749948883474071)
              ·
                refine ⟨24090902033624923325211107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16060601355749948883474071 24090902033624923325211107)
                ·
                  refine ⟨36136353050437384987816661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24090902033624923325211107 36136353050437384987816661)
                  ·
                    refine ⟨846945774619626210651953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 36136353050437384987816661 846945774619626210651953)
                    ·
                      rfl

theorem cell23_4948263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 1, 1, 1, 1, 7].length) (baseStart_4948263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4948263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4948263 prefixEnd_4948263 := by exact prefixLift 4948263
  have htrace : WordTrace (prefixWord ++ tailWord_4948263) baseStart_4948263 baseEnd_4948263 := by
    simpa [prefixWord, tailWord_4948263, baseEnd_4948263] using wordTrace_append hprefix tailTrace_4948263
  have hstable : (prefixWord ++ tailWord_4948263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4948263).length < 2 ^ (prefixWord ++ tailWord_4948263).sum := by decide
  have hdescent : baseEnd_4948263 < baseStart_4948263 := by decide
  rcases family_descends (prefixWord ++ tailWord_4948263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4948266 : List Nat := [3, 1, 4, 2, 2, 1, 1, 1, 1, 3, 4]
def baseStart_4948266 : Nat := 118140960795 + 4948266 * 2 ^ 59
def prefixEnd_4948266 : Nat := 4983230072969 + 3 ^ 40 * 4948266 * 2
def baseEnd_4948266 : Nat := 2540838864300842120218345

theorem tailTrace_4948266 : CollatzResearch.WordTrace tailWord_4948266 prefixEnd_4948266 2540838864300842120218345 := by
  unfold tailWord_4948266
  simp only [CollatzResearch.WordTrace]
  refine ⟨45119521972821213349084163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 120318725260856568930891101 45119521972821213349084163)
  ·
    refine ⟨67679282959231820023626245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45119521972821213349084163 67679282959231820023626245)
    ·
      refine ⟨12689865554855966254429921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 67679282959231820023626245 12689865554855966254429921)
      ·
        refine ⟨9517399166141974690822441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12689865554855966254429921 9517399166141974690822441)
        ·
          refine ⟨7138049374606481018116831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9517399166141974690822441 7138049374606481018116831)
          ·
            refine ⟨10707074061909721527175247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7138049374606481018116831 10707074061909721527175247)
            ·
              refine ⟨16060611092864582290762871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10707074061909721527175247 16060611092864582290762871)
              ·
                refine ⟨24090916639296873436144307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16060611092864582290762871 24090916639296873436144307)
                ·
                  refine ⟨36136374958945310154216461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24090916639296873436144307 36136374958945310154216461)
                  ·
                    refine ⟨13551140609604491307831173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 36136374958945310154216461 13551140609604491307831173)
                    ·
                      refine ⟨2540838864300842120218345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13551140609604491307831173 2540838864300842120218345)
                      ·
                        rfl

theorem cell23_4948266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 1, 1, 1, 1, 3, 4].length) (baseStart_4948266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4948266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4948266 prefixEnd_4948266 := by exact prefixLift 4948266
  have htrace : WordTrace (prefixWord ++ tailWord_4948266) baseStart_4948266 baseEnd_4948266 := by
    simpa [prefixWord, tailWord_4948266, baseEnd_4948266] using wordTrace_append hprefix tailTrace_4948266
  have hstable : (prefixWord ++ tailWord_4948266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4948266).length < 2 ^ (prefixWord ++ tailWord_4948266).sum := by decide
  have hdescent : baseEnd_4948266 < baseStart_4948266 := by decide
  rcases family_descends (prefixWord ++ tailWord_4948266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4948302 : List Nat := [4, 1, 1, 1, 1, 1, 2, 1, 2, 9]
def baseStart_4948302 : Nat := 118140960795 + 4948302 * 2 ^ 59
def prefixEnd_4948302 : Nat := 4983230072969 + 3 ^ 40 * 4948302 * 2
def baseEnd_4948302 : Nat := 846952449868134659789393

theorem tailTrace_4948302 : CollatzResearch.WordTrace tailWord_4948302 prefixEnd_4948302 846952449868134659789393 := by
  unfold tailWord_4948302
  simp only [CollatzResearch.WordTrace]
  refine ⟨22559925114894303943080895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 120319600612769621029764773 22559925114894303943080895)
  ·
    refine ⟨33839887672341455914621343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22559925114894303943080895 33839887672341455914621343)
    ·
      refine ⟨50759831508512183871932015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33839887672341455914621343 50759831508512183871932015)
      ·
        refine ⟨76139747262768275807898023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50759831508512183871932015 76139747262768275807898023)
        ·
          refine ⟨114209620894152413711847035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76139747262768275807898023 114209620894152413711847035)
          ·
            refine ⟨171314431341228620567770553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 114209620894152413711847035 171314431341228620567770553)
            ·
              refine ⟨128485823505921465425827915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 171314431341228620567770553 128485823505921465425827915)
              ·
                refine ⟨192728735258882198138741873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 128485823505921465425827915 192728735258882198138741873)
                ·
                  refine ⟨144546551444161648604056405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 192728735258882198138741873 144546551444161648604056405)
                  ·
                    refine ⟨846952449868134659789393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 144546551444161648604056405 846952449868134659789393)
                    ·
                      rfl

theorem cell23_4948302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 1, 2, 9].length) (baseStart_4948302 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4948302 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4948302 prefixEnd_4948302 := by exact prefixLift 4948302
  have htrace : WordTrace (prefixWord ++ tailWord_4948302) baseStart_4948302 baseEnd_4948302 := by
    simpa [prefixWord, tailWord_4948302, baseEnd_4948302] using wordTrace_append hprefix tailTrace_4948302
  have hstable : (prefixWord ++ tailWord_4948302).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4948302).length < 2 ^ (prefixWord ++ tailWord_4948302).sum := by decide
  have hdescent : baseEnd_4948302 < baseStart_4948302 := by decide
  rcases family_descends (prefixWord ++ tailWord_4948302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4948319 : List Nat := [1, 1, 2, 3, 1, 2, 3, 4, 1, 5]
def baseStart_4948319 : Nat := 118140960795 + 4948319 * 2 ^ 59
def prefixEnd_4948319 : Nat := 4983230072969 + 3 ^ 40 * 4948319 * 2
def baseEnd_4948319 : Nat := 846955359591843470951867

theorem tailTrace_4948319 : CollatzResearch.WordTrace tailWord_4948319 prefixEnd_4948319 846955359591843470951867 := by
  unfold tailWord_4948319
  simp only [CollatzResearch.WordTrace]
  refine ⟨180480020960092843448016011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120320013973395228965344007 180480020960092843448016011)
  ·
    refine ⟨270720031440139265172024017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 180480020960092843448016011 270720031440139265172024017)
    ·
      refine ⟨203040023580104448879018013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 270720031440139265172024017 203040023580104448879018013)
      ·
        refine ⟨76140008842539168329631755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 203040023580104448879018013 76140008842539168329631755)
        ·
          refine ⟨114210013263808752494447633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76140008842539168329631755 114210013263808752494447633)
          ·
            refine ⟨85657509947856564370835725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 114210013263808752494447633 85657509947856564370835725)
            ·
              refine ⟨32121566230446211639063397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 85657509947856564370835725 32121566230446211639063397)
              ·
                refine ⟨6022793668208664682324387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 32121566230446211639063397 6022793668208664682324387)
                ·
                  refine ⟨9034190502312997023486581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6022793668208664682324387 9034190502312997023486581)
                  ·
                    refine ⟨846955359591843470951867, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9034190502312997023486581 846955359591843470951867)
                    ·
                      rfl

theorem cell23_4948319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 3, 4, 1, 5].length) (baseStart_4948319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4948319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4948319 prefixEnd_4948319 := by exact prefixLift 4948319
  have htrace : WordTrace (prefixWord ++ tailWord_4948319) baseStart_4948319 baseEnd_4948319 := by
    simpa [prefixWord, tailWord_4948319, baseEnd_4948319] using wordTrace_append hprefix tailTrace_4948319
  have hstable : (prefixWord ++ tailWord_4948319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4948319).length < 2 ^ (prefixWord ++ tailWord_4948319).sum := by decide
  have hdescent : baseEnd_4948319 < baseStart_4948319 := by decide
  rcases family_descends (prefixWord ++ tailWord_4948319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4948339 : List Nat := [1, 1, 1, 2, 2, 1, 2, 2, 1, 8, 2]
def baseStart_4948339 : Nat := 118140960795 + 4948339 * 2 ^ 59
def prefixEnd_4948339 : Nat := 4983230072969 + 3 ^ 40 * 4948339 * 2
def baseEnd_4948339 : Nat := 2540876348388620334605509

theorem tailTrace_4948339 : CollatzResearch.WordTrace tailWord_4948339 prefixEnd_4948339 2540876348388620334605509 := by
  unfold tailWord_4948339
  simp only [CollatzResearch.WordTrace]
  refine ⟨180480750420020386863744071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120320500280013591242496047 180480750420020386863744071)
  ·
    refine ⟨270721125630030580295616107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 180480750420020386863744071 270721125630030580295616107)
    ·
      refine ⟨406081688445045870443424161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 270721125630030580295616107 406081688445045870443424161)
      ·
        refine ⟨304561266333784402832568121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 406081688445045870443424161 304561266333784402832568121)
        ·
          refine ⟨228420949750338302124426091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 304561266333784402832568121 228420949750338302124426091)
          ·
            refine ⟨342631424625507453186639137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 228420949750338302124426091 342631424625507453186639137)
            ·
              refine ⟨256973568469130589889979353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 342631424625507453186639137 256973568469130589889979353)
              ·
                refine ⟨192730176351847942417484515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 256973568469130589889979353 192730176351847942417484515)
                ·
                  refine ⟨289095264527771913626226773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 192730176351847942417484515 289095264527771913626226773)
                  ·
                    refine ⟨3387835131184827112807345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 289095264527771913626226773 3387835131184827112807345)
                    ·
                      refine ⟨2540876348388620334605509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3387835131184827112807345 2540876348388620334605509)
                      ·
                        rfl

theorem cell23_4948339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 2, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 2, 1, 8, 2].length) (baseStart_4948339 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4948339 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4948339 prefixEnd_4948339 := by exact prefixLift 4948339
  have htrace : WordTrace (prefixWord ++ tailWord_4948339) baseStart_4948339 baseEnd_4948339 := by
    simpa [prefixWord, tailWord_4948339, baseEnd_4948339] using wordTrace_append hprefix tailTrace_4948339
  have hstable : (prefixWord ++ tailWord_4948339).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4948339).length < 2 ^ (prefixWord ++ tailWord_4948339).sum := by decide
  have hdescent : baseEnd_4948339 < baseStart_4948339 := by decide
  rcases family_descends (prefixWord ++ tailWord_4948339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4948359 : List Nat := [1, 1, 4, 2, 2, 1, 1, 4, 1, 1, 5]
def baseStart_4948359 : Nat := 118140960795 + 4948359 * 2 ^ 59
def prefixEnd_4948359 : Nat := 4983230072969 + 3 ^ 40 * 4948359 * 2
def baseEnd_4948359 : Nat := 2540886618001710256355417

theorem tailTrace_4948359 : CollatzResearch.WordTrace tailWord_4948359 prefixEnd_4948359 2540886618001710256355417 := by
  unfold tailWord_4948359
  simp only [CollatzResearch.WordTrace]
  refine ⟨180481479879947930279472131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120320986586631953519648087 180481479879947930279472131)
  ·
    refine ⟨270722219819921895419208197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 180481479879947930279472131 270722219819921895419208197)
    ·
      refine ⟨50760416216235355391101537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 270722219819921895419208197 50760416216235355391101537)
      ·
        refine ⟨38070312162176516543326153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50760416216235355391101537 38070312162176516543326153)
        ·
          refine ⟨28552734121632387407494615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38070312162176516543326153 28552734121632387407494615)
          ·
            refine ⟨42829101182448581111241923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28552734121632387407494615 42829101182448581111241923)
            ·
              refine ⟨64243651773672871666862885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42829101182448581111241923 64243651773672871666862885)
              ·
                refine ⟨12045684707563663437536791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 64243651773672871666862885 12045684707563663437536791)
                ·
                  refine ⟨18068527061345495156305187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12045684707563663437536791 18068527061345495156305187)
                  ·
                    refine ⟨27102790592018242734457781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18068527061345495156305187 27102790592018242734457781)
                    ·
                      refine ⟨2540886618001710256355417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27102790592018242734457781 2540886618001710256355417)
                      ·
                        rfl

theorem cell23_4948359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 1, 4, 1, 1, 5].length) (baseStart_4948359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4948359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4948359 prefixEnd_4948359 := by exact prefixLift 4948359
  have htrace : WordTrace (prefixWord ++ tailWord_4948359) baseStart_4948359 baseEnd_4948359 := by
    simpa [prefixWord, tailWord_4948359, baseEnd_4948359] using wordTrace_append hprefix tailTrace_4948359
  have hstable : (prefixWord ++ tailWord_4948359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4948359).length < 2 ^ (prefixWord ++ tailWord_4948359).sum := by decide
  have hdescent : baseEnd_4948359 < baseStart_4948359 := by decide
  rcases family_descends (prefixWord ++ tailWord_4948359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4948386 : List Nat := [3, 3, 1, 2, 1, 1, 3, 2, 1, 2, 4]
def baseStart_4948386 : Nat := 118140960795 + 4948386 * 2 ^ 59
def prefixEnd_4948386 : Nat := 4983230072969 + 3 ^ 40 * 4948386 * 2
def baseEnd_4948386 : Nat := 2540900481979381650717793

theorem tailTrace_4948386 : CollatzResearch.WordTrace tailWord_4948386 prefixEnd_4948386 2540900481979381650717793 := by
  unfold tailWord_4948386
  simp only [CollatzResearch.WordTrace]
  refine ⟨45120616162712528472676253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 120321643100566742593803341 45120616162712528472676253)
  ·
    refine ⟨16920231061017198177253595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45120616162712528472676253 16920231061017198177253595)
    ·
      refine ⟨25380346591525797265880393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16920231061017198177253595 25380346591525797265880393)
      ·
        refine ⟨19035259943644347949410295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25380346591525797265880393 19035259943644347949410295)
        ·
          refine ⟨28552889915466521924115443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19035259943644347949410295 28552889915466521924115443)
          ·
            refine ⟨42829334873199782886173165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28552889915466521924115443 42829334873199782886173165)
            ·
              refine ⟨16061000577449918582314937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 42829334873199782886173165 16061000577449918582314937)
              ·
                refine ⟨12045750433087438936736203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16061000577449918582314937 12045750433087438936736203)
                ·
                  refine ⟨18068625649631158405104305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12045750433087438936736203 18068625649631158405104305)
                  ·
                    refine ⟨13551469237223368803828229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18068625649631158405104305 13551469237223368803828229)
                    ·
                      refine ⟨2540900481979381650717793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13551469237223368803828229 2540900481979381650717793)
                      ·
                        rfl

theorem cell23_4948386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 3, 2, 1, 2, 4].length) (baseStart_4948386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4948386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4948386 prefixEnd_4948386 := by exact prefixLift 4948386
  have htrace : WordTrace (prefixWord ++ tailWord_4948386) baseStart_4948386 baseEnd_4948386 := by
    simpa [prefixWord, tailWord_4948386, baseEnd_4948386] using wordTrace_append hprefix tailTrace_4948386
  have hstable : (prefixWord ++ tailWord_4948386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4948386).length < 2 ^ (prefixWord ++ tailWord_4948386).sum := by decide
  have hdescent : baseEnd_4948386 < baseStart_4948386 := by decide
  rcases family_descends (prefixWord ++ tailWord_4948386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4948407 : List Nat := [1, 1, 3, 1, 3, 3, 4, 2, 1, 2, 2]
def baseStart_4948407 : Nat := 118140960795 + 4948407 * 2 ^ 59
def prefixEnd_4948407 : Nat := 4983230072969 + 3 ^ 40 * 4948407 * 2
def baseEnd_4948407 : Nat := 2540911265073126068555197

theorem tailTrace_4948407 : CollatzResearch.WordTrace tailWord_4948407 prefixEnd_4948407 2540911265073126068555197 := by
  unfold tailWord_4948407
  simp only [CollatzResearch.WordTrace]
  refine ⟨180483230583774034477219475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120322153722516022984812983 180483230583774034477219475)
  ·
    refine ⟨270724845875661051715829213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 180483230583774034477219475 270724845875661051715829213)
    ·
      refine ⟨101521817203372894393435955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 270724845875661051715829213 101521817203372894393435955)
      ·
        refine ⟨152282725805059341590153933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101521817203372894393435955 152282725805059341590153933)
        ·
          refine ⟨57106022176897253096307725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 152282725805059341590153933 57106022176897253096307725)
          ·
            refine ⟨21414758316336469911115397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 57106022176897253096307725 21414758316336469911115397)
            ·
              refine ⟨4015267184313088108334137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21414758316336469911115397 4015267184313088108334137)
              ·
                refine ⟨3011450388234816081250603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4015267184313088108334137 3011450388234816081250603)
                ·
                  refine ⟨4517175582352224121875905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3011450388234816081250603 4517175582352224121875905)
                  ·
                    refine ⟨3387881686764168091406929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4517175582352224121875905 3387881686764168091406929)
                    ·
                      refine ⟨2540911265073126068555197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3387881686764168091406929 2540911265073126068555197)
                      ·
                        rfl

theorem cell23_4948407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 4, 2, 1, 2, 2].length) (baseStart_4948407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4948407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4948407 prefixEnd_4948407 := by exact prefixLift 4948407
  have htrace : WordTrace (prefixWord ++ tailWord_4948407) baseStart_4948407 baseEnd_4948407 := by
    simpa [prefixWord, tailWord_4948407, baseEnd_4948407] using wordTrace_append hprefix tailTrace_4948407
  have hstable : (prefixWord ++ tailWord_4948407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4948407).length < 2 ^ (prefixWord ++ tailWord_4948407).sum := by decide
  have hdescent : baseEnd_4948407 < baseStart_4948407 := by decide
  rcases family_descends (prefixWord ++ tailWord_4948407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4948409 : List Nat := [1, 2, 1, 4, 3, 1, 1, 1, 2, 7]
def baseStart_4948409 : Nat := 118140960795 + 4948409 * 2 ^ 59
def prefixEnd_4948409 : Nat := 4983230072969 + 3 ^ 40 * 4948409 * 2
def baseEnd_4948409 : Nat := 846970764011478353576729

theorem tailTrace_4948409 : CollatzResearch.WordTrace tailWord_4948409 prefixEnd_4948409 846970764011478353576729 := by
  unfold tailWord_4948409
  simp only [CollatzResearch.WordTrace]
  refine ⟨180483303529766788818792281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120322202353177859212528187 180483303529766788818792281)
  ·
    refine ⟨135362477647325091614094211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 180483303529766788818792281 135362477647325091614094211)
    ·
      refine ⟨203043716470987637421141317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 135362477647325091614094211 203043716470987637421141317)
      ·
        refine ⟨38070696838310182016463997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 203043716470987637421141317 38070696838310182016463997)
        ·
          refine ⟨14276511314366318256173999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38070696838310182016463997 14276511314366318256173999)
          ·
            refine ⟨21414766971549477384260999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14276511314366318256173999 21414766971549477384260999)
            ·
              refine ⟨32122150457324216076391499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21414766971549477384260999 32122150457324216076391499)
              ·
                refine ⟨48183225685986324114587249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32122150457324216076391499 48183225685986324114587249)
                ·
                  refine ⟨36137419264489743085940437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 48183225685986324114587249 36137419264489743085940437)
                  ·
                    refine ⟨846970764011478353576729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 36137419264489743085940437 846970764011478353576729)
                    ·
                      rfl

theorem cell23_4948409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 1, 1, 2, 7].length) (baseStart_4948409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4948409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4948409 prefixEnd_4948409 := by exact prefixLift 4948409
  have htrace : WordTrace (prefixWord ++ tailWord_4948409) baseStart_4948409 baseEnd_4948409 := by
    simpa [prefixWord, tailWord_4948409, baseEnd_4948409] using wordTrace_append hprefix tailTrace_4948409
  have hstable : (prefixWord ++ tailWord_4948409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4948409).length < 2 ^ (prefixWord ++ tailWord_4948409).sum := by decide
  have hdescent : baseEnd_4948409 < baseStart_4948409 := by decide
  rcases family_descends (prefixWord ++ tailWord_4948409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4948423 : List Nat := [1, 1, 4, 1, 1, 4, 2, 3, 2, 1, 3]
def baseStart_4948423 : Nat := 118140960795 + 4948423 * 2 ^ 59
def prefixEnd_4948423 : Nat := 4983230072969 + 3 ^ 40 * 4948423 * 2
def baseEnd_4948423 : Nat := 2540919480763598005955123

theorem tailTrace_4948423 : CollatzResearch.WordTrace tailWord_4948423 prefixEnd_4948423 2540919480763598005955123 := by
  unfold tailWord_4948423
  simp only [CollatzResearch.WordTrace]
  refine ⟨180483814151716069209801923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120322542767810712806534615 180483814151716069209801923)
  ·
    refine ⟨270725721227574103814702885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 180483814151716069209801923 270725721227574103814702885)
    ·
      refine ⟨50761072730170144465256791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 270725721227574103814702885 50761072730170144465256791)
      ·
        refine ⟨76141609095255216697885187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50761072730170144465256791 76141609095255216697885187)
        ·
          refine ⟨114212413642882825046827781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76141609095255216697885187 114212413642882825046827781)
          ·
            refine ⟨21414827558040529696280209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 114212413642882825046827781 21414827558040529696280209)
            ·
              refine ⟨16061120668530397272210157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21414827558040529696280209 16061120668530397272210157)
              ·
                refine ⟨6022920250698898977078809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16061120668530397272210157 6022920250698898977078809)
                ·
                  refine ⟨4517190188024174232809107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6022920250698898977078809 4517190188024174232809107)
                  ·
                    refine ⟨6775785282036261349213661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4517190188024174232809107 6775785282036261349213661)
                    ·
                      refine ⟨2540919480763598005955123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6775785282036261349213661 2540919480763598005955123)
                      ·
                        rfl

theorem cell23_4948423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 2, 3, 2, 1, 3].length) (baseStart_4948423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4948423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4948423 prefixEnd_4948423 := by exact prefixLift 4948423
  have htrace : WordTrace (prefixWord ++ tailWord_4948423) baseStart_4948423 baseEnd_4948423 := by
    simpa [prefixWord, tailWord_4948423, baseEnd_4948423] using wordTrace_append hprefix tailTrace_4948423
  have hstable : (prefixWord ++ tailWord_4948423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4948423).length < 2 ^ (prefixWord ++ tailWord_4948423).sum := by decide
  have hdescent : baseEnd_4948423 < baseStart_4948423 := by decide
  rcases family_descends (prefixWord ++ tailWord_4948423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4948449 : List Nat := [1, 2, 3, 1, 2, 2, 2, 1, 1, 3, 5]
def baseStart_4948449 : Nat := 118140960795 + 4948449 * 2 ^ 59
def prefixEnd_4948449 : Nat := 4983230072969 + 3 ^ 40 * 4948449 * 2
def baseEnd_4948449 : Nat := 2540932831260614904230003

theorem tailTrace_4948449 : CollatzResearch.WordTrace tailWord_4948449 prefixEnd_4948449 2540932831260614904230003 := by
  unfold tailWord_4948449
  simp only [CollatzResearch.WordTrace]
  refine ⟨180484762449621875650248401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120323174966414583766832267 180484762449621875650248401)
  ·
    refine ⟨135363571837216406737686301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 180484762449621875650248401 135363571837216406737686301)
    ·
      refine ⟨50761339438956152526632363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 135363571837216406737686301 50761339438956152526632363)
      ·
        refine ⟨76142009158434228789948545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50761339438956152526632363 76142009158434228789948545)
        ·
          refine ⟨57106506868825671592461409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 76142009158434228789948545 57106506868825671592461409)
          ·
            refine ⟨42829880151619253694346057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57106506868825671592461409 42829880151619253694346057)
            ·
              refine ⟨32122410113714440270759543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42829880151619253694346057 32122410113714440270759543)
              ·
                refine ⟨48183615170571660406139315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32122410113714440270759543 48183615170571660406139315)
                ·
                  refine ⟨72275422755857490609208973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 48183615170571660406139315 72275422755857490609208973)
                  ·
                    refine ⟨27103283533446558978453365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 72275422755857490609208973 27103283533446558978453365)
                    ·
                      refine ⟨2540932831260614904230003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27103283533446558978453365 2540932831260614904230003)
                      ·
                        rfl

theorem cell23_4948449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 2, 1, 1, 3, 5].length) (baseStart_4948449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4948449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4948449 prefixEnd_4948449 := by exact prefixLift 4948449
  have htrace : WordTrace (prefixWord ++ tailWord_4948449) baseStart_4948449 baseEnd_4948449 := by
    simpa [prefixWord, tailWord_4948449, baseEnd_4948449] using wordTrace_append hprefix tailTrace_4948449
  have hstable : (prefixWord ++ tailWord_4948449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4948449).length < 2 ^ (prefixWord ++ tailWord_4948449).sum := by decide
  have hdescent : baseEnd_4948449 < baseStart_4948449 := by decide
  rcases family_descends (prefixWord ++ tailWord_4948449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4948459 : List Nat := [1, 1, 1, 1, 2, 3, 3, 1, 4, 2, 4]
def baseStart_4948459 : Nat := 118140960795 + 4948459 * 2 ^ 59
def prefixEnd_4948459 : Nat := 4983230072969 + 3 ^ 40 * 4948459 * 2
def baseEnd_4948459 : Nat := 2540937966067159865104957

theorem tailTrace_4948459 : CollatzResearch.WordTrace tailWord_4948459 prefixEnd_4948459 2540937966067159865104957 := by
  unfold tailWord_4948459
  simp only [CollatzResearch.WordTrace]
  refine ⟨180485127179585647358112431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120323418119723764905408287 180485127179585647358112431)
  ·
    refine ⟨270727690769378471037168647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 180485127179585647358112431 270727690769378471037168647)
    ·
      refine ⟨406091536154067706555752971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 270727690769378471037168647 406091536154067706555752971)
      ·
        refine ⟨609137304231101559833629457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 406091536154067706555752971 609137304231101559833629457)
        ·
          refine ⟨456852978173326169875222093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 609137304231101559833629457 456852978173326169875222093)
          ·
            refine ⟨171319866814997313703208285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 456852978173326169875222093 171319866814997313703208285)
            ·
              refine ⟨64244950055623992638703107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 171319866814997313703208285 64244950055623992638703107)
              ·
                refine ⟨96367425083435988958054661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 64244950055623992638703107 96367425083435988958054661)
                ·
                  refine ⟨18068892203144247929635249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 96367425083435988958054661 18068892203144247929635249)
                  ·
                    refine ⟨13551669152358185947226437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18068892203144247929635249 13551669152358185947226437)
                    ·
                      refine ⟨2540937966067159865104957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13551669152358185947226437 2540937966067159865104957)
                      ·
                        rfl

theorem cell23_4948459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 3, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 3, 1, 4, 2, 4].length) (baseStart_4948459 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4948459 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4948459 prefixEnd_4948459 := by exact prefixLift 4948459
  have htrace : WordTrace (prefixWord ++ tailWord_4948459) baseStart_4948459 baseEnd_4948459 := by
    simpa [prefixWord, tailWord_4948459, baseEnd_4948459] using wordTrace_append hprefix tailTrace_4948459
  have hstable : (prefixWord ++ tailWord_4948459).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4948459).length < 2 ^ (prefixWord ++ tailWord_4948459).sum := by decide
  have hdescent : baseEnd_4948459 < baseStart_4948459 := by decide
  rcases family_descends (prefixWord ++ tailWord_4948459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4948499 : List Nat := [1, 1, 1, 2, 1, 5, 1, 3, 1, 7]
def baseStart_4948499 : Nat := 118140960795 + 4948499 * 2 ^ 59
def prefixEnd_4948499 : Nat := 4983230072969 + 3 ^ 40 * 4948499 * 2
def baseEnd_4948499 : Nat := 846986168431113236201591

theorem tailTrace_4948499 : CollatzResearch.WordTrace tailWord_4948499 prefixEnd_4948499 846986168431113236201591 := by
  unfold tailWord_4948499
  simp only [CollatzResearch.WordTrace]
  refine ⟨180486586099440734189568551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120324390732960489459712367 180486586099440734189568551)
  ·
    refine ⟨270729879149161101284352827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 180486586099440734189568551 270729879149161101284352827)
    ·
      refine ⟨406094818723741651926529241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 270729879149161101284352827 406094818723741651926529241)
      ·
        refine ⟨304571114042806238944896931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 406094818723741651926529241 304571114042806238944896931)
        ·
          refine ⟨456856671064209358417345397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 304571114042806238944896931 456856671064209358417345397)
          ·
            refine ⟨42830312912269627351626131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 456856671064209358417345397 42830312912269627351626131)
            ·
              refine ⟨64245469368404441027439197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42830312912269627351626131 64245469368404441027439197)
              ·
                refine ⟨24092051013151665385289699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 64245469368404441027439197 24092051013151665385289699)
                ·
                  refine ⟨36138076519727498077934549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24092051013151665385289699 36138076519727498077934549)
                  ·
                    refine ⟨846986168431113236201591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 36138076519727498077934549 846986168431113236201591)
                    ·
                      rfl

theorem cell23_4948499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 1, 3, 1, 7].length) (baseStart_4948499 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4948499 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4948499 prefixEnd_4948499 := by exact prefixLift 4948499
  have htrace : WordTrace (prefixWord ++ tailWord_4948499) baseStart_4948499 baseEnd_4948499 := by
    simpa [prefixWord, tailWord_4948499, baseEnd_4948499] using wordTrace_append hprefix tailTrace_4948499
  have hstable : (prefixWord ++ tailWord_4948499).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4948499).length < 2 ^ (prefixWord ++ tailWord_4948499).sum := by decide
  have hdescent : baseEnd_4948499 < baseStart_4948499 := by decide
  rcases family_descends (prefixWord ++ tailWord_4948499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4948536 : List Nat := [2, 1, 2, 1, 4, 1, 1, 2, 4, 1, 4]
def baseStart_4948536 : Nat := 118140960795 + 4948536 * 2 ^ 59
def prefixEnd_4948536 : Nat := 4983230072969 + 3 ^ 40 * 4948536 * 2
def baseEnd_4948536 : Nat := 2540977504077556063842103

theorem tailTrace_4948536 : CollatzResearch.WordTrace tailWord_4948536 prefixEnd_4948536 2540977504077556063842103 := by
  unfold tailWord_4948536
  simp only [CollatzResearch.WordTrace]
  refine ⟨90243967800153344754332731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120325290400204459672443641 90243967800153344754332731)
  ·
    refine ⟨135365951700230017131499097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90243967800153344754332731 135365951700230017131499097)
    ·
      refine ⟨101524463775172512848624323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 135365951700230017131499097 101524463775172512848624323)
      ·
        refine ⟨152286695662758769272936485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101524463775172512848624323 152286695662758769272936485)
        ·
          refine ⟨28553755436767269238675591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 152286695662758769272936485 28553755436767269238675591)
          ·
            refine ⟨42830633155150903858013387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28553755436767269238675591 42830633155150903858013387)
            ·
              refine ⟨64245949732726355787020081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42830633155150903858013387 64245949732726355787020081)
              ·
                refine ⟨48184462299544766840265061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 64245949732726355787020081 48184462299544766840265061)
                ·
                  refine ⟨9034586681164643782549699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 48184462299544766840265061 9034586681164643782549699)
                  ·
                    refine ⟨13551880021746965673824549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9034586681164643782549699 13551880021746965673824549)
                    ·
                      refine ⟨2540977504077556063842103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13551880021746965673824549 2540977504077556063842103)
                      ·
                        rfl

theorem cell23_4948536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 1, 2, 4, 1, 4].length) (baseStart_4948536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4948536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4948536 prefixEnd_4948536 := by exact prefixLift 4948536
  have htrace : WordTrace (prefixWord ++ tailWord_4948536) baseStart_4948536 baseEnd_4948536 := by
    simpa [prefixWord, tailWord_4948536, baseEnd_4948536] using wordTrace_append hprefix tailTrace_4948536
  have hstable : (prefixWord ++ tailWord_4948536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4948536).length < 2 ^ (prefixWord ++ tailWord_4948536).sum := by decide
  have hdescent : baseEnd_4948536 < baseStart_4948536 := by decide
  rcases family_descends (prefixWord ++ tailWord_4948536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4948550 : List Nat := [6, 1, 1, 1, 2, 1, 1, 3, 2, 5]
def baseStart_4948550 : Nat := 118140960795 + 4948550 * 2 ^ 59
def prefixEnd_4948550 : Nat := 4983230072969 + 3 ^ 40 * 4948550 * 2
def baseEnd_4948550 : Nat := 846994897602239669689013

theorem tailTrace_4948550 : CollatzResearch.WordTrace tailWord_4948550 prefixEnd_4948550 846994897602239669689013 := by
  unfold tailWord_4948550
  simp only [CollatzResearch.WordTrace]
  refine ⟨5640263944445499059364847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 120325630814837313266450069 5640263944445499059364847)
  ·
    refine ⟨8460395916668248589047271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5640263944445499059364847 8460395916668248589047271)
    ·
      refine ⟨12690593875002372883570907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8460395916668248589047271 12690593875002372883570907)
      ·
        refine ⟨19035890812503559325356361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12690593875002372883570907 19035890812503559325356361)
        ·
          refine ⟨14276918109377669494017271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19035890812503559325356361 14276918109377669494017271)
          ·
            refine ⟨21415377164066504241025907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14276918109377669494017271 21415377164066504241025907)
            ·
              refine ⟨32123065746099756361538861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21415377164066504241025907 32123065746099756361538861)
              ·
                refine ⟨12046149654787408635577073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32123065746099756361538861 12046149654787408635577073)
                ·
                  refine ⟨9034612241090556476682805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12046149654787408635577073 9034612241090556476682805)
                  ·
                    refine ⟨846994897602239669689013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9034612241090556476682805 846994897602239669689013)
                    ·
                      rfl

theorem cell23_4948550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 1, 3, 2, 5].length) (baseStart_4948550 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4948550 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4948550 prefixEnd_4948550 := by exact prefixLift 4948550
  have htrace : WordTrace (prefixWord ++ tailWord_4948550) baseStart_4948550 baseEnd_4948550 := by
    simpa [prefixWord, tailWord_4948550, baseEnd_4948550] using wordTrace_append hprefix tailTrace_4948550
  have hstable : (prefixWord ++ tailWord_4948550).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4948550).length < 2 ^ (prefixWord ++ tailWord_4948550).sum := by decide
  have hdescent : baseEnd_4948550 < baseStart_4948550 := by decide
  rcases family_descends (prefixWord ++ tailWord_4948550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4948559 : List Nat := [1, 1, 2, 1, 1, 2, 4, 1, 10]
def baseStart_4948559 : Nat := 118140960795 + 4948559 * 2 ^ 59
def prefixEnd_4948559 : Nat := 4983230072969 + 3 ^ 40 * 4948559 * 2
def baseEnd_4948559 : Nat := 282332146014734385983833

theorem tailTrace_4948559 : CollatzResearch.WordTrace tailWord_4948559 prefixEnd_4948559 282332146014734385983833 := by
  unfold tailWord_4948559
  simp only [CollatzResearch.WordTrace]
  refine ⟨180488774479223364436752731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120325849652815576291168487 180488774479223364436752731)
  ·
    refine ⟨270733161718835046655129097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 180488774479223364436752731 270733161718835046655129097)
    ·
      refine ⟨203049871289126284991346823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 270733161718835046655129097 203049871289126284991346823)
      ·
        refine ⟨304574806933689427487020235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 203049871289126284991346823 304574806933689427487020235)
        ·
          refine ⟨456862210400534141230530353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 304574806933689427487020235 456862210400534141230530353)
          ·
            refine ⟨342646657800400605922897765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 456862210400534141230530353 342646657800400605922897765)
            ·
              refine ⟨64246248337575113610543331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 342646657800400605922897765 64246248337575113610543331)
              ·
                refine ⟨96369372506362670415814997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 64246248337575113610543331 96369372506362670415814997)
                ·
                  refine ⟨282332146014734385983833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 96369372506362670415814997 282332146014734385983833)
                  ·
                    rfl

theorem cell23_4948559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 4, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 4, 1, 10].length) (baseStart_4948559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4948559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4948559 prefixEnd_4948559 := by exact prefixLift 4948559
  have htrace : WordTrace (prefixWord ++ tailWord_4948559) baseStart_4948559 baseEnd_4948559 := by
    simpa [prefixWord, tailWord_4948559, baseEnd_4948559] using wordTrace_append hprefix tailTrace_4948559
  have hstable : (prefixWord ++ tailWord_4948559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4948559).length < 2 ^ (prefixWord ++ tailWord_4948559).sum := by decide
  have hdescent : baseEnd_4948559 < baseStart_4948559 := by decide
  rcases family_descends (prefixWord ++ tailWord_4948559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4948576 : List Nat := [2, 1, 1, 3, 2, 1, 3, 4, 6]
def baseStart_4948576 : Nat := 118140960795 + 4948576 * 2 ^ 59
def prefixEnd_4948576 : Nat := 4983230072969 + 3 ^ 40 * 4948576 * 2
def baseEnd_4948576 : Nat := 282333115922637323037991

theorem tailTrace_4948576 : CollatzResearch.WordTrace tailWord_4948576 prefixEnd_4948576 282333115922637323037991 := by
  unfold tailWord_4948576
  simp only [CollatzResearch.WordTrace]
  refine ⟨90244697260080888170060791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120326263013441184226747721 90244697260080888170060791)
  ·
    refine ⟨135367045890121332255091187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90244697260080888170060791 135367045890121332255091187)
    ·
      refine ⟨203050568835181998382636781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 135367045890121332255091187 203050568835181998382636781)
      ·
        refine ⟨76143963313193249393488793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 203050568835181998382636781 76143963313193249393488793)
        ·
          refine ⟨57107972484894937045116595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 76143963313193249393488793 57107972484894937045116595)
          ·
            refine ⟨85661958727342405567674893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57107972484894937045116595 85661958727342405567674893)
            ·
              refine ⟨32123234522753402087878085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 85661958727342405567674893 32123234522753402087878085)
              ·
                refine ⟨6023106473016262891477141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 32123234522753402087878085 6023106473016262891477141)
                ·
                  refine ⟨282333115922637323037991, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6023106473016262891477141 282333115922637323037991)
                  ·
                    rfl

theorem cell23_4948576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 3, 4, 6].length) (baseStart_4948576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4948576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4948576 prefixEnd_4948576 := by exact prefixLift 4948576
  have htrace : WordTrace (prefixWord ++ tailWord_4948576) baseStart_4948576 baseEnd_4948576 := by
    simpa [prefixWord, tailWord_4948576, baseEnd_4948576] using wordTrace_append hprefix tailTrace_4948576
  have hstable : (prefixWord ++ tailWord_4948576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4948576).length < 2 ^ (prefixWord ++ tailWord_4948576).sum := by decide
  have hdescent : baseEnd_4948576 < baseStart_4948576 := by decide
  rcases family_descends (prefixWord ++ tailWord_4948576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4948580 : List Nat := [2, 3, 1, 1, 2, 2, 3, 4, 1, 4]
def baseStart_4948580 : Nat := 118140960795 + 4948580 * 2 ^ 59
def prefixEnd_4948580 : Nat := 4983230072969 + 3 ^ 40 * 4948580 * 2
def baseEnd_4948580 : Nat := 847000032408784630563967

theorem tailTrace_4948580 : CollatzResearch.WordTrace tailWord_4948580 prefixEnd_4948580 847000032408784630563967 := by
  unfold tailWord_4948580
  simp only [CollatzResearch.WordTrace]
  refine ⟨90244770206073642511633597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120326360274764856682178129 90244770206073642511633597)
  ·
    refine ⟨33841788827277615941862599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 90244770206073642511633597 33841788827277615941862599)
    ·
      refine ⟨50762683240916423912793899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33841788827277615941862599 50762683240916423912793899)
      ·
        refine ⟨76144024861374635869190849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50762683240916423912793899 76144024861374635869190849)
        ·
          refine ⟨57108018646030976901893137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 76144024861374635869190849 57108018646030976901893137)
          ·
            refine ⟨42831013984523232676419853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57108018646030976901893137 42831013984523232676419853)
            ·
              refine ⟨16061630244196212253657445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 42831013984523232676419853 16061630244196212253657445)
              ·
                refine ⟨3011555670786789797560771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16061630244196212253657445 3011555670786789797560771)
                ·
                  refine ⟨4517333506180184696341157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3011555670786789797560771 4517333506180184696341157)
                  ·
                    refine ⟨847000032408784630563967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4517333506180184696341157 847000032408784630563967)
                    ·
                      rfl

theorem cell23_4948580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 3, 4, 1, 4].length) (baseStart_4948580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4948580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4948580 prefixEnd_4948580 := by exact prefixLift 4948580
  have htrace : WordTrace (prefixWord ++ tailWord_4948580) baseStart_4948580 baseEnd_4948580 := by
    simpa [prefixWord, tailWord_4948580, baseEnd_4948580] using wordTrace_append hprefix tailTrace_4948580
  have hstable : (prefixWord ++ tailWord_4948580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4948580).length < 2 ^ (prefixWord ++ tailWord_4948580).sum := by decide
  have hdescent : baseEnd_4948580 < baseStart_4948580 := by decide
  rcases family_descends (prefixWord ++ tailWord_4948580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4948637 : List Nat := [1, 4, 2, 1, 1, 1, 4, 4, 1, 1, 3]
def baseStart_4948637 : Nat := 118140960795 + 4948637 * 2 ^ 59
def prefixEnd_4948637 : Nat := 4983230072969 + 3 ^ 40 * 4948637 * 2
def baseEnd_4948637 : Nat := 2541029365623660168679139

theorem tailTrace_4948637 : CollatzResearch.WordTrace tailWord_4948637 prefixEnd_4948637 2541029365623660168679139 := by
  unfold tailWord_4948637
  simp only [CollatzResearch.WordTrace]
  refine ⟨180491619372940783758092165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120327746248627189172061443 180491619372940783758092165)
  ·
    refine ⟨33842178632426396954642281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 180491619372940783758092165 33842178632426396954642281)
    ·
      refine ⟨25381633974319797715981711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33842178632426396954642281 25381633974319797715981711)
      ·
        refine ⟨38072450961479696573972567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25381633974319797715981711 38072450961479696573972567)
        ·
          refine ⟨57108676442219544860958851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38072450961479696573972567 57108676442219544860958851)
          ·
            refine ⟨85663014663329317291438277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57108676442219544860958851 85663014663329317291438277)
            ·
              refine ⟨16061815249374246992144677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 85663014663329317291438277 16061815249374246992144677)
              ·
                refine ⟨3011590359257671311027127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16061815249374246992144677 3011590359257671311027127)
                ·
                  refine ⟨4517385538886506966540691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3011590359257671311027127 4517385538886506966540691)
                  ·
                    refine ⟨6776078308329760449811037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4517385538886506966540691 6776078308329760449811037)
                    ·
                      refine ⟨2541029365623660168679139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6776078308329760449811037 2541029365623660168679139)
                      ·
                        rfl

theorem cell23_4948637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 4, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 4, 4, 1, 1, 3].length) (baseStart_4948637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4948637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4948637 prefixEnd_4948637 := by exact prefixLift 4948637
  have htrace : WordTrace (prefixWord ++ tailWord_4948637) baseStart_4948637 baseEnd_4948637 := by
    simpa [prefixWord, tailWord_4948637, baseEnd_4948637] using wordTrace_append hprefix tailTrace_4948637
  have hstable : (prefixWord ++ tailWord_4948637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4948637).length < 2 ^ (prefixWord ++ tailWord_4948637).sum := by decide
  have hdescent : baseEnd_4948637 < baseStart_4948637 := by decide
  rcases family_descends (prefixWord ++ tailWord_4948637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4948657 : List Nat := [1, 2, 2, 6, 1, 1, 2, 2, 1, 5]
def baseStart_4948657 : Nat := 118140960795 + 4948657 * 2 ^ 59
def prefixEnd_4948657 : Nat := 4983230072969 + 3 ^ 40 * 4948657 * 2
def baseEnd_4948657 : Nat := 847013211745583363476349

theorem tailTrace_4948657 : CollatzResearch.WordTrace tailWord_4948657 prefixEnd_4948657 847013211745583363476349 := by
  unfold tailWord_4948657
  simp only [CollatzResearch.WordTrace]
  refine ⟨180492348832868327173820225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120328232555245551449213483 180492348832868327173820225)
  ·
    refine ⟨135369261624651245380365169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 180492348832868327173820225 135369261624651245380365169)
    ·
      refine ⟨101526946218488434035273877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 135369261624651245380365169 101526946218488434035273877)
      ·
        refine ⟨4759075603991645345403463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 101526946218488434035273877 4759075603991645345403463)
        ·
          refine ⟨7138613405987468018105195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4759075603991645345403463 7138613405987468018105195)
          ·
            refine ⟨10707920108981202027157793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7138613405987468018105195 10707920108981202027157793)
            ·
              refine ⟨8030940081735901520368345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10707920108981202027157793 8030940081735901520368345)
              ·
                refine ⟨6023205061301926140276259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8030940081735901520368345 6023205061301926140276259)
                ·
                  refine ⟨9034807591952889210414389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6023205061301926140276259 9034807591952889210414389)
                  ·
                    refine ⟨847013211745583363476349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9034807591952889210414389 847013211745583363476349)
                    ·
                      rfl

theorem cell23_4948657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 1, 2, 2, 1, 5].length) (baseStart_4948657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4948657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4948657 prefixEnd_4948657 := by exact prefixLift 4948657
  have htrace : WordTrace (prefixWord ++ tailWord_4948657) baseStart_4948657 baseEnd_4948657 := by
    simpa [prefixWord, tailWord_4948657, baseEnd_4948657] using wordTrace_append hprefix tailTrace_4948657
  have hstable : (prefixWord ++ tailWord_4948657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4948657).length < 2 ^ (prefixWord ++ tailWord_4948657).sum := by decide
  have hdescent : baseEnd_4948657 < baseStart_4948657 := by decide
  rcases family_descends (prefixWord ++ tailWord_4948657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4948666 : List Nat := [3, 1, 1, 1, 2, 3, 3, 9]
def baseStart_4948666 : Nat := 118140960795 + 4948666 * 2 ^ 59
def prefixEnd_4948666 : Nat := 4983230072969 + 3 ^ 40 * 4948666 * 2
def baseEnd_4948666 : Nat := 94112750243060761304315

theorem tailTrace_4948666 : CollatzResearch.WordTrace tailWord_4948666 prefixEnd_4948666 94112750243060761304315 := by
  unfold tailWord_4948666
  simp only [CollatzResearch.WordTrace]
  refine ⟨45123169272458930427724463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 120328451393223814473931901 45123169272458930427724463)
  ·
    refine ⟨67684753908688395641586695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45123169272458930427724463 67684753908688395641586695)
    ·
      refine ⟨101527130863032593462380043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67684753908688395641586695 101527130863032593462380043)
      ·
        refine ⟨152290696294548890193570065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101527130863032593462380043 152290696294548890193570065)
        ·
          refine ⟨114218022220911667645177549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 152290696294548890193570065 114218022220911667645177549)
          ·
            refine ⟨42831758332841875366941581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 114218022220911667645177549 42831758332841875366941581)
            ·
              refine ⟨16061909374815703262603093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 42831758332841875366941581 16061909374815703262603093)
              ·
                refine ⟨94112750243060761304315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 16061909374815703262603093 94112750243060761304315)
                ·
                  rfl

theorem cell23_4948666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 3, 9].length) (baseStart_4948666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4948666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4948666 prefixEnd_4948666 := by exact prefixLift 4948666
  have htrace : WordTrace (prefixWord ++ tailWord_4948666) baseStart_4948666 baseEnd_4948666 := by
    simpa [prefixWord, tailWord_4948666, baseEnd_4948666] using wordTrace_append hprefix tailTrace_4948666
  have hstable : (prefixWord ++ tailWord_4948666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4948666).length < 2 ^ (prefixWord ++ tailWord_4948666).sum := by decide
  have hdescent : baseEnd_4948666 < baseStart_4948666 := by decide
  rcases family_descends (prefixWord ++ tailWord_4948666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4948680 : List Nat := [2, 1, 3, 1, 2, 3, 2, 3, 1, 2, 3]
def baseStart_4948680 : Nat := 118140960795 + 4948680 * 2 ^ 59
def prefixEnd_4948680 : Nat := 4983230072969 + 3 ^ 40 * 4948680 * 2
def baseEnd_4948680 : Nat := 2541051445291803500441441

theorem tailTrace_4948680 : CollatzResearch.WordTrace tailWord_4948680 prefixEnd_4948680 2541051445291803500441441 := by
  unfold tailWord_4948680
  simp only [CollatzResearch.WordTrace]
  refine ⟨90246593855892501050953747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120328791807856668067938329 90246593855892501050953747)
  ·
    refine ⟨135369890783838751576430621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90246593855892501050953747 135369890783838751576430621)
    ·
      refine ⟨50763709043939531841161483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 135369890783838751576430621 50763709043939531841161483)
      ·
        refine ⟨76145563565909297761742225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50763709043939531841161483 76145563565909297761742225)
        ·
          refine ⟨57109172674431973321306669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 76145563565909297761742225 57109172674431973321306669)
          ·
            refine ⟨21415939752911989995490001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 57109172674431973321306669 21415939752911989995490001)
            ·
              refine ⟨16061954814683992496617501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21415939752911989995490001 16061954814683992496617501)
              ·
                refine ⟨6023233055506497186231563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16061954814683992496617501 6023233055506497186231563)
                ·
                  refine ⟨9034849583259745779347345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6023233055506497186231563 9034849583259745779347345)
                  ·
                    refine ⟨6776137187444809334510509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9034849583259745779347345 6776137187444809334510509)
                    ·
                      refine ⟨2541051445291803500441441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6776137187444809334510509 2541051445291803500441441)
                      ·
                        rfl

theorem cell23_4948680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 2, 3, 1, 2, 3].length) (baseStart_4948680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4948680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4948680 prefixEnd_4948680 := by exact prefixLift 4948680
  have htrace : WordTrace (prefixWord ++ tailWord_4948680) baseStart_4948680 baseEnd_4948680 := by
    simpa [prefixWord, tailWord_4948680, baseEnd_4948680] using wordTrace_append hprefix tailTrace_4948680
  have hstable : (prefixWord ++ tailWord_4948680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4948680).length < 2 ^ (prefixWord ++ tailWord_4948680).sum := by decide
  have hdescent : baseEnd_4948680 < baseStart_4948680 := by decide
  rcases family_descends (prefixWord ++ tailWord_4948680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4948700 : List Nat := [2, 2, 5, 1, 1, 2, 2, 8]
def baseStart_4948700 : Nat := 118140960795 + 4948700 * 2 ^ 59
def prefixEnd_4948700 : Nat := 4983230072969 + 3 ^ 40 * 4948700 * 2
def baseEnd_4948700 : Nat := 94113396848329386007087

theorem tailTrace_4948700 : CollatzResearch.WordTrace tailWord_4948700 prefixEnd_4948700 94113396848329386007087 := by
  unfold tailWord_4948700
  simp only [CollatzResearch.WordTrace]
  refine ⟨90246958585856272758817777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120329278114475030345090369 90246958585856272758817777)
  ·
    refine ⟨67685218939392204569113333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90246958585856272758817777 67685218939392204569113333)
    ·
      refine ⟨6345489275568019178354375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 67685218939392204569113333 6345489275568019178354375)
      ·
        refine ⟨9518233913352028767531563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6345489275568019178354375 9518233913352028767531563)
        ·
          refine ⟨14277350870028043151297345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9518233913352028767531563 14277350870028043151297345)
          ·
            refine ⟨10708013152521032363473009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14277350870028043151297345 10708013152521032363473009)
            ·
              refine ⟨8031009864390774272604757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10708013152521032363473009 8031009864390774272604757)
              ·
                refine ⟨94113396848329386007087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8031009864390774272604757 94113396848329386007087)
                ·
                  rfl

theorem cell23_4948700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 2, 2, 8].length) (baseStart_4948700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4948700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4948700 prefixEnd_4948700 := by exact prefixLift 4948700
  have htrace : WordTrace (prefixWord ++ tailWord_4948700) baseStart_4948700 baseEnd_4948700 := by
    simpa [prefixWord, tailWord_4948700, baseEnd_4948700] using wordTrace_append hprefix tailTrace_4948700
  have hstable : (prefixWord ++ tailWord_4948700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4948700).length < 2 ^ (prefixWord ++ tailWord_4948700).sum := by decide
  have hdescent : baseEnd_4948700 < baseStart_4948700 := by decide
  rcases family_descends (prefixWord ++ tailWord_4948700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4948716 : List Nat := [2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 8]
def baseStart_4948716 : Nat := 118140960795 + 4948716 * 2 ^ 59
def prefixEnd_4948716 : Nat := 4983230072969 + 3 ^ 40 * 4948716 * 2
def baseEnd_4948716 : Nat := 2541069930595365359591275

theorem tailTrace_4948716 : CollatzResearch.WordTrace tailWord_4948716 prefixEnd_4948716 2541069930595365359591275 := by
  unfold tailWord_4948716
  simp only [CollatzResearch.WordTrace]
  refine ⟨90247250369827290125109001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120329667159769720166812001 90247250369827290125109001)
  ·
    refine ⟨67685437777370467593831751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90247250369827290125109001 67685437777370467593831751)
    ·
      refine ⟨101528156666055701390747627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67685437777370467593831751 101528156666055701390747627)
      ·
        refine ⟨152292234999083552086121441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101528156666055701390747627 152292234999083552086121441)
        ·
          refine ⟨114219176249312664064591081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 152292234999083552086121441 114219176249312664064591081)
          ·
            refine ⟨85664382186984498048443311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 114219176249312664064591081 85664382186984498048443311)
            ·
              refine ⟨128496573280476747072664967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 85664382186984498048443311 128496573280476747072664967)
              ·
                refine ⟨192744859920715120608997451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 128496573280476747072664967 192744859920715120608997451)
                ·
                  refine ⟨289117289881072680913496177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 192744859920715120608997451 289117289881072680913496177)
                  ·
                    refine ⟨216837967410804510685122133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 289117289881072680913496177 216837967410804510685122133)
                    ·
                      refine ⟨2541069930595365359591275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 216837967410804510685122133 2541069930595365359591275)
                      ·
                        rfl

theorem cell23_4948716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 8].length) (baseStart_4948716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4948716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4948716 prefixEnd_4948716 := by exact prefixLift 4948716
  have htrace : WordTrace (prefixWord ++ tailWord_4948716) baseStart_4948716 baseEnd_4948716 := by
    simpa [prefixWord, tailWord_4948716, baseEnd_4948716] using wordTrace_append hprefix tailTrace_4948716
  have hstable : (prefixWord ++ tailWord_4948716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4948716).length < 2 ^ (prefixWord ++ tailWord_4948716).sum := by decide
  have hdescent : baseEnd_4948716 < baseStart_4948716 := by decide
  rcases family_descends (prefixWord ++ tailWord_4948716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4948720 : List Nat := [2, 1, 1, 1, 3, 1, 5, 1, 3, 3, 2]
def baseStart_4948720 : Nat := 118140960795 + 4948720 * 2 ^ 59
def prefixEnd_4948720 : Nat := 4983230072969 + 3 ^ 40 * 4948720 * 2
def baseEnd_4948720 : Nat := 2541071984517983343941257

theorem tailTrace_4948720 : CollatzResearch.WordTrace tailWord_4948720 prefixEnd_4948720 2541071984517983343941257 := by
  unfold tailWord_4948720
  simp only [CollatzResearch.WordTrace]
  refine ⟨90247323315820044466681807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120329764421093392622242409 90247323315820044466681807)
  ·
    refine ⟨135370984973730066700022711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90247323315820044466681807 135370984973730066700022711)
    ·
      refine ⟨203056477460595100050034067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 135370984973730066700022711 203056477460595100050034067)
      ·
        refine ⟨304584716190892650075051101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 203056477460595100050034067 304584716190892650075051101)
        ·
          refine ⟨114219268571584743778144163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 304584716190892650075051101 114219268571584743778144163)
          ·
            refine ⟨171328902857377115667216245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 114219268571584743778144163 171328902857377115667216245)
            ·
              refine ⟨16062084642879104593801523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 171328902857377115667216245 16062084642879104593801523)
              ·
                refine ⟨24093126964318656890702285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16062084642879104593801523 24093126964318656890702285)
                ·
                  refine ⟨9034922611619496334013357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24093126964318656890702285 9034922611619496334013357)
                  ·
                    refine ⟨3388095979357311125255009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9034922611619496334013357 3388095979357311125255009)
                    ·
                      refine ⟨2541071984517983343941257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3388095979357311125255009 2541071984517983343941257)
                      ·
                        rfl

theorem cell23_4948720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 5, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 5, 1, 3, 3, 2].length) (baseStart_4948720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4948720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4948720 prefixEnd_4948720 := by exact prefixLift 4948720
  have htrace : WordTrace (prefixWord ++ tailWord_4948720) baseStart_4948720 baseEnd_4948720 := by
    simpa [prefixWord, tailWord_4948720, baseEnd_4948720] using wordTrace_append hprefix tailTrace_4948720
  have hstable : (prefixWord ++ tailWord_4948720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4948720).length < 2 ^ (prefixWord ++ tailWord_4948720).sum := by decide
  have hdescent : baseEnd_4948720 < baseStart_4948720 := by decide
  rcases family_descends (prefixWord ++ tailWord_4948720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4948724 : List Nat := [2, 6, 1, 1, 2, 1, 1, 2, 1, 2, 4]
def baseStart_4948724 : Nat := 118140960795 + 4948724 * 2 ^ 59
def prefixEnd_4948724 : Nat := 4983230072969 + 3 ^ 40 * 4948724 * 2
def baseEnd_4948724 : Nat := 2541074038440601328291239

theorem tailTrace_4948724 : CollatzResearch.WordTrace tailWord_4948724 prefixEnd_4948724 2541074038440601328291239 := by
  unfold tailWord_4948724
  simp only [CollatzResearch.WordTrace]
  refine ⟨90247396261812798808254613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120329861682417065077672817 90247396261812798808254613)
  ·
    refine ⟨4230346699772474944136935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 90247396261812798808254613 4230346699772474944136935)
    ·
      refine ⟨6345520049658712416205403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4230346699772474944136935 6345520049658712416205403)
      ·
        refine ⟨9518280074488068624308105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6345520049658712416205403 9518280074488068624308105)
        ·
          refine ⟨7138710055866051468231079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9518280074488068624308105 7138710055866051468231079)
          ·
            refine ⟨10708065083799077202346619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7138710055866051468231079 10708065083799077202346619)
            ·
              refine ⟨16062097625698615803519929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10708065083799077202346619 16062097625698615803519929)
              ·
                refine ⟨12046573219273961852639947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16062097625698615803519929 12046573219273961852639947)
                ·
                  refine ⟨18069859828910942778959921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12046573219273961852639947 18069859828910942778959921)
                  ·
                    refine ⟨13552394871683207084219941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18069859828910942778959921 13552394871683207084219941)
                    ·
                      refine ⟨2541074038440601328291239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13552394871683207084219941 2541074038440601328291239)
                      ·
                        rfl

theorem cell23_4948724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 1, 1, 2, 1, 2, 4].length) (baseStart_4948724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4948724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4948724 prefixEnd_4948724 := by exact prefixLift 4948724
  have htrace : WordTrace (prefixWord ++ tailWord_4948724) baseStart_4948724 baseEnd_4948724 := by
    simpa [prefixWord, tailWord_4948724, baseEnd_4948724] using wordTrace_append hprefix tailTrace_4948724
  have hstable : (prefixWord ++ tailWord_4948724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4948724).length < 2 ^ (prefixWord ++ tailWord_4948724).sum := by decide
  have hdescent : baseEnd_4948724 < baseStart_4948724 := by decide
  rcases family_descends (prefixWord ++ tailWord_4948724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4948750 : List Nat := [4, 1, 1, 2, 1, 1, 1, 1, 5, 4, 2]
def baseStart_4948750 : Nat := 118140960795 + 4948750 * 2 ^ 59
def prefixEnd_4948750 : Nat := 4983230072969 + 3 ^ 40 * 4948750 * 2
def baseEnd_4948750 : Nat := 2541087388937618226566119

theorem tailTrace_4948750 : CollatzResearch.WordTrace tailWord_4948750 prefixEnd_4948750 2541087388937618226566119 := by
  unfold tailWord_4948750
  simp only [CollatzResearch.WordTrace]
  refine ⟨22561967602691425507119463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 120330493881020936037970469 22561967602691425507119463)
  ·
    refine ⟨33842951404037138260679195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22561967602691425507119463 33842951404037138260679195)
    ·
      refine ⟨50764427106055707391018793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33842951404037138260679195 50764427106055707391018793)
      ·
        refine ⟨38073320329541780543264095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50764427106055707391018793 38073320329541780543264095)
        ·
          refine ⟨57109980494312670814896143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38073320329541780543264095 57109980494312670814896143)
          ·
            refine ⟨85664970741469006222344215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57109980494312670814896143 85664970741469006222344215)
            ·
              refine ⟨128497456112203509333516323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 85664970741469006222344215 128497456112203509333516323)
              ·
                refine ⟨192746184168305264000274485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 128497456112203509333516323 192746184168305264000274485)
                ·
                  refine ⟨18069954765778618500025733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 192746184168305264000274485 18069954765778618500025733)
                  ·
                    refine ⟨3388116518583490968754825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18069954765778618500025733 3388116518583490968754825)
                    ·
                      refine ⟨2541087388937618226566119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3388116518583490968754825 2541087388937618226566119)
                      ·
                        rfl

theorem cell23_4948750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 1, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 1, 5, 4, 2].length) (baseStart_4948750 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4948750 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4948750 prefixEnd_4948750 := by exact prefixLift 4948750
  have htrace : WordTrace (prefixWord ++ tailWord_4948750) baseStart_4948750 baseEnd_4948750 := by
    simpa [prefixWord, tailWord_4948750, baseEnd_4948750] using wordTrace_append hprefix tailTrace_4948750
  have hstable : (prefixWord ++ tailWord_4948750).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4948750).length < 2 ^ (prefixWord ++ tailWord_4948750).sum := by decide
  have hdescent : baseEnd_4948750 < baseStart_4948750 := by decide
  rcases family_descends (prefixWord ++ tailWord_4948750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4948753 : List Nat := [1, 2, 2, 1, 1, 3, 3, 1, 2, 4, 3]
def baseStart_4948753 : Nat := 118140960795 + 4948753 * 2 ^ 59
def prefixEnd_4948753 : Nat := 4983230072969 + 3 ^ 40 * 4948753 * 2
def baseEnd_4948753 : Nat := 2541088929379581714828605

theorem tailTrace_4948753 : CollatzResearch.WordTrace tailWord_4948753 prefixEnd_4948753 2541088929379581714828605 := by
  unfold tailWord_4948753
  simp only [CollatzResearch.WordTrace]
  refine ⟨180495850240520535569314913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120330566827013690379543275 180495850240520535569314913)
  ·
    refine ⟨135371887680390401676986185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 180495850240520535569314913 135371887680390401676986185)
    ·
      refine ⟨101528915760292801257739639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 135371887680390401676986185 101528915760292801257739639)
      ·
        refine ⟨152293373640439201886609459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101528915760292801257739639 152293373640439201886609459)
        ·
          refine ⟨228440060460658802829914189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 152293373640439201886609459 228440060460658802829914189)
          ·
            refine ⟨85665022672747051061217821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 228440060460658802829914189 85665022672747051061217821)
            ·
              refine ⟨32124383502280144147956683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 85665022672747051061217821 32124383502280144147956683)
              ·
                refine ⟨48186575253420216221935025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32124383502280144147956683 48186575253420216221935025)
                ·
                  refine ⟨36139931440065162166451269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 48186575253420216221935025 36139931440065162166451269)
                  ·
                    refine ⟨6776237145012217906209613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 36139931440065162166451269 6776237145012217906209613)
                    ·
                      refine ⟨2541088929379581714828605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6776237145012217906209613 2541088929379581714828605)
                      ·
                        rfl

theorem cell23_4948753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 4, 3].length) (baseStart_4948753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4948753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4948753 prefixEnd_4948753 := by exact prefixLift 4948753
  have htrace : WordTrace (prefixWord ++ tailWord_4948753) baseStart_4948753 baseEnd_4948753 := by
    simpa [prefixWord, tailWord_4948753, baseEnd_4948753] using wordTrace_append hprefix tailTrace_4948753
  have hstable : (prefixWord ++ tailWord_4948753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4948753).length < 2 ^ (prefixWord ++ tailWord_4948753).sum := by decide
  have hdescent : baseEnd_4948753 < baseStart_4948753 := by decide
  rcases family_descends (prefixWord ++ tailWord_4948753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4948767 : List Nat := [1, 1, 2, 4, 2, 3, 2, 1, 1, 4, 2]
def baseStart_4948767 : Nat := 118140960795 + 4948767 * 2 ^ 59
def prefixEnd_4948767 : Nat := 4983230072969 + 3 ^ 40 * 4948767 * 2
def baseEnd_4948767 : Nat := 2541096118108744660053541

theorem tailTrace_4948767 : CollatzResearch.WordTrace tailWord_4948767 prefixEnd_4948767 2541096118108744660053541 := by
  unfold tailWord_4948767
  simp only [CollatzResearch.WordTrace]
  refine ⟨180496360862469815960324555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120330907241646543973549703 180496360862469815960324555)
  ·
    refine ⟨270744541293704723940486833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 180496360862469815960324555 270744541293704723940486833)
    ·
      refine ⟨203058405970278542955365125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 270744541293704723940486833 203058405970278542955365125)
      ·
        refine ⟨38073451119427226804130961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 203058405970278542955365125 38073451119427226804130961)
        ·
          refine ⟨28555088339570420103098221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38073451119427226804130961 28555088339570420103098221)
          ·
            refine ⟨10708158127338907538661833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28555088339570420103098221 10708158127338907538661833)
            ·
              refine ⟨8031118595504180653996375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10708158127338907538661833 8031118595504180653996375)
              ·
                refine ⟨12046677893256270980994563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8031118595504180653996375 12046677893256270980994563)
                ·
                  refine ⟨18070016839884406471491845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12046677893256270980994563 18070016839884406471491845)
                  ·
                    refine ⟨3388128157478326213404721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18070016839884406471491845 3388128157478326213404721)
                    ·
                      refine ⟨2541096118108744660053541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3388128157478326213404721 2541096118108744660053541)
                      ·
                        rfl

theorem cell23_4948767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 3, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 3, 2, 1, 1, 4, 2].length) (baseStart_4948767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4948767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4948767 prefixEnd_4948767 := by exact prefixLift 4948767
  have htrace : WordTrace (prefixWord ++ tailWord_4948767) baseStart_4948767 baseEnd_4948767 := by
    simpa [prefixWord, tailWord_4948767, baseEnd_4948767] using wordTrace_append hprefix tailTrace_4948767
  have hstable : (prefixWord ++ tailWord_4948767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4948767).length < 2 ^ (prefixWord ++ tailWord_4948767).sum := by decide
  have hdescent : baseEnd_4948767 < baseStart_4948767 := by decide
  rcases family_descends (prefixWord ++ tailWord_4948767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4948773 : List Nat := [1, 3, 1, 2, 3, 1, 3, 2, 7]
def baseStart_4948773 : Nat := 118140960795 + 4948773 * 2 ^ 59
def prefixEnd_4948773 : Nat := 4983230072969 + 3 ^ 40 * 4948773 * 2
def baseEnd_4948773 : Nat := 282344355443630181842057

theorem tailTrace_4948773 : CollatzResearch.WordTrace tailWord_4948773 prefixEnd_4948773 282344355443630181842057 := by
  unfold tailWord_4948773
  simp only [CollatzResearch.WordTrace]
  refine ⟨180496579700448078985042973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120331053133632052656695315 180496579700448078985042973)
  ·
    refine ⟨67686217387668029619391115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 180496579700448078985042973 67686217387668029619391115)
    ·
      refine ⟨101529326081502044429086673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67686217387668029619391115 101529326081502044429086673)
      ·
        refine ⟨76146994561126533321815005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 101529326081502044429086673 76146994561126533321815005)
        ·
          refine ⟨28555122960422449995680627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 76146994561126533321815005 28555122960422449995680627)
          ·
            refine ⟨42832684440633674993520941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28555122960422449995680627 42832684440633674993520941)
            ·
              refine ⟨16062256665237628122570353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 42832684440633674993520941 16062256665237628122570353)
              ·
                refine ⟨12046692498928221091927765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16062256665237628122570353 12046692498928221091927765)
                ·
                  refine ⟨282344355443630181842057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12046692498928221091927765 282344355443630181842057)
                  ·
                    rfl

theorem cell23_4948773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 3, 2, 7].length) (baseStart_4948773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4948773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4948773 prefixEnd_4948773 := by exact prefixLift 4948773
  have htrace : WordTrace (prefixWord ++ tailWord_4948773) baseStart_4948773 baseEnd_4948773 := by
    simpa [prefixWord, tailWord_4948773, baseEnd_4948773] using wordTrace_append hprefix tailTrace_4948773
  have hstable : (prefixWord ++ tailWord_4948773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4948773).length < 2 ^ (prefixWord ++ tailWord_4948773).sum := by decide
  have hdescent : baseEnd_4948773 < baseStart_4948773 := by decide
  rcases family_descends (prefixWord ++ tailWord_4948773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4948783 : List Nat := [1, 1, 2, 1, 2, 1, 2, 1, 6, 3, 3]
def baseStart_4948783 : Nat := 118140960795 + 4948783 * 2 ^ 59
def prefixEnd_4948783 : Nat := 4983230072969 + 3 ^ 40 * 4948783 * 2
def baseEnd_4948783 : Nat := 2541104333799216597453467

theorem tailTrace_4948783 : CollatzResearch.WordTrace tailWord_4948783 prefixEnd_4948783 2541104333799216597453467 := by
  unfold tailWord_4948783
  simp only [CollatzResearch.WordTrace]
  refine ⟨180496944430411850692907003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120331296286941233795271335 180496944430411850692907003)
  ·
    refine ⟨270745416645617776039360505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 180496944430411850692907003 270745416645617776039360505)
    ·
      refine ⟨203059062484213332029520379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 270745416645617776039360505 203059062484213332029520379)
      ·
        refine ⟨304588593726319998044280569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 203059062484213332029520379 304588593726319998044280569)
        ·
          refine ⟨228441445294739998533210427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 304588593726319998044280569 228441445294739998533210427)
          ·
            refine ⟨342662167942109997799815641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 228441445294739998533210427 342662167942109997799815641)
            ·
              refine ⟨256996625956582498349861731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 342662167942109997799815641 256996625956582498349861731)
              ·
                refine ⟨385494938934873747524792597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 256996625956582498349861731 385494938934873747524792597)
                ·
                  refine ⟨18070075262572206915224653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 385494938934873747524792597 18070075262572206915224653)
                  ·
                    refine ⟨6776278223464577593209245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18070075262572206915224653 6776278223464577593209245)
                    ·
                      refine ⟨2541104333799216597453467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6776278223464577593209245 2541104333799216597453467)
                      ·
                        rfl

theorem cell23_4948783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 1, 6, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 1, 6, 3, 3].length) (baseStart_4948783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4948783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4948783 prefixEnd_4948783 := by exact prefixLift 4948783
  have htrace : WordTrace (prefixWord ++ tailWord_4948783) baseStart_4948783 baseEnd_4948783 := by
    simpa [prefixWord, tailWord_4948783, baseEnd_4948783] using wordTrace_append hprefix tailTrace_4948783
  have hstable : (prefixWord ++ tailWord_4948783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4948783).length < 2 ^ (prefixWord ++ tailWord_4948783).sum := by decide
  have hdescent : baseEnd_4948783 < baseStart_4948783 := by decide
  rcases family_descends (prefixWord ++ tailWord_4948783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4948788 : List Nat := [2, 5, 1, 1, 3, 2, 2, 1, 1, 3, 2]
def baseStart_4948788 : Nat := 118140960795 + 4948788 * 2 ^ 59
def prefixEnd_4948788 : Nat := 4983230072969 + 3 ^ 40 * 4948788 * 2
def baseEnd_4948788 : Nat := 2541106901202489077890945

theorem tailTrace_4948788 : CollatzResearch.WordTrace tailWord_4948788 prefixEnd_4948788 2541106901202489077890945 := by
  unfold tailWord_4948788
  simp only [CollatzResearch.WordTrace]
  refine ⟨90248563397696868273419509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120331417863595824364559345 90248563397696868273419509)
  ·
    refine ⟨8460802818534081400633079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 90248563397696868273419509 8460802818534081400633079)
    ·
      refine ⟨12691204227801122100949619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8460802818534081400633079 12691204227801122100949619)
      ·
        refine ⟨19036806341701683151424429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12691204227801122100949619 19036806341701683151424429)
        ·
          refine ⟨7138802378138131181784161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19036806341701683151424429 7138802378138131181784161)
          ·
            refine ⟨5354101783603598386338121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7138802378138131181784161 5354101783603598386338121)
            ·
              refine ⟨4015576337702698789753591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5354101783603598386338121 4015576337702698789753591)
              ·
                refine ⟨6023364506554048184630387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4015576337702698789753591 6023364506554048184630387)
                ·
                  refine ⟨9035046759831072276945581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6023364506554048184630387 9035046759831072276945581)
                  ·
                    refine ⟨3388142534936652103854593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9035046759831072276945581 3388142534936652103854593)
                    ·
                      refine ⟨2541106901202489077890945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3388142534936652103854593 2541106901202489077890945)
                      ·
                        rfl

theorem cell23_4948788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 2, 2, 1, 1, 3, 2].length) (baseStart_4948788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4948788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4948788 prefixEnd_4948788 := by exact prefixLift 4948788
  have htrace : WordTrace (prefixWord ++ tailWord_4948788) baseStart_4948788 baseEnd_4948788 := by
    simpa [prefixWord, tailWord_4948788, baseEnd_4948788] using wordTrace_append hprefix tailTrace_4948788
  have hstable : (prefixWord ++ tailWord_4948788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4948788).length < 2 ^ (prefixWord ++ tailWord_4948788).sum := by decide
  have hdescent : baseEnd_4948788 < baseStart_4948788 := by decide
  rcases family_descends (prefixWord ++ tailWord_4948788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4948801 : List Nat := [1, 2, 5, 3, 1, 1, 1, 1, 4, 2, 2]
def baseStart_4948801 : Nat := 118140960795 + 4948801 * 2 ^ 59
def prefixEnd_4948801 : Nat := 4983230072969 + 3 ^ 40 * 4948801 * 2
def baseEnd_4948801 : Nat := 2541113576450997527028385

theorem tailTrace_4948801 : CollatzResearch.WordTrace tailWord_4948801 prefixEnd_4948801 2541113576450997527028385 := by
  unfold tailWord_4948801
  simp only [CollatzResearch.WordTrace]
  refine ⟨180497600944346639767062257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120331733962897759844708171 180497600944346639767062257)
  ·
    refine ⟨135373200708259979825296693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 180497600944346639767062257 135373200708259979825296693)
    ·
      refine ⟨12691237566399373108621565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 135373200708259979825296693 12691237566399373108621565)
      ·
        refine ⟨4759214087399764915733087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12691237566399373108621565 4759214087399764915733087)
        ·
          refine ⟨7138821131099647373599631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4759214087399764915733087 7138821131099647373599631)
          ·
            refine ⟨10708231696649471060399447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7138821131099647373599631 10708231696649471060399447)
            ·
              refine ⟨16062347544974206590599171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10708231696649471060399447 16062347544974206590599171)
              ·
                refine ⟨24093521317461309885898757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16062347544974206590599171 24093521317461309885898757)
                ·
                  refine ⟨4517535247023995603606017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24093521317461309885898757 4517535247023995603606017)
                  ·
                    refine ⟨3388151435267996702704513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4517535247023995603606017 3388151435267996702704513)
                    ·
                      refine ⟨2541113576450997527028385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3388151435267996702704513 2541113576450997527028385)
                      ·
                        rfl

theorem cell23_4948801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 1, 1, 1, 4, 2, 2].length) (baseStart_4948801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4948801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4948801 prefixEnd_4948801 := by exact prefixLift 4948801
  have htrace : WordTrace (prefixWord ++ tailWord_4948801) baseStart_4948801 baseEnd_4948801 := by
    simpa [prefixWord, tailWord_4948801, baseEnd_4948801] using wordTrace_append hprefix tailTrace_4948801
  have hstable : (prefixWord ++ tailWord_4948801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4948801).length < 2 ^ (prefixWord ++ tailWord_4948801).sum := by decide
  have hdescent : baseEnd_4948801 < baseStart_4948801 := by decide
  rcases family_descends (prefixWord ++ tailWord_4948801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4948803 : List Nat := [1, 1, 1, 3, 1, 4, 2, 1, 4, 5]
def baseStart_4948803 : Nat := 118140960795 + 4948803 * 2 ^ 59
def prefixEnd_4948803 : Nat := 4983230072969 + 3 ^ 40 * 4948803 * 2
def baseEnd_4948803 : Nat := 847038201137435506401125

theorem tailTrace_4948803 : CollatzResearch.WordTrace tailWord_4948803 prefixEnd_4948803 847038201137435506401125 := by
  unfold tailWord_4948803
  simp only [CollatzResearch.WordTrace]
  refine ⟨180497673890339394108635063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120331782593559596072423375 180497673890339394108635063)
  ·
    refine ⟨270746510835509091162952595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 180497673890339394108635063 270746510835509091162952595)
    ·
      refine ⟨406119766253263636744428893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 270746510835509091162952595 406119766253263636744428893)
      ·
        refine ⟨152294912344973863779160835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 406119766253263636744428893 152294912344973863779160835)
        ·
          refine ⟨228442368517460795668741253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 152294912344973863779160835 228442368517460795668741253)
          ·
            refine ⟨42832944097023899187888985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 228442368517460795668741253 42832944097023899187888985)
            ·
              refine ⟨32124708072767924390916739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42832944097023899187888985 32124708072767924390916739)
              ·
                refine ⟨48187062109151886586375109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32124708072767924390916739 48187062109151886586375109)
                ·
                  refine ⟨9035074145465978734945333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 48187062109151886586375109 9035074145465978734945333)
                  ·
                    refine ⟨847038201137435506401125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9035074145465978734945333 847038201137435506401125)
                    ·
                      rfl

theorem cell23_4948803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 2, 1, 4, 5].length) (baseStart_4948803 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4948803 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4948803 prefixEnd_4948803 := by exact prefixLift 4948803
  have htrace : WordTrace (prefixWord ++ tailWord_4948803) baseStart_4948803 baseEnd_4948803 := by
    simpa [prefixWord, tailWord_4948803, baseEnd_4948803] using wordTrace_append hprefix tailTrace_4948803
  have hstable : (prefixWord ++ tailWord_4948803).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4948803).length < 2 ^ (prefixWord ++ tailWord_4948803).sum := by decide
  have hdescent : baseEnd_4948803 < baseStart_4948803 := by decide
  rcases family_descends (prefixWord ++ tailWord_4948803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4948810 : List Nat := [3, 1, 2, 1, 1, 1, 2, 3, 2, 5, 2]
def baseStart_4948810 : Nat := 118140960795 + 4948810 * 2 ^ 59
def prefixEnd_4948810 : Nat := 4983230072969 + 3 ^ 40 * 4948810 * 2
def baseEnd_4948810 : Nat := 2541118197776887991815843

theorem tailTrace_4948810 : CollatzResearch.WordTrace tailWord_4948810 prefixEnd_4948810 2541118197776887991815843 := by
  unfold tailWord_4948810
  simp only [CollatzResearch.WordTrace]
  refine ⟨45124482300328508576034971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 120331952800876022869426589 45124482300328508576034971)
  ·
    refine ⟨67686723450492762864052457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45124482300328508576034971 67686723450492762864052457)
    ·
      refine ⟨50765042587869572148039343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67686723450492762864052457 50765042587869572148039343)
      ·
        refine ⟨76147563881804358222059015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50765042587869572148039343 76147563881804358222059015)
        ·
          refine ⟨114221345822706537333088523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76147563881804358222059015 114221345822706537333088523)
          ·
            refine ⟨171332018734059805999632785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 114221345822706537333088523 171332018734059805999632785)
            ·
              refine ⟨128499014050544854499724589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 171332018734059805999632785 128499014050544854499724589)
              ·
                refine ⟨48187130268954320437396721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 128499014050544854499724589 48187130268954320437396721)
                ·
                  refine ⟨36140347701715740328047541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 48187130268954320437396721 36140347701715740328047541)
                  ·
                    refine ⟨3388157597035850655754457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 36140347701715740328047541 3388157597035850655754457)
                    ·
                      refine ⟨2541118197776887991815843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3388157597035850655754457 2541118197776887991815843)
                      ·
                        rfl

theorem cell23_4948810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 3, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 3, 2, 5, 2].length) (baseStart_4948810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4948810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4948810 prefixEnd_4948810 := by exact prefixLift 4948810
  have htrace : WordTrace (prefixWord ++ tailWord_4948810) baseStart_4948810 baseEnd_4948810 := by
    simpa [prefixWord, tailWord_4948810, baseEnd_4948810] using wordTrace_append hprefix tailTrace_4948810
  have hstable : (prefixWord ++ tailWord_4948810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4948810).length < 2 ^ (prefixWord ++ tailWord_4948810).sum := by decide
  have hdescent : baseEnd_4948810 < baseStart_4948810 := by decide
  rcases family_descends (prefixWord ++ tailWord_4948810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4948840 : List Nat := [2, 1, 4, 2, 1, 2, 2, 1, 1, 3, 4]
def baseStart_4948840 : Nat := 118140960795 + 4948840 * 2 ^ 59
def prefixEnd_4948840 : Nat := 4983230072969 + 3 ^ 40 * 4948840 * 2
def baseEnd_4948840 : Nat := 2541133602196522874440705

theorem tailTrace_4948840 : CollatzResearch.WordTrace tailWord_4948840 prefixEnd_4948840 2541133602196522874440705 := by
  unfold tailWord_4948840
  simp only [CollatzResearch.WordTrace]
  refine ⟨90249511695602674713865987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120332682260803566285154649 90249511695602674713865987)
  ·
    refine ⟨135374267543404012070798981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90249511695602674713865987 135374267543404012070798981)
    ·
      refine ⟨25382675164388252263274809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 135374267543404012070798981 25382675164388252263274809)
      ·
        refine ⟨19037006373291189197456107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25382675164388252263274809 19037006373291189197456107)
        ·
          refine ⟨28555509559936783796184161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19037006373291189197456107 28555509559936783796184161)
          ·
            refine ⟨21416632169952587847138121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28555509559936783796184161 21416632169952587847138121)
            ·
              refine ⟨16062474127464440885353591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21416632169952587847138121 16062474127464440885353591)
              ·
                refine ⟨24093711191196661328030387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16062474127464440885353591 24093711191196661328030387)
                ·
                  refine ⟨36140566786794991992045581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24093711191196661328030387 36140566786794991992045581)
                  ·
                    refine ⟨13552712545048121997017093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 36140566786794991992045581 13552712545048121997017093)
                    ·
                      refine ⟨2541133602196522874440705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13552712545048121997017093 2541133602196522874440705)
                      ·
                        rfl

theorem cell23_4948840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 2, 1, 1, 3, 4].length) (baseStart_4948840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4948840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4948840 prefixEnd_4948840 := by exact prefixLift 4948840
  have htrace : WordTrace (prefixWord ++ tailWord_4948840) baseStart_4948840 baseEnd_4948840 := by
    simpa [prefixWord, tailWord_4948840, baseEnd_4948840] using wordTrace_append hprefix tailTrace_4948840
  have hstable : (prefixWord ++ tailWord_4948840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4948840).length < 2 ^ (prefixWord ++ tailWord_4948840).sum := by decide
  have hdescent : baseEnd_4948840 < baseStart_4948840 := by decide
  rcases family_descends (prefixWord ++ tailWord_4948840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4948850 : List Nat := [3, 2, 1, 2, 1, 1, 2, 2, 5, 4]
def baseStart_4948850 : Nat := 118140960795 + 4948850 * 2 ^ 59
def prefixEnd_4948850 : Nat := 4983230072969 + 3 ^ 40 * 4948850 * 2
def baseEnd_4948850 : Nat := 847046245667689278438553

theorem tailTrace_4948850 : CollatzResearch.WordTrace tailWord_4948850 prefixEnd_4948850 847046245667689278438553 := by
  unfold tailWord_4948850
  simp only [CollatzResearch.WordTrace]
  refine ⟨45124847030292280283899001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 120332925414112747423730669 45124847030292280283899001)
  ·
    refine ⟨33843635272719210212924251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45124847030292280283899001 33843635272719210212924251)
    ·
      refine ⟨50765452909078815319386377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33843635272719210212924251 50765452909078815319386377)
      ·
        refine ⟨38074089681809111489539783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50765452909078815319386377 38074089681809111489539783)
        ·
          refine ⟨57111134522713667234309675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38074089681809111489539783 57111134522713667234309675)
          ·
            refine ⟨85666701784070500851464513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57111134522713667234309675 85666701784070500851464513)
            ·
              refine ⟨64250026338052875638598385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 85666701784070500851464513 64250026338052875638598385)
              ·
                refine ⟨48187519753539656728948789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 64250026338052875638598385 48187519753539656728948789)
                ·
                  refine ⟨4517579976894342818338949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 48187519753539656728948789 4517579976894342818338949)
                  ·
                    refine ⟨847046245667689278438553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4517579976894342818338949 847046245667689278438553)
                    ·
                      rfl

theorem cell23_4948850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 2, 2, 5, 4].length) (baseStart_4948850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4948850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4948850 prefixEnd_4948850 := by exact prefixLift 4948850
  have htrace : WordTrace (prefixWord ++ tailWord_4948850) baseStart_4948850 baseEnd_4948850 := by
    simpa [prefixWord, tailWord_4948850, baseEnd_4948850] using wordTrace_append hprefix tailTrace_4948850
  have hstable : (prefixWord ++ tailWord_4948850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4948850).length < 2 ^ (prefixWord ++ tailWord_4948850).sum := by decide
  have hdescent : baseEnd_4948850 < baseStart_4948850 := by decide
  rcases family_descends (prefixWord ++ tailWord_4948850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4948863 : List Nat := [1, 1, 2, 2, 1, 1, 6, 1, 8]
def baseStart_4948863 : Nat := 118140960795 + 4948863 * 2 ^ 59
def prefixEnd_4948863 : Nat := 4983230072969 + 3 ^ 40 * 4948863 * 2
def baseEnd_4948863 : Nat := 282349490250175142717011

theorem tailTrace_4948863 : CollatzResearch.WordTrace tailWord_4948863 prefixEnd_4948863 282349490250175142717011 := by
  unfold tailWord_4948863
  simp only [CollatzResearch.WordTrace]
  refine ⟨180499862270122024355819243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120333241513414682903879495 180499862270122024355819243)
  ·
    refine ⟨270749793405183036533728865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 180499862270122024355819243 270749793405183036533728865)
    ·
      refine ⟨203062345053887277400296649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 270749793405183036533728865 203062345053887277400296649)
      ·
        refine ⟨152296758790415458050222487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 203062345053887277400296649 152296758790415458050222487)
        ·
          refine ⟨228445138185623187075333731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 152296758790415458050222487 228445138185623187075333731)
          ·
            refine ⟨342667707278434780613000597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 228445138185623187075333731 342667707278434780613000597)
            ·
              refine ⟨16062548778676630341234403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 342667707278434780613000597 16062548778676630341234403)
              ·
                refine ⟨24093823168014945511851605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16062548778676630341234403 24093823168014945511851605)
                ·
                  refine ⟨282349490250175142717011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 24093823168014945511851605 282349490250175142717011)
                  ·
                    rfl

theorem cell23_4948863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 6, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 6, 1, 8].length) (baseStart_4948863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4948863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4948863 prefixEnd_4948863 := by exact prefixLift 4948863
  have htrace : WordTrace (prefixWord ++ tailWord_4948863) baseStart_4948863 baseEnd_4948863 := by
    simpa [prefixWord, tailWord_4948863, baseEnd_4948863] using wordTrace_append hprefix tailTrace_4948863
  have hstable : (prefixWord ++ tailWord_4948863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4948863).length < 2 ^ (prefixWord ++ tailWord_4948863).sum := by decide
  have hdescent : baseEnd_4948863 < baseStart_4948863 := by decide
  rcases family_descends (prefixWord ++ tailWord_4948863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4948957 : List Nat := [1, 4, 3, 1, 2, 1, 2, 2, 1, 6]
def baseStart_4948957 : Nat := 118140960795 + 4948957 * 2 ^ 59
def prefixEnd_4948957 : Nat := 4983230072969 + 3 ^ 40 * 4948957 * 2
def baseEnd_4948957 : Nat := 847064559811032972225889

theorem tailTrace_4948957 : CollatzResearch.WordTrace tailWord_4948957 prefixEnd_4948957 847064559811032972225889 := by
  unfold tailWord_4948957
  simp only [CollatzResearch.WordTrace]
  refine ⟨180503290731781478409741125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120335527154520985606494083 180503290731781478409741125)
  ·
    refine ⟨33844367012209027201826461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 180503290731781478409741125 33844367012209027201826461)
    ·
      refine ⟨12691637629578385200684923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33844367012209027201826461 12691637629578385200684923)
      ·
        refine ⟨19037456444367577801027385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12691637629578385200684923 19037456444367577801027385)
        ·
          refine ⟨14278092333275683350770539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19037456444367577801027385 14278092333275683350770539)
          ·
            refine ⟨21417138499913525026155809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14278092333275683350770539 21417138499913525026155809)
            ·
              refine ⟨16062853874935143769616857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21417138499913525026155809 16062853874935143769616857)
              ·
                refine ⟨12047140406201357827212643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16062853874935143769616857 12047140406201357827212643)
                ·
                  refine ⟨18070710609302036740818965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12047140406201357827212643 18070710609302036740818965)
                  ·
                    refine ⟨847064559811032972225889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18070710609302036740818965 847064559811032972225889)
                    ·
                      rfl

theorem cell23_4948957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 2, 2, 1, 6].length) (baseStart_4948957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4948957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4948957 prefixEnd_4948957 := by exact prefixLift 4948957
  have htrace : WordTrace (prefixWord ++ tailWord_4948957) baseStart_4948957 baseEnd_4948957 := by
    simpa [prefixWord, tailWord_4948957, baseEnd_4948957] using wordTrace_append hprefix tailTrace_4948957
  have hstable : (prefixWord ++ tailWord_4948957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4948957).length < 2 ^ (prefixWord ++ tailWord_4948957).sum := by decide
  have hdescent : baseEnd_4948957 < baseStart_4948957 := by decide
  rcases family_descends (prefixWord ++ tailWord_4948957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4948970 : List Nat := [3, 1, 3, 1, 2, 3, 10]
def baseStart_4948970 : Nat := 118140960795 + 4948970 * 2 ^ 59
def prefixEnd_4948970 : Nat := 4983230072969 + 3 ^ 40 * 4948970 * 2
def baseEnd_4948970 : Nat := 31372843884958115627347

theorem tailTrace_4948970 : CollatzResearch.WordTrace tailWord_4948970 prefixEnd_4948970 31372843884958115627347 := by
  unfold tailWord_4948970
  simp only [CollatzResearch.WordTrace]
  refine ⟨45125941220183595407491091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 120335843253822921086642909 45125941220183595407491091)
  ·
    refine ⟨67688911830275393111236637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45125941220183595407491091 67688911830275393111236637)
    ·
      refine ⟨25383341936353272416713739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 67688911830275393111236637 25383341936353272416713739)
      ·
        refine ⟨38075012904529908625070609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25383341936353272416713739 38075012904529908625070609)
        ·
          refine ⟨28556259678397431468802957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38075012904529908625070609 28556259678397431468802957)
          ·
            refine ⟨10708597379399036800801109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28556259678397431468802957 10708597379399036800801109)
            ·
              refine ⟨31372843884958115627347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 10708597379399036800801109 31372843884958115627347)
              ·
                rfl

theorem cell23_4948970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 3, 10].length) (baseStart_4948970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4948970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4948970 prefixEnd_4948970 := by exact prefixLift 4948970
  have htrace : WordTrace (prefixWord ++ tailWord_4948970) baseStart_4948970 baseEnd_4948970 := by
    simpa [prefixWord, tailWord_4948970, baseEnd_4948970] using wordTrace_append hprefix tailTrace_4948970
  have hstable : (prefixWord ++ tailWord_4948970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4948970).length < 2 ^ (prefixWord ++ tailWord_4948970).sum := by decide
  have hdescent : baseEnd_4948970 < baseStart_4948970 := by decide
  rcases family_descends (prefixWord ++ tailWord_4948970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4948974 : List Nat := [4, 1, 2, 1, 4, 1, 1, 1, 4, 4]
def baseStart_4948974 : Nat := 118140960795 + 4948974 * 2 ^ 59
def prefixEnd_4948974 : Nat := 4983230072969 + 3 ^ 40 * 4948974 * 2
def baseEnd_4948974 : Nat := 847067469534741783388363

theorem tailTrace_4948974 : CollatzResearch.WordTrace tailWord_4948974 prefixEnd_4948974 847067469534741783388363 := by
  unfold tailWord_4948974
  simp only [CollatzResearch.WordTrace]
  refine ⟨22562988846589986289138747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 120335940515146593542073317 22562988846589986289138747)
  ·
    refine ⟨33844483269884979433708121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22562988846589986289138747 33844483269884979433708121)
    ·
      refine ⟨25383362452413734575281091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33844483269884979433708121 25383362452413734575281091)
      ·
        refine ⟨38075043678620601862921637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25383362452413734575281091 38075043678620601862921637)
        ·
          refine ⟨7139070689741362849297807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 38075043678620601862921637 7139070689741362849297807)
          ·
            refine ⟨10708606034612044273946711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7139070689741362849297807 10708606034612044273946711)
            ·
              refine ⟨16062909051918066410920067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10708606034612044273946711 16062909051918066410920067)
              ·
                refine ⟨24094363577877099616380101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16062909051918066410920067 24094363577877099616380101)
                ·
                  refine ⟨4517693170851956178071269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24094363577877099616380101 4517693170851956178071269)
                  ·
                    refine ⟨847067469534741783388363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4517693170851956178071269 847067469534741783388363)
                    ·
                      rfl

theorem cell23_4948974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 1, 1, 1, 4, 4].length) (baseStart_4948974 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4948974 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4948974 prefixEnd_4948974 := by exact prefixLift 4948974
  have htrace : WordTrace (prefixWord ++ tailWord_4948974) baseStart_4948974 baseEnd_4948974 := by
    simpa [prefixWord, tailWord_4948974, baseEnd_4948974] using wordTrace_append hprefix tailTrace_4948974
  have hstable : (prefixWord ++ tailWord_4948974).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4948974).length < 2 ^ (prefixWord ++ tailWord_4948974).sum := by decide
  have hdescent : baseEnd_4948974 < baseStart_4948974 := by decide
  rcases family_descends (prefixWord ++ tailWord_4948974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4949015 : List Nat := [1, 1, 3, 5, 1, 3, 1, 3, 1, 2, 2]
def baseStart_4949015 : Nat := 118140960795 + 4949015 * 2 ^ 59
def prefixEnd_4949015 : Nat := 4983230072969 + 3 ^ 40 * 4949015 * 2
def baseEnd_4949015 : Nat := 2541223461311059689752401

theorem tailTrace_4949015 : CollatzResearch.WordTrace tailWord_4949015 prefixEnd_4949015 2541223461311059689752401 := by
  unfold tailWord_4949015
  simp only [CollatzResearch.WordTrace]
  refine ⟨180505406165571354315352499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120336937443714236210234999 180505406165571354315352499)
  ·
    refine ⟨270758109248357031473028749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 180505406165571354315352499 270758109248357031473028749)
    ·
      refine ⟨101534290968133886802385781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 270758109248357031473028749 101534290968133886802385781)
      ·
        refine ⟨9518839778262551887723667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 101534290968133886802385781 9518839778262551887723667)
        ·
          refine ⟨14278259667393827831585501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9518839778262551887723667 14278259667393827831585501)
          ·
            refine ⟨5354347375272685436844563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14278259667393827831585501 5354347375272685436844563)
            ·
              refine ⟨8031521062909028155266845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5354347375272685436844563 8031521062909028155266845)
              ·
                refine ⟨3011820398590885558225067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8031521062909028155266845 3011820398590885558225067)
                ·
                  refine ⟨4517730597886328337337601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3011820398590885558225067 4517730597886328337337601)
                  ·
                    refine ⟨3388297948414746253003201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4517730597886328337337601 3388297948414746253003201)
                    ·
                      refine ⟨2541223461311059689752401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3388297948414746253003201 2541223461311059689752401)
                      ·
                        rfl

theorem cell23_4949015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 3, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 3, 1, 3, 1, 2, 2].length) (baseStart_4949015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4949015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4949015 prefixEnd_4949015 := by exact prefixLift 4949015
  have htrace : WordTrace (prefixWord ++ tailWord_4949015) baseStart_4949015 baseEnd_4949015 := by
    simpa [prefixWord, tailWord_4949015, baseEnd_4949015] using wordTrace_append hprefix tailTrace_4949015
  have hstable : (prefixWord ++ tailWord_4949015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4949015).length < 2 ^ (prefixWord ++ tailWord_4949015).sum := by decide
  have hdescent : baseEnd_4949015 < baseStart_4949015 := by decide
  rcases family_descends (prefixWord ++ tailWord_4949015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4949031 : List Nat := [1, 1, 7, 1, 1, 1, 2, 1, 4, 1, 3]
def baseStart_4949031 : Nat := 118140960795 + 4949031 * 2 ^ 59
def prefixEnd_4949031 : Nat := 4983230072969 + 3 ^ 40 * 4949031 * 2
def baseEnd_4949031 : Nat := 2541231677001531627152327

theorem tailTrace_4949031 : CollatzResearch.WordTrace tailWord_4949031 prefixEnd_4949031 2541231677001531627152327 := by
  unfold tailWord_4949031
  simp only [CollatzResearch.WordTrace]
  refine ⟨180505989733513389047934947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120337326489008926031956631 180505989733513389047934947)
  ·
    refine ⟨270758984600270083571902421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 180505989733513389047934947 270758984600270083571902421)
    ·
      refine ⟨6345913701568830083716463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 270758984600270083571902421 6345913701568830083716463)
      ·
        refine ⟨9518870552353245125574695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6345913701568830083716463 9518870552353245125574695)
        ·
          refine ⟨14278305828529867688362043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9518870552353245125574695 14278305828529867688362043)
          ·
            refine ⟨21417458742794801532543065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14278305828529867688362043 21417458742794801532543065)
            ·
              refine ⟨16063094057096101149407299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21417458742794801532543065 16063094057096101149407299)
              ·
                refine ⟨24094641085644151724110949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16063094057096101149407299 24094641085644151724110949)
                ·
                  refine ⟨4517745203558278448270803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24094641085644151724110949 4517745203558278448270803)
                  ·
                    refine ⟨6776617805337417672406205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4517745203558278448270803 6776617805337417672406205)
                    ·
                      refine ⟨2541231677001531627152327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6776617805337417672406205 2541231677001531627152327)
                      ·
                        rfl

theorem cell23_4949031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 2, 1, 4, 1, 3].length) (baseStart_4949031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4949031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4949031 prefixEnd_4949031 := by exact prefixLift 4949031
  have htrace : WordTrace (prefixWord ++ tailWord_4949031) baseStart_4949031 baseEnd_4949031 := by
    simpa [prefixWord, tailWord_4949031, baseEnd_4949031] using wordTrace_append hprefix tailTrace_4949031
  have hstable : (prefixWord ++ tailWord_4949031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4949031).length < 2 ^ (prefixWord ++ tailWord_4949031).sum := by decide
  have hdescent : baseEnd_4949031 < baseStart_4949031 := by decide
  rcases family_descends (prefixWord ++ tailWord_4949031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4949040 : List Nat := [2, 1, 1, 1, 2, 4, 1, 2, 1, 3, 5]
def baseStart_4949040 : Nat := 118140960795 + 4949040 * 2 ^ 59
def prefixEnd_4949040 : Nat := 4983230072969 + 3 ^ 40 * 4949040 * 2
def baseEnd_4949040 : Nat := 2541236298327422091939785

theorem tailTrace_4949040 : CollatzResearch.WordTrace tailWord_4949040 prefixEnd_4949040 2541236298327422091939785 := by
  unfold tailWord_4949040
  simp only [CollatzResearch.WordTrace]
  refine ⟨90253158995240391792506287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120337545326987189056675049 90253158995240391792506287)
  ·
    refine ⟨135379738492860587688759431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90253158995240391792506287 135379738492860587688759431)
    ·
      refine ⟨203069607739290881533139147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 135379738492860587688759431 203069607739290881533139147)
      ·
        refine ⟨304604411608936322299708721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 203069607739290881533139147 304604411608936322299708721)
        ·
          refine ⟨228453308706702241724781541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 304604411608936322299708721 228453308706702241724781541)
          ·
            refine ⟨42834995382506670323396539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 228453308706702241724781541 42834995382506670323396539)
            ·
              refine ⟨64252493073760005485094809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42834995382506670323396539 64252493073760005485094809)
              ·
                refine ⟨48189369805320004113821107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 64252493073760005485094809 48189369805320004113821107)
                ·
                  refine ⟨72284054707980006170731661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 48189369805320004113821107 72284054707980006170731661)
                  ·
                    refine ⟨27106520515492502314024373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 72284054707980006170731661 27106520515492502314024373)
                    ·
                      refine ⟨2541236298327422091939785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27106520515492502314024373 2541236298327422091939785)
                      ·
                        rfl

theorem cell23_4949040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 1, 2, 1, 3, 5].length) (baseStart_4949040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4949040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4949040 prefixEnd_4949040 := by exact prefixLift 4949040
  have htrace : WordTrace (prefixWord ++ tailWord_4949040) baseStart_4949040 baseEnd_4949040 := by
    simpa [prefixWord, tailWord_4949040, baseEnd_4949040] using wordTrace_append hprefix tailTrace_4949040
  have hstable : (prefixWord ++ tailWord_4949040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4949040).length < 2 ^ (prefixWord ++ tailWord_4949040).sum := by decide
  have hdescent : baseEnd_4949040 < baseStart_4949040 := by decide
  rcases family_descends (prefixWord ++ tailWord_4949040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4949048 : List Nat := [2, 1, 2, 1, 5, 3, 2, 1, 2, 1, 3]
def baseStart_4949048 : Nat := 118140960795 + 4949048 * 2 ^ 59
def prefixEnd_4949048 : Nat := 4983230072969 + 3 ^ 40 * 4949048 * 2
def baseEnd_4949048 : Nat := 2541240406172658060639749

theorem tailTrace_4949048 : CollatzResearch.WordTrace tailWord_4949048 prefixEnd_4949048 2541240406172658060639749 := by
  unfold tailWord_4949048
  simp only [CollatzResearch.WordTrace]
  refine ⟨90253304887225900475651899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120337739849634533967535865 90253304887225900475651899)
  ·
    refine ⟨135379957330838850713477849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90253304887225900475651899 135379957330838850713477849)
    ·
      refine ⟨101534967998129138035108387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 135379957330838850713477849 101534967998129138035108387)
      ·
        refine ⟨152302451997193707052662581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101534967998129138035108387 152302451997193707052662581)
        ·
          refine ⟨14278354874736910036187117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 152302451997193707052662581 14278354874736910036187117)
          ·
            refine ⟨5354383078026341263570169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14278354874736910036187117 5354383078026341263570169)
            ·
              refine ⟨4015787308519755947677627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5354383078026341263570169 4015787308519755947677627)
              ·
                refine ⟨6023680962779633921516441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4015787308519755947677627 6023680962779633921516441)
                ·
                  refine ⟨4517760722084725441137331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6023680962779633921516441 4517760722084725441137331)
                  ·
                    refine ⟨6776641083127088161705997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4517760722084725441137331 6776641083127088161705997)
                    ·
                      refine ⟨2541240406172658060639749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6776641083127088161705997 2541240406172658060639749)
                      ·
                        rfl

theorem cell23_4949048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 3, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 3, 2, 1, 2, 1, 3].length) (baseStart_4949048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4949048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4949048 prefixEnd_4949048 := by exact prefixLift 4949048
  have htrace : WordTrace (prefixWord ++ tailWord_4949048) baseStart_4949048 baseEnd_4949048 := by
    simpa [prefixWord, tailWord_4949048, baseEnd_4949048] using wordTrace_append hprefix tailTrace_4949048
  have hstable : (prefixWord ++ tailWord_4949048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4949048).length < 2 ^ (prefixWord ++ tailWord_4949048).sum := by decide
  have hdescent : baseEnd_4949048 < baseStart_4949048 := by decide
  rcases family_descends (prefixWord ++ tailWord_4949048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4949087 : List Nat := [1, 1, 2, 3, 1, 1, 4, 2, 2, 3, 3]
def baseStart_4949087 : Nat := 118140960795 + 4949087 * 2 ^ 59
def prefixEnd_4949087 : Nat := 4983230072969 + 3 ^ 40 * 4949087 * 2
def baseEnd_4949087 : Nat := 2541260431918183408052069

theorem tailTrace_4949087 : CollatzResearch.WordTrace tailWord_4949087 prefixEnd_4949087 2541260431918183408052069 := by
  unfold tailWord_4949087
  simp only [CollatzResearch.WordTrace]
  refine ⟨180508032221310510611973515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120338688147540340407982343 180508032221310510611973515)
  ·
    refine ⟨270762048331965765917960273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 180508032221310510611973515 270762048331965765917960273)
    ·
      refine ⟨203071536248974324438470205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 270762048331965765917960273 203071536248974324438470205)
      ·
        refine ⟨76151826093365371664426327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 203071536248974324438470205 76151826093365371664426327)
        ·
          refine ⟨114227739140048057496639491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76151826093365371664426327 114227739140048057496639491)
          ·
            refine ⟨171341608710072086244959237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 114227739140048057496639491 171341608710072086244959237)
            ·
              refine ⟨32126551633138516170929857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 171341608710072086244959237 32126551633138516170929857)
              ·
                refine ⟨24094913724853887128197393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32126551633138516170929857 24094913724853887128197393)
                ·
                  refine ⟨18071185293640415346148045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24094913724853887128197393 18071185293640415346148045)
                  ·
                    refine ⟨6776694485115155754805517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18071185293640415346148045 6776694485115155754805517)
                    ·
                      refine ⟨2541260431918183408052069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6776694485115155754805517 2541260431918183408052069)
                      ·
                        rfl

theorem cell23_4949087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 4, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 4, 2, 2, 3, 3].length) (baseStart_4949087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4949087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4949087 prefixEnd_4949087 := by exact prefixLift 4949087
  have htrace : WordTrace (prefixWord ++ tailWord_4949087) baseStart_4949087 baseEnd_4949087 := by
    simpa [prefixWord, tailWord_4949087, baseEnd_4949087] using wordTrace_append hprefix tailTrace_4949087
  have hstable : (prefixWord ++ tailWord_4949087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4949087).length < 2 ^ (prefixWord ++ tailWord_4949087).sum := by decide
  have hdescent : baseEnd_4949087 < baseStart_4949087 := by decide
  rcases family_descends (prefixWord ++ tailWord_4949087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4949124 : List Nat := [2, 3, 2, 1, 2, 2, 3, 1, 2, 5]
def baseStart_4949124 : Nat := 118140960795 + 4949124 * 2 ^ 59
def prefixEnd_4949124 : Nat := 4983230072969 + 3 ^ 40 * 4949124 * 2
def baseEnd_4949124 : Nat := 847093143567466587763133

theorem tailTrace_4949124 : CollatzResearch.WordTrace tailWord_4949124 prefixEnd_4949124 847093143567466587763133 := by
  unfold tailWord_4949124
  simp only [CollatzResearch.WordTrace]
  refine ⟨90254690861088232965535213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120339587814784310620713617 90254690861088232965535213)
  ·
    refine ⟨33845509072908087362075705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 90254690861088232965535213 33845509072908087362075705)
    ·
      refine ⟨25384131804681065521556779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33845509072908087362075705 25384131804681065521556779)
      ·
        refine ⟨38076197707021598282335169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25384131804681065521556779 38076197707021598282335169)
        ·
          refine ⟨28557148280266198711751377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38076197707021598282335169 28557148280266198711751377)
          ·
            refine ⟨21417861210199649033813533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28557148280266198711751377 21417861210199649033813533)
            ·
              refine ⟨8031697953824868387680075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21417861210199649033813533 8031697953824868387680075)
              ·
                refine ⟨12047546930737302581520113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8031697953824868387680075 12047546930737302581520113)
                ·
                  refine ⟨9035660198052976936140085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12047546930737302581520113 9035660198052976936140085)
                  ·
                    refine ⟨847093143567466587763133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9035660198052976936140085 847093143567466587763133)
                    ·
                      rfl

theorem cell23_4949124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 3, 1, 2, 5].length) (baseStart_4949124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4949124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4949124 prefixEnd_4949124 := by exact prefixLift 4949124
  have htrace : WordTrace (prefixWord ++ tailWord_4949124) baseStart_4949124 baseEnd_4949124 := by
    simpa [prefixWord, tailWord_4949124, baseEnd_4949124] using wordTrace_append hprefix tailTrace_4949124
  have hstable : (prefixWord ++ tailWord_4949124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4949124).length < 2 ^ (prefixWord ++ tailWord_4949124).sum := by decide
  have hdescent : baseEnd_4949124 < baseStart_4949124 := by decide
  rcases family_descends (prefixWord ++ tailWord_4949124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4949167 : List Nat := [1, 1, 2, 1, 2, 3, 2, 5, 6]
def baseStart_4949167 : Nat := 118140960795 + 4949167 * 2 ^ 59
def prefixEnd_4949167 : Nat := 4983230072969 + 3 ^ 40 * 4949167 * 2
def baseEnd_4949167 : Nat := 282366834485615899450189

theorem tailTrace_4949167 : CollatzResearch.WordTrace tailWord_4949167 prefixEnd_4949167 282366834485615899450189 := by
  unfold tailWord_4949167
  simp only [CollatzResearch.WordTrace]
  refine ⟨180510950061020684274885755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120340633374013789516590503 180510950061020684274885755)
  ·
    refine ⟨270766425091531026412328633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 180510950061020684274885755 270766425091531026412328633)
    ·
      refine ⟨203074818818648269809246475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 270766425091531026412328633 203074818818648269809246475)
      ·
        refine ⟨304612228227972404713869713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 203074818818648269809246475 304612228227972404713869713)
        ·
          refine ⟨228459171170979303535402285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 304612228227972404713869713 228459171170979303535402285)
          ·
            refine ⟨85672189189117238825775857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 228459171170979303535402285 85672189189117238825775857)
            ·
              refine ⟨64254141891837929119331893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 85672189189117238825775857 64254141891837929119331893)
              ·
                refine ⟨6023825802359805854937365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 64254141891837929119331893 6023825802359805854937365)
                ·
                  refine ⟨282366834485615899450189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6023825802359805854937365 282366834485615899450189)
                  ·
                    rfl

theorem cell23_4949167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 2, 5, 6].length) (baseStart_4949167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4949167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4949167 prefixEnd_4949167 := by exact prefixLift 4949167
  have htrace : WordTrace (prefixWord ++ tailWord_4949167) baseStart_4949167 baseEnd_4949167 := by
    simpa [prefixWord, tailWord_4949167, baseEnd_4949167] using wordTrace_append hprefix tailTrace_4949167
  have hstable : (prefixWord ++ tailWord_4949167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4949167).length < 2 ^ (prefixWord ++ tailWord_4949167).sum := by decide
  have hdescent : baseEnd_4949167 < baseStart_4949167 := by decide
  rcases family_descends (prefixWord ++ tailWord_4949167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4949205 : List Nat := [1, 3, 2, 4, 1, 2, 3, 2, 1, 4]
def baseStart_4949205 : Nat := 118140960795 + 4949205 * 2 ^ 59
def prefixEnd_4949205 : Nat := 4983230072969 + 3 ^ 40 * 4949205 * 2
def baseEnd_4949205 : Nat := 847107007545137982125509

theorem tailTrace_4949205 : CollatzResearch.WordTrace tailWord_4949205 prefixEnd_4949205 847107007545137982125509 := by
  unfold tailWord_4949205
  simp only [CollatzResearch.WordTrace]
  refine ⟨180512336034883016764769069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120341557356588677843179379 180512336034883016764769069)
  ·
    refine ⟨67692126013081131286788401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 180512336034883016764769069 67692126013081131286788401)
    ·
      refine ⟨50769094509810848465091301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67692126013081131286788401 50769094509810848465091301)
      ·
        refine ⟨9519205220589534087204619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 50769094509810848465091301 9519205220589534087204619)
        ·
          refine ⟨14278807830884301130806929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9519205220589534087204619 14278807830884301130806929)
          ·
            refine ⟨10709105873163225848105197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14278807830884301130806929 10709105873163225848105197)
            ·
              refine ⟨4015914702436209693039449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10709105873163225848105197 4015914702436209693039449)
              ·
                refine ⟨3011936026827157269779587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4015914702436209693039449 3011936026827157269779587)
                ·
                  refine ⟨4517904040240735904669381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3011936026827157269779587 4517904040240735904669381)
                  ·
                    refine ⟨847107007545137982125509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4517904040240735904669381 847107007545137982125509)
                    ·
                      rfl

theorem cell23_4949205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 2, 3, 2, 1, 4].length) (baseStart_4949205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4949205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4949205 prefixEnd_4949205 := by exact prefixLift 4949205
  have htrace : WordTrace (prefixWord ++ tailWord_4949205) baseStart_4949205 baseEnd_4949205 := by
    simpa [prefixWord, tailWord_4949205, baseEnd_4949205] using wordTrace_append hprefix tailTrace_4949205
  have hstable : (prefixWord ++ tailWord_4949205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4949205).length < 2 ^ (prefixWord ++ tailWord_4949205).sum := by decide
  have hdescent : baseEnd_4949205 < baseStart_4949205 := by decide
  rcases family_descends (prefixWord ++ tailWord_4949205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4949262 : List Nat := [4, 1, 1, 2, 1, 5, 2, 2, 1, 1, 3]
def baseStart_4949262 : Nat := 118140960795 + 4949262 * 2 ^ 59
def prefixEnd_4949262 : Nat := 4983230072969 + 3 ^ 40 * 4949262 * 2
def baseEnd_4949262 : Nat := 2541350291032720223363765

theorem tailTrace_4949262 : CollatzResearch.WordTrace tailWord_4949262 prefixEnd_4949262 2541350291032720223363765 := by
  unfold tailWord_4949262
  simp only [CollatzResearch.WordTrace]
  refine ⟨22564301874459564437449255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 120342943330451010333062693 22564301874459564437449255)
  ·
    refine ⟨33846452811689346656173883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22564301874459564437449255 33846452811689346656173883)
    ·
      refine ⟨50769679217534019984260825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33846452811689346656173883 50769679217534019984260825)
      ·
        refine ⟨38077259413150514988195619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50769679217534019984260825 38077259413150514988195619)
        ·
          refine ⟨57115889119725772482293429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38077259413150514988195619 57115889119725772482293429)
          ·
            refine ⟨5354614604974291170215009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 57115889119725772482293429 5354614604974291170215009)
            ·
              refine ⟨4015960953730718377661257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5354614604974291170215009 4015960953730718377661257)
              ·
                refine ⟨3011970715298038783245943, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4015960953730718377661257 3011970715298038783245943)
                ·
                  refine ⟨4517956072947058174868915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3011970715298038783245943 4517956072947058174868915)
                  ·
                    refine ⟨6776934109420587262303373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4517956072947058174868915 6776934109420587262303373)
                    ·
                      refine ⟨2541350291032720223363765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6776934109420587262303373 2541350291032720223363765)
                      ·
                        rfl

theorem cell23_4949262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 5, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 5, 2, 2, 1, 1, 3].length) (baseStart_4949262 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4949262 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4949262 prefixEnd_4949262 := by exact prefixLift 4949262
  have htrace : WordTrace (prefixWord ++ tailWord_4949262) baseStart_4949262 baseEnd_4949262 := by
    simpa [prefixWord, tailWord_4949262, baseEnd_4949262] using wordTrace_append hprefix tailTrace_4949262
  have hstable : (prefixWord ++ tailWord_4949262).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4949262).length < 2 ^ (prefixWord ++ tailWord_4949262).sum := by decide
  have hdescent : baseEnd_4949262 < baseStart_4949262 := by decide
  rcases family_descends (prefixWord ++ tailWord_4949262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4949274 : List Nat := [3, 1, 1, 3, 3, 1, 3, 8]
def baseStart_4949274 : Nat := 118140960795 + 4949274 * 2 ^ 59
def prefixEnd_4949274 : Nat := 4983230072969 + 3 ^ 40 * 4949274 * 2
def baseEnd_4949274 : Nat := 94124313066687932459767

theorem tailTrace_4949274 : CollatzResearch.WordTrace tailWord_4949274 prefixEnd_4949274 94124313066687932459767 := by
  unfold tailWord_4949274
  simp only [CollatzResearch.WordTrace]
  refine ⟨45128713167908260387257719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 120343235114422027699353917 45128713167908260387257719)
  ·
    refine ⟨67693069751862390580886579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45128713167908260387257719 67693069751862390580886579)
    ·
      refine ⟨101539604627793585871329869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67693069751862390580886579 101539604627793585871329869)
      ·
        refine ⟨38077351735422594701748701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 101539604627793585871329869 38077351735422594701748701)
        ·
          refine ⟨14279006900783473013155763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38077351735422594701748701 14279006900783473013155763)
          ·
            refine ⟨21418510351175209519733645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14279006900783473013155763 21418510351175209519733645)
            ·
              refine ⟨8031941381690703569900117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21418510351175209519733645 8031941381690703569900117)
              ·
                refine ⟨94124313066687932459767, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8031941381690703569900117 94124313066687932459767)
                ·
                  rfl

theorem cell23_4949274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 3, 8].length) (baseStart_4949274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4949274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4949274 prefixEnd_4949274 := by exact prefixLift 4949274
  have htrace : WordTrace (prefixWord ++ tailWord_4949274) baseStart_4949274 baseEnd_4949274 := by
    simpa [prefixWord, tailWord_4949274, baseEnd_4949274] using wordTrace_append hprefix tailTrace_4949274
  have hstable : (prefixWord ++ tailWord_4949274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4949274).length < 2 ^ (prefixWord ++ tailWord_4949274).sum := by decide
  have hdescent : baseEnd_4949274 < baseStart_4949274 := by decide
  rcases family_descends (prefixWord ++ tailWord_4949274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4949301 : List Nat := [1, 3, 3, 1, 2, 2, 2, 2, 1, 3, 3]
def baseStart_4949301 : Nat := 118140960795 + 4949301 * 2 ^ 59
def prefixEnd_4949301 : Nat := 4983230072969 + 3 ^ 40 * 4949301 * 2
def baseEnd_4949301 : Nat := 2541370316778245570776085

theorem tailTrace_4949301 : CollatzResearch.WordTrace tailWord_4949301 prefixEnd_4949301 2541370316778245570776085 := by
  unfold tailWord_4949301
  simp only [CollatzResearch.WordTrace]
  refine ⟨180515837442535225160263757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120343891628356816773509171 180515837442535225160263757)
  ·
    refine ⟨67693439040950709435098909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 180515837442535225160263757 67693439040950709435098909)
    ·
      refine ⟨25385039640356516038162091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 67693439040950709435098909 25385039640356516038162091)
      ·
        refine ⟨38077559460534774057243137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25385039640356516038162091 38077559460534774057243137)
        ·
          refine ⟨28558169595401080542932353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38077559460534774057243137 28558169595401080542932353)
          ·
            refine ⟨21418627196550810407199265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28558169595401080542932353 21418627196550810407199265)
            ·
              refine ⟨16063970397413107805399449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21418627196550810407199265 16063970397413107805399449)
              ·
                refine ⟨12047977798059830854049587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16063970397413107805399449 12047977798059830854049587)
                ·
                  refine ⟨18071966697089746281074381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12047977798059830854049587 18071966697089746281074381)
                  ·
                    refine ⟨6776987511408654855402893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18071966697089746281074381 6776987511408654855402893)
                    ·
                      refine ⟨2541370316778245570776085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6776987511408654855402893 2541370316778245570776085)
                      ·
                        rfl

theorem cell23_4949301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 2, 2, 1, 3, 3].length) (baseStart_4949301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4949301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4949301 prefixEnd_4949301 := by exact prefixLift 4949301
  have htrace : WordTrace (prefixWord ++ tailWord_4949301) baseStart_4949301 baseEnd_4949301 := by
    simpa [prefixWord, tailWord_4949301, baseEnd_4949301] using wordTrace_append hprefix tailTrace_4949301
  have hstable : (prefixWord ++ tailWord_4949301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4949301).length < 2 ^ (prefixWord ++ tailWord_4949301).sum := by decide
  have hdescent : baseEnd_4949301 < baseStart_4949301 := by decide
  rcases family_descends (prefixWord ++ tailWord_4949301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4949335 : List Nat := [1, 1, 3, 2, 3, 3, 3, 1, 2, 1, 3]
def baseStart_4949335 : Nat := 118140960795 + 4949335 * 2 ^ 59
def prefixEnd_4949335 : Nat := 4983230072969 + 3 ^ 40 * 4949335 * 2
def baseEnd_4949335 : Nat := 2541387775120498437750929

theorem tailTrace_4949335 : CollatzResearch.WordTrace tailWord_4949335 prefixEnd_4949335 2541387775120498437750929 := by
  unfold tailWord_4949335
  simp only [CollatzResearch.WordTrace]
  refine ⟨180517077524412048967001459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120344718349608032644667639 180517077524412048967001459)
  ·
    refine ⟨270775616286618073450502189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 180517077524412048967001459 270775616286618073450502189)
    ·
      refine ⟨101540856107481777543938321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 270775616286618073450502189 101540856107481777543938321)
      ·
        refine ⟨76155642080611333157953741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 101540856107481777543938321 76155642080611333157953741)
        ·
          refine ⟨28558365780229249934232653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 76155642080611333157953741 28558365780229249934232653)
          ·
            refine ⟨10709387167585968725337245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28558365780229249934232653 10709387167585968725337245)
            ·
              refine ⟨4016020187844738272001467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10709387167585968725337245 4016020187844738272001467)
              ·
                refine ⟨6024030281767107408002201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4016020187844738272001467 6024030281767107408002201)
                ·
                  refine ⟨4518022711325330556001651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6024030281767107408002201 4518022711325330556001651)
                  ·
                    refine ⟨6777034066987995834002477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4518022711325330556001651 6777034066987995834002477)
                    ·
                      refine ⟨2541387775120498437750929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6777034066987995834002477 2541387775120498437750929)
                      ·
                        rfl

theorem cell23_4949335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 3, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 3, 3, 1, 2, 1, 3].length) (baseStart_4949335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4949335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4949335 prefixEnd_4949335 := by exact prefixLift 4949335
  have htrace : WordTrace (prefixWord ++ tailWord_4949335) baseStart_4949335 baseEnd_4949335 := by
    simpa [prefixWord, tailWord_4949335, baseEnd_4949335] using wordTrace_append hprefix tailTrace_4949335
  have hstable : (prefixWord ++ tailWord_4949335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4949335).length < 2 ^ (prefixWord ++ tailWord_4949335).sum := by decide
  have hdescent : baseEnd_4949335 < baseStart_4949335 := by decide
  rcases family_descends (prefixWord ++ tailWord_4949335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4949381 : List Nat := [1, 3, 1, 1, 3, 1, 2, 6, 5]
def baseStart_4949381 : Nat := 118140960795 + 4949381 * 2 ^ 59
def prefixEnd_4949381 : Nat := 4983230072969 + 3 ^ 40 * 4949381 * 2
def baseEnd_4949381 : Nat := 282379043914511695308413

theorem tailTrace_4949381 : CollatzResearch.WordTrace tailWord_4949381 prefixEnd_4949381 282379043914511695308413 := by
  unfold tailWord_4949381
  simp only [CollatzResearch.WordTrace]
  refine ⟨180518755282245398823175997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120345836854830265882117331 180518755282245398823175997)
  ·
    refine ⟨67694533230842024558690999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 180518755282245398823175997 67694533230842024558690999)
    ·
      refine ⟨101541799846263036838036499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67694533230842024558690999 101541799846263036838036499)
      ·
        refine ⟨152312699769394555257054749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101541799846263036838036499 152312699769394555257054749)
        ·
          refine ⟨57117262413522958221395531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 152312699769394555257054749 57117262413522958221395531)
          ·
            refine ⟨85675893620284437332093297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57117262413522958221395531 85675893620284437332093297)
            ·
              refine ⟨64256920215213327999069973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 85675893620284437332093297 64256920215213327999069973)
              ·
                refine ⟨3012043135088124749956405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 64256920215213327999069973 3012043135088124749956405)
                ·
                  refine ⟨282379043914511695308413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3012043135088124749956405 282379043914511695308413)
                  ·
                    rfl

theorem cell23_4949381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 2, 6, 5].length) (baseStart_4949381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4949381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4949381 prefixEnd_4949381 := by exact prefixLift 4949381
  have htrace : WordTrace (prefixWord ++ tailWord_4949381) baseStart_4949381 baseEnd_4949381 := by
    simpa [prefixWord, tailWord_4949381, baseEnd_4949381] using wordTrace_append hprefix tailTrace_4949381
  have hstable : (prefixWord ++ tailWord_4949381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4949381).length < 2 ^ (prefixWord ++ tailWord_4949381).sum := by decide
  have hdescent : baseEnd_4949381 < baseStart_4949381 := by decide
  rcases family_descends (prefixWord ++ tailWord_4949381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4949411 : List Nat := [1, 1, 1, 4, 1, 3, 4, 1, 2, 5]
def baseStart_4949411 : Nat := 118140960795 + 4949411 * 2 ^ 59
def prefixEnd_4949411 : Nat := 4983230072969 + 3 ^ 40 * 4949411 * 2
def baseEnd_4949411 : Nat := 847142266550080046800193

theorem tailTrace_4949411 : CollatzResearch.WordTrace tailWord_4949411 prefixEnd_4949411 847142266550080046800193 := by
  unfold tailWord_4949411
  simp only [CollatzResearch.WordTrace]
  refine ⟨180519849472136713946768087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120346566314757809297845391 180519849472136713946768087)
  ·
    refine ⟨270779774208205070920152131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 180519849472136713946768087 270779774208205070920152131)
    ·
      refine ⟨406169661312307606380228197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 270779774208205070920152131 406169661312307606380228197)
      ·
        refine ⟨76156811496057676196292787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 406169661312307606380228197 76156811496057676196292787)
        ·
          refine ⟨114235217244086514294439181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76156811496057676196292787 114235217244086514294439181)
          ·
            refine ⟨42838206466532442860414693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 114235217244086514294439181 42838206466532442860414693)
            ·
              refine ⟨8032163712474833036327755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 42838206466532442860414693 8032163712474833036327755)
              ·
                refine ⟨12048245568712249554491633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8032163712474833036327755 12048245568712249554491633)
                ·
                  refine ⟨9036184176534187165868725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12048245568712249554491633 9036184176534187165868725)
                  ·
                    refine ⟨847142266550080046800193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9036184176534187165868725 847142266550080046800193)
                    ·
                      rfl

theorem cell23_4949411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 4, 1, 2, 5].length) (baseStart_4949411 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4949411 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4949411 prefixEnd_4949411 := by exact prefixLift 4949411
  have htrace : WordTrace (prefixWord ++ tailWord_4949411) baseStart_4949411 baseEnd_4949411 := by
    simpa [prefixWord, tailWord_4949411, baseEnd_4949411] using wordTrace_append hprefix tailTrace_4949411
  have hstable : (prefixWord ++ tailWord_4949411).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4949411).length < 2 ^ (prefixWord ++ tailWord_4949411).sum := by decide
  have hdescent : baseEnd_4949411 < baseStart_4949411 := by decide
  rcases family_descends (prefixWord ++ tailWord_4949411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4949431 : List Nat := [1, 1, 3, 1, 3, 2, 1, 4, 2, 1, 4]
def baseStart_4949431 : Nat := 118140960795 + 4949431 * 2 ^ 59
def prefixEnd_4949431 : Nat := 4983230072969 + 3 ^ 40 * 4949431 * 2
def baseEnd_4949431 : Nat := 2541437069263330062150487

theorem tailTrace_4949431 : CollatzResearch.WordTrace tailWord_4949431 prefixEnd_4949431 2541437069263330062150487 := by
  unfold tailWord_4949431
  simp only [CollatzResearch.WordTrace]
  refine ⟨180520578932064257362496147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120347052621376171574997431 180520578932064257362496147)
  ·
    refine ⟨270780868398096386043744221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 180520578932064257362496147 270780868398096386043744221)
    ·
      refine ⟨101542825649286144766404083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 270780868398096386043744221 101542825649286144766404083)
      ·
        refine ⟨152314238473929217149606125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101542825649286144766404083 152314238473929217149606125)
        ·
          refine ⟨57117839427723456431102297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 152314238473929217149606125 57117839427723456431102297)
          ·
            refine ⟨42838379570792592323326723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57117839427723456431102297 42838379570792592323326723)
            ·
              refine ⟨64257569356188888484990085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42838379570792592323326723 64257569356188888484990085)
              ·
                refine ⟨12048294254285416590935641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 64257569356188888484990085 12048294254285416590935641)
                ·
                  refine ⟨9036220690714062443201731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12048294254285416590935641 9036220690714062443201731)
                  ·
                    refine ⟨13554331036071093664802597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9036220690714062443201731 13554331036071093664802597)
                    ·
                      refine ⟨2541437069263330062150487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13554331036071093664802597 2541437069263330062150487)
                      ·
                        rfl

theorem cell23_4949431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 1, 4, 2, 1, 4].length) (baseStart_4949431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4949431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4949431 prefixEnd_4949431 := by exact prefixLift 4949431
  have htrace : WordTrace (prefixWord ++ tailWord_4949431) baseStart_4949431 baseEnd_4949431 := by
    simpa [prefixWord, tailWord_4949431, baseEnd_4949431] using wordTrace_append hprefix tailTrace_4949431
  have hstable : (prefixWord ++ tailWord_4949431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4949431).length < 2 ^ (prefixWord ++ tailWord_4949431).sum := by decide
  have hdescent : baseEnd_4949431 < baseStart_4949431 := by decide
  rcases family_descends (prefixWord ++ tailWord_4949431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4949448 : List Nat := [2, 1, 3, 1, 3, 1, 3, 1, 2, 4, 2]
def baseStart_4949448 : Nat := 118140960795 + 4949448 * 2 ^ 59
def prefixEnd_4949448 : Nat := 4983230072969 + 3 ^ 40 * 4949448 * 2
def baseEnd_4949448 : Nat := 2541445798434456495637909

theorem tailTrace_4949448 : CollatzResearch.WordTrace tailWord_4949448 prefixEnd_4949448 2541445798434456495637909 := by
  unfold tailWord_4949448
  simp only [CollatzResearch.WordTrace]
  refine ⟨90260599486501334632932499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120347465982001779510576665 90260599486501334632932499)
  ·
    refine ⟨135390899229752001949398749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90260599486501334632932499 135390899229752001949398749)
    ·
      refine ⟨50771587211157000731024531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 135390899229752001949398749 50771587211157000731024531)
      ·
        refine ⟨76157380816735501096536797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50771587211157000731024531 76157380816735501096536797)
        ·
          refine ⟨28559017806275812911201299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 76157380816735501096536797 28559017806275812911201299)
          ·
            refine ⟨42838526709413719366801949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28559017806275812911201299 42838526709413719366801949)
            ·
              refine ⟨16064447516030144762550731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 42838526709413719366801949 16064447516030144762550731)
              ·
                refine ⟨24096671274045217143826097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16064447516030144762550731 24096671274045217143826097)
                ·
                  refine ⟨18072503455533912857869573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24096671274045217143826097 18072503455533912857869573)
                  ·
                    refine ⟨3388594397912608660850545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18072503455533912857869573 3388594397912608660850545)
                    ·
                      refine ⟨2541445798434456495637909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3388594397912608660850545 2541445798434456495637909)
                      ·
                        rfl

theorem cell23_4949448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 3, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 3, 1, 2, 4, 2].length) (baseStart_4949448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4949448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4949448 prefixEnd_4949448 := by exact prefixLift 4949448
  have htrace : WordTrace (prefixWord ++ tailWord_4949448) baseStart_4949448 baseEnd_4949448 := by
    simpa [prefixWord, tailWord_4949448, baseEnd_4949448] using wordTrace_append hprefix tailTrace_4949448
  have hstable : (prefixWord ++ tailWord_4949448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4949448).length < 2 ^ (prefixWord ++ tailWord_4949448).sum := by decide
  have hdescent : baseEnd_4949448 < baseStart_4949448 := by decide
  rcases family_descends (prefixWord ++ tailWord_4949448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4949451 : List Nat := [1, 1, 1, 1, 3, 3, 2, 2, 4, 2, 3]
def baseStart_4949451 : Nat := 118140960795 + 4949451 * 2 ^ 59
def prefixEnd_4949451 : Nat := 4983230072969 + 3 ^ 40 * 4949451 * 2
def baseEnd_4949451 : Nat := 2541447338876419983900395

theorem tailTrace_4949451 : CollatzResearch.WordTrace tailWord_4949451 prefixEnd_4949451 2541447338876419983900395 := by
  unfold tailWord_4949451
  simp only [CollatzResearch.WordTrace]
  refine ⟨180521308391991800778224207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120347538927994533852149471 180521308391991800778224207)
  ·
    refine ⟨270781962587987701167336311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 180521308391991800778224207 270781962587987701167336311)
    ·
      refine ⟨406172943881981551751004467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 270781962587987701167336311 406172943881981551751004467)
      ·
        refine ⟨609259415822972327626506701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 406172943881981551751004467 609259415822972327626506701)
        ·
          refine ⟨228472280933614622859940013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 609259415822972327626506701 228472280933614622859940013)
          ·
            refine ⟨85677105350105483572477505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 228472280933614622859940013 85677105350105483572477505)
            ·
              refine ⟨64257829012579112679358129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 85677105350105483572477505 64257829012579112679358129)
              ·
                refine ⟨48193371759434334509518597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 64257829012579112679358129 48193371759434334509518597)
                ·
                  refine ⟨9036257204893937720534737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 48193371759434334509518597 9036257204893937720534737)
                  ·
                    refine ⟨6777192903670453290401053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9036257204893937720534737 6777192903670453290401053)
                    ·
                      refine ⟨2541447338876419983900395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6777192903670453290401053 2541447338876419983900395)
                      ·
                        rfl

theorem cell23_4949451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 2, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 2, 2, 4, 2, 3].length) (baseStart_4949451 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4949451 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4949451 prefixEnd_4949451 := by exact prefixLift 4949451
  have htrace : WordTrace (prefixWord ++ tailWord_4949451) baseStart_4949451 baseEnd_4949451 := by
    simpa [prefixWord, tailWord_4949451, baseEnd_4949451] using wordTrace_append hprefix tailTrace_4949451
  have hstable : (prefixWord ++ tailWord_4949451).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4949451).length < 2 ^ (prefixWord ++ tailWord_4949451).sum := by decide
  have hdescent : baseEnd_4949451 < baseStart_4949451 := by decide
  rcases family_descends (prefixWord ++ tailWord_4949451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4949475 : List Nat := [1, 1, 1, 6, 2, 1, 1, 5, 1, 4]
def baseStart_4949475 : Nat := 118140960795 + 4949475 * 2 ^ 59
def prefixEnd_4949475 : Nat := 4983230072969 + 3 ^ 40 * 4949475 * 2
def baseEnd_4949475 : Nat := 847153220804042630000095

theorem tailTrace_4949475 : CollatzResearch.WordTrace tailWord_4949475 prefixEnd_4949475 847153220804042630000095 := by
  unfold tailWord_4949475
  simp only [CollatzResearch.WordTrace]
  refine ⟨180522183743904852877097879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120348122495936568584731919 180522183743904852877097879)
  ·
    refine ⟨270783275615857279315646819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 180522183743904852877097879 270783275615857279315646819)
    ·
      refine ⟨406174913423785918973470229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 270783275615857279315646819 406174913423785918973470229)
      ·
        refine ⟨19039449066739964951881417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 406174913423785918973470229 19039449066739964951881417)
        ·
          refine ⟨14279586800054973713911063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19039449066739964951881417 14279586800054973713911063)
          ·
            refine ⟨21419380200082460570866595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14279586800054973713911063 21419380200082460570866595)
            ·
              refine ⟨32129070300123690856299893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21419380200082460570866595 32129070300123690856299893)
              ·
                refine ⟨3012100340636596017778115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 32129070300123690856299893 3012100340636596017778115)
                ·
                  refine ⟨4518150510954894026667173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3012100340636596017778115 4518150510954894026667173)
                  ·
                    refine ⟨847153220804042630000095, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4518150510954894026667173 847153220804042630000095)
                    ·
                      rfl

theorem cell23_4949475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 1, 5, 1, 4].length) (baseStart_4949475 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4949475 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4949475 prefixEnd_4949475 := by exact prefixLift 4949475
  have htrace : WordTrace (prefixWord ++ tailWord_4949475) baseStart_4949475 baseEnd_4949475 := by
    simpa [prefixWord, tailWord_4949475, baseEnd_4949475] using wordTrace_append hprefix tailTrace_4949475
  have hstable : (prefixWord ++ tailWord_4949475).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4949475).length < 2 ^ (prefixWord ++ tailWord_4949475).sum := by decide
  have hdescent : baseEnd_4949475 < baseStart_4949475 := by decide
  rcases family_descends (prefixWord ++ tailWord_4949475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4949488 : List Nat := [2, 1, 1, 1, 3, 6, 1, 2, 6]
def baseStart_4949488 : Nat := 118140960795 + 4949488 * 2 ^ 59
def prefixEnd_4949488 : Nat := 4983230072969 + 3 ^ 40 * 4949488 * 2
def baseEnd_4949488 : Nat := 282385148628959593237525

theorem tailTrace_4949488 : CollatzResearch.WordTrace tailWord_4949488 prefixEnd_4949488 282385148628959593237525 := by
  unfold tailWord_4949488
  simp only [CollatzResearch.WordTrace]
  refine ⟨90261328946428878048660559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120348438595238504064880745 90261328946428878048660559)
  ·
    refine ⟨135391993419643317072990839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90261328946428878048660559 135391993419643317072990839)
    ·
      refine ⟨203087990129464975609486259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 135391993419643317072990839 203087990129464975609486259)
      ·
        refine ⟨304631985194197463414229389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 203087990129464975609486259 304631985194197463414229389)
        ·
          refine ⟨114236994447824048780336021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 304631985194197463414229389 114236994447824048780336021)
          ·
            refine ⟨5354859114741752286578251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 114236994447824048780336021 5354859114741752286578251)
            ·
              refine ⟨8032288672112628429867377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5354859114741752286578251 8032288672112628429867377)
              ·
                refine ⟨6024216504084471322400533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8032288672112628429867377 6024216504084471322400533)
                ·
                  refine ⟨282385148628959593237525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6024216504084471322400533 282385148628959593237525)
                  ·
                    rfl

theorem cell23_4949488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 6, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 6, 1, 2, 6].length) (baseStart_4949488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4949488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4949488 prefixEnd_4949488 := by exact prefixLift 4949488
  have htrace : WordTrace (prefixWord ++ tailWord_4949488) baseStart_4949488 baseEnd_4949488 := by
    simpa [prefixWord, tailWord_4949488, baseEnd_4949488] using wordTrace_append hprefix tailTrace_4949488
  have hstable : (prefixWord ++ tailWord_4949488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4949488).length < 2 ^ (prefixWord ++ tailWord_4949488).sum := by decide
  have hdescent : baseEnd_4949488 < baseStart_4949488 := by decide
  rcases family_descends (prefixWord ++ tailWord_4949488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4949505 : List Nat := [1, 2, 4, 1, 4, 1, 3, 1, 6]
def baseStart_4949505 : Nat := 118140960795 + 4949505 * 2 ^ 59
def prefixEnd_4949505 : Nat := 4983230072969 + 3 ^ 40 * 4949505 * 2
def baseEnd_4949505 : Nat := 282386118536862530291683

theorem tailTrace_4949505 : CollatzResearch.WordTrace tailWord_4949505 prefixEnd_4949505 282386118536862530291683 := by
  unfold tailWord_4949505
  simp only [CollatzResearch.WordTrace]
  refine ⟨180523277933796168000689969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120348851955864112000459979 180523277933796168000689969)
  ·
    refine ⟨135392458450347126000517477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 180523277933796168000689969 135392458450347126000517477)
    ·
      refine ⟨25386085959440086125097027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 135392458450347126000517477 25386085959440086125097027)
      ·
        refine ⟨38079128939160129187645541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25386085959440086125097027 38079128939160129187645541)
        ·
          refine ⟨7139836676092524222683539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 38079128939160129187645541 7139836676092524222683539)
          ·
            refine ⟨10709755014138786334025309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7139836676092524222683539 10709755014138786334025309)
            ·
              refine ⟨4016158130302044875259491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10709755014138786334025309 4016158130302044875259491)
              ·
                refine ⟨6024237195453067312889237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4016158130302044875259491 6024237195453067312889237)
                ·
                  refine ⟨282386118536862530291683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6024237195453067312889237 282386118536862530291683)
                  ·
                    rfl

theorem cell23_4949505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 1, 3, 1, 6].length) (baseStart_4949505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4949505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4949505 prefixEnd_4949505 := by exact prefixLift 4949505
  have htrace : WordTrace (prefixWord ++ tailWord_4949505) baseStart_4949505 baseEnd_4949505 := by
    simpa [prefixWord, tailWord_4949505, baseEnd_4949505] using wordTrace_append hprefix tailTrace_4949505
  have hstable : (prefixWord ++ tailWord_4949505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4949505).length < 2 ^ (prefixWord ++ tailWord_4949505).sum := by decide
  have hdescent : baseEnd_4949505 < baseStart_4949505 := by decide
  rcases family_descends (prefixWord ++ tailWord_4949505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4949561 : List Nat := [1, 2, 1, 5, 1, 2, 1, 10]
def baseStart_4949561 : Nat := 118140960795 + 4949561 * 2 ^ 59
def prefixEnd_4949561 : Nat := 4983230072969 + 3 ^ 40 * 4949561 * 2
def baseEnd_4949561 : Nat := 94129771175867205686107

theorem tailTrace_4949561 : CollatzResearch.WordTrace tailWord_4949561 prefixEnd_4949561 94129771175867205686107 := by
  unfold tailWord_4949561
  simp only [CollatzResearch.WordTrace]
  refine ⟨180525320421593289564728537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120350213614395526376485691 180525320421593289564728537)
  ·
    refine ⟨135393990316194967173546403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 180525320421593289564728537 135393990316194967173546403)
    ·
      refine ⟨203090985474292450760319605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 135393990316194967173546403 203090985474292450760319605)
      ·
        refine ⟨19039779888214917258779963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 203090985474292450760319605 19039779888214917258779963)
        ·
          refine ⟨28559669832322375888169945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19039779888214917258779963 28559669832322375888169945)
          ·
            refine ⟨21419752374241781916127459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28559669832322375888169945 21419752374241781916127459)
            ·
              refine ⟨32129628561362672874191189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21419752374241781916127459 32129628561362672874191189)
              ·
                refine ⟨94129771175867205686107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 32129628561362672874191189 94129771175867205686107)
                ·
                  rfl

theorem cell23_4949561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 1, 10].length) (baseStart_4949561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4949561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4949561 prefixEnd_4949561 := by exact prefixLift 4949561
  have htrace : WordTrace (prefixWord ++ tailWord_4949561) baseStart_4949561 baseEnd_4949561 := by
    simpa [prefixWord, tailWord_4949561, baseEnd_4949561] using wordTrace_append hprefix tailTrace_4949561
  have hstable : (prefixWord ++ tailWord_4949561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4949561).length < 2 ^ (prefixWord ++ tailWord_4949561).sum := by decide
  have hdescent : baseEnd_4949561 < baseStart_4949561 := by decide
  rcases family_descends (prefixWord ++ tailWord_4949561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4949575 : List Nat := [1, 1, 4, 1, 5, 1, 1, 1, 3, 2, 3]
def baseStart_4949575 : Nat := 118140960795 + 4949575 * 2 ^ 59
def prefixEnd_4949575 : Nat := 4983230072969 + 3 ^ 40 * 4949575 * 2
def baseEnd_4949575 : Nat := 2541511010477577498749825

theorem tailTrace_4949575 : CollatzResearch.WordTrace tailWord_4949575 prefixEnd_4949575 2541511010477577498749825 := by
  unfold tailWord_4949575
  simp only [CollatzResearch.WordTrace]
  refine ⟨180525831043542569955738179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120350554029028379970492119 180525831043542569955738179)
  ·
    refine ⟨270788746565313854933607269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 180525831043542569955738179 270788746565313854933607269)
    ·
      refine ⟨50772889980996347800051363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 270788746565313854933607269 50772889980996347800051363)
      ·
        refine ⟨76159334971494521700077045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50772889980996347800051363 76159334971494521700077045)
        ·
          refine ⟨7139937653577611409382223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 76159334971494521700077045 7139937653577611409382223)
          ·
            refine ⟨10709906480366417114073335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7139937653577611409382223 10709906480366417114073335)
            ·
              refine ⟨16064859720549625671110003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10709906480366417114073335 16064859720549625671110003)
              ·
                refine ⟨24097289580824438506665005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16064859720549625671110003 24097289580824438506665005)
                ·
                  refine ⟨9036483592809164439999377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24097289580824438506665005 9036483592809164439999377)
                  ·
                    refine ⟨6777362694606873329999533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9036483592809164439999377 6777362694606873329999533)
                    ·
                      refine ⟨2541511010477577498749825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6777362694606873329999533 2541511010477577498749825)
                      ·
                        rfl

theorem cell23_4949575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 1, 1, 1, 3, 2, 3].length) (baseStart_4949575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4949575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4949575 prefixEnd_4949575 := by exact prefixLift 4949575
  have htrace : WordTrace (prefixWord ++ tailWord_4949575) baseStart_4949575 baseEnd_4949575 := by
    simpa [prefixWord, tailWord_4949575, baseEnd_4949575] using wordTrace_append hprefix tailTrace_4949575
  have hstable : (prefixWord ++ tailWord_4949575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4949575).length < 2 ^ (prefixWord ++ tailWord_4949575).sum := by decide
  have hdescent : baseEnd_4949575 < baseStart_4949575 := by decide
  rcases family_descends (prefixWord ++ tailWord_4949575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4949608 : List Nat := [2, 1, 4, 3, 1, 1, 1, 1, 2, 7]
def baseStart_4949608 : Nat := 118140960795 + 4949608 * 2 ^ 59
def prefixEnd_4949608 : Nat := 4983230072969 + 3 ^ 40 * 4949608 * 2
def baseEnd_4949608 : Nat := 847175985113058623212391

theorem tailTrace_4949608 : CollatzResearch.WordTrace tailWord_4949608 prefixEnd_4949608 847175985113058623212391 := by
  unfold tailWord_4949608
  simp only [CollatzResearch.WordTrace]
  refine ⟨90263517326211508295844739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120351356434948677727792985 90263517326211508295844739)
  ·
    refine ⟨135395275989317262443767109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90263517326211508295844739 135395275989317262443767109)
    ·
      refine ⟨25386614247996986708206333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 135395275989317262443767109 25386614247996986708206333)
      ·
        refine ⟨9519980342998870015577375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25386614247996986708206333 9519980342998870015577375)
        ·
          refine ⟨14279970514498305023366063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9519980342998870015577375 14279970514498305023366063)
          ·
            refine ⟨21419955771747457535049095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14279970514498305023366063 21419955771747457535049095)
            ·
              refine ⟨32129933657621186302573643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21419955771747457535049095 32129933657621186302573643)
              ·
                refine ⟨48194900486431779453860465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32129933657621186302573643 48194900486431779453860465)
                ·
                  refine ⟨36146175364823834590395349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 48194900486431779453860465 36146175364823834590395349)
                  ·
                    refine ⟨847175985113058623212391, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 36146175364823834590395349 847175985113058623212391)
                    ·
                      rfl

theorem cell23_4949608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 1, 1, 2, 7].length) (baseStart_4949608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4949608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4949608 prefixEnd_4949608 := by exact prefixLift 4949608
  have htrace : WordTrace (prefixWord ++ tailWord_4949608) baseStart_4949608 baseEnd_4949608 := by
    simpa [prefixWord, tailWord_4949608, baseEnd_4949608] using wordTrace_append hprefix tailTrace_4949608
  have hstable : (prefixWord ++ tailWord_4949608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4949608).length < 2 ^ (prefixWord ++ tailWord_4949608).sum := by decide
  have hdescent : baseEnd_4949608 < baseStart_4949608 := by decide
  rcases family_descends (prefixWord ++ tailWord_4949608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4949622 : List Nat := [5, 1, 1, 2, 2, 2, 2, 1, 1, 3, 3]
def baseStart_4949622 : Nat := 118140960795 + 4949622 * 2 ^ 59
def prefixEnd_4949622 : Nat := 4983230072969 + 3 ^ 40 * 4949622 * 2
def baseEnd_4949622 : Nat := 2541535144068338814862109

theorem tailTrace_4949622 : CollatzResearch.WordTrace tailWord_4949622 prefixEnd_4949622 2541535144068338814862109 := by
  unfold tailWord_4949622
  simp only [CollatzResearch.WordTrace]
  refine ⟨11282971579648268561418695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 120351696849581531321799413 11282971579648268561418695)
  ·
    refine ⟨16924457369472402842128043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11282971579648268561418695 16924457369472402842128043)
    ·
      refine ⟨25386686054208604263192065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16924457369472402842128043 25386686054208604263192065)
      ·
        refine ⟨19040014540656453197394049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25386686054208604263192065 19040014540656453197394049)
        ·
          refine ⟨14280010905492339898045537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19040014540656453197394049 14280010905492339898045537)
          ·
            refine ⟨10710008179119254923534153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14280010905492339898045537 10710008179119254923534153)
            ·
              refine ⟨8032506134339441192650615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10710008179119254923534153 8032506134339441192650615)
              ·
                refine ⟨12048759201509161788975923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8032506134339441192650615 12048759201509161788975923)
                ·
                  refine ⟨18073138802263742683463885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12048759201509161788975923 18073138802263742683463885)
                  ·
                    refine ⟨6777427050848903506298957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18073138802263742683463885 6777427050848903506298957)
                    ·
                      refine ⟨2541535144068338814862109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6777427050848903506298957 2541535144068338814862109)
                      ·
                        rfl

theorem cell23_4949622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 2, 2, 1, 1, 3, 3].length) (baseStart_4949622 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4949622 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4949622 prefixEnd_4949622 := by exact prefixLift 4949622
  have htrace : WordTrace (prefixWord ++ tailWord_4949622) baseStart_4949622 baseEnd_4949622 := by
    simpa [prefixWord, tailWord_4949622, baseEnd_4949622] using wordTrace_append hprefix tailTrace_4949622
  have hstable : (prefixWord ++ tailWord_4949622).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4949622).length < 2 ^ (prefixWord ++ tailWord_4949622).sum := by decide
  have hdescent : baseEnd_4949622 < baseStart_4949622 := by decide
  rcases family_descends (prefixWord ++ tailWord_4949622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4949668 : List Nat := [2, 3, 1, 2, 2, 2, 1, 3, 7]
def baseStart_4949668 : Nat := 118140960795 + 4949668 * 2 ^ 59
def prefixEnd_4949668 : Nat := 4983230072969 + 3 ^ 40 * 4949668 * 2
def baseEnd_4949668 : Nat := 282395418242049514987433

theorem tailTrace_4949668 : CollatzResearch.WordTrace tailWord_4949668 prefixEnd_4949668 282395418242049514987433 := by
  unfold tailWord_4949668
  simp only [CollatzResearch.WordTrace]
  refine ⟨90264611516102823419436829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120352815354803764559249105 90264611516102823419436829)
  ·
    refine ⟨33849229318538558782288811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 90264611516102823419436829 33849229318538558782288811)
    ·
      refine ⟨50773843977807838173433217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33849229318538558782288811 50773843977807838173433217)
      ·
        refine ⟨38080382983355878630074913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50773843977807838173433217 38080382983355878630074913)
        ·
          refine ⟨28560287237516908972556185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38080382983355878630074913 28560287237516908972556185)
          ·
            refine ⟨21420215428137681729417139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28560287237516908972556185 21420215428137681729417139)
            ·
              refine ⟨32130323142206522594125709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21420215428137681729417139 32130323142206522594125709)
              ·
                refine ⟨12048871178327445972797141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32130323142206522594125709 12048871178327445972797141)
                ·
                  refine ⟨282395418242049514987433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12048871178327445972797141 282395418242049514987433)
                  ·
                    rfl

theorem cell23_4949668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 1, 3, 7].length) (baseStart_4949668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4949668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4949668 prefixEnd_4949668 := by exact prefixLift 4949668
  have htrace : WordTrace (prefixWord ++ tailWord_4949668) baseStart_4949668 baseEnd_4949668 := by
    simpa [prefixWord, tailWord_4949668, baseEnd_4949668] using wordTrace_append hprefix tailTrace_4949668
  have hstable : (prefixWord ++ tailWord_4949668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4949668).length < 2 ^ (prefixWord ++ tailWord_4949668).sum := by decide
  have hdescent : baseEnd_4949668 < baseStart_4949668 := by decide
  rcases family_descends (prefixWord ++ tailWord_4949668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4949679 : List Nat := [1, 1, 2, 1, 2, 4, 5, 1, 2, 2, 2]
def baseStart_4949679 : Nat := 118140960795 + 4949679 * 2 ^ 59
def prefixEnd_4949679 : Nat := 4983230072969 + 3 ^ 40 * 4949679 * 2
def baseEnd_4949679 : Nat := 2541564412465645091849347

theorem tailTrace_4949679 : CollatzResearch.WordTrace tailWord_4949679 prefixEnd_4949679 2541564412465645091849347 := by
  unfold tailWord_4949679
  simp only [CollatzResearch.WordTrace]
  refine ⟨180529624235165795717524091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120353082823443863811682727 180529624235165795717524091)
  ·
    refine ⟨270794436352748693576286137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 180529624235165795717524091 270794436352748693576286137)
    ·
      refine ⟨203095827264561520182214603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 270794436352748693576286137 203095827264561520182214603)
      ·
        refine ⟨304643740896842280273321905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 203095827264561520182214603 304643740896842280273321905)
        ·
          refine ⟨228482805672631710204991429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 304643740896842280273321905 228482805672631710204991429)
          ·
            refine ⟨42840526063618445663435893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 228482805672631710204991429 42840526063618445663435893)
            ·
              refine ⟨4016299318464229280947115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 42840526063618445663435893 4016299318464229280947115)
              ·
                refine ⟨6024448977696343921420673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4016299318464229280947115 6024448977696343921420673)
                ·
                  refine ⟨4518336733272257941065505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6024448977696343921420673 4518336733272257941065505)
                  ·
                    refine ⟨3388752549954193455799129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4518336733272257941065505 3388752549954193455799129)
                    ·
                      refine ⟨2541564412465645091849347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3388752549954193455799129 2541564412465645091849347)
                      ·
                        rfl

theorem cell23_4949679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 5, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 5, 1, 2, 2, 2].length) (baseStart_4949679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4949679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4949679 prefixEnd_4949679 := by exact prefixLift 4949679
  have htrace : WordTrace (prefixWord ++ tailWord_4949679) baseStart_4949679 baseEnd_4949679 := by
    simpa [prefixWord, tailWord_4949679, baseEnd_4949679] using wordTrace_append hprefix tailTrace_4949679
  have hstable : (prefixWord ++ tailWord_4949679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4949679).length < 2 ^ (prefixWord ++ tailWord_4949679).sum := by decide
  have hdescent : baseEnd_4949679 < baseStart_4949679 := by decide
  rcases family_descends (prefixWord ++ tailWord_4949679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4949806 : List Nat := [4, 1, 3, 2, 2, 2, 1, 1, 2, 2, 3]
def baseStart_4949806 : Nat := 118140960795 + 4949806 * 2 ^ 59
def prefixEnd_4949806 : Nat := 4983230072969 + 3 ^ 40 * 4949806 * 2
def baseEnd_4949806 : Nat := 2541629624508766094961263

theorem tailTrace_4949806 : CollatzResearch.WordTrace tailWord_4949806 prefixEnd_4949806 2541629624508766094961263 := by
  unfold tailWord_4949806
  simp only [CollatzResearch.WordTrace]
  refine ⟨22566782038213212050924659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 120356170870470464271598181 22566782038213212050924659)
  ·
    refine ⟨33850173057319818076386989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22566782038213212050924659 33850173057319818076386989)
    ·
      refine ⟨12693814896494931778645121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33850173057319818076386989 12693814896494931778645121)
      ·
        refine ⟨9520361172371198833983841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12693814896494931778645121 9520361172371198833983841)
        ·
          refine ⟨7140270879278399125487881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9520361172371198833983841 7140270879278399125487881)
          ·
            refine ⟨5355203159458799344115911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7140270879278399125487881 5355203159458799344115911)
            ·
              refine ⟨8032804739188199016173867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5355203159458799344115911 8032804739188199016173867)
              ·
                refine ⟨12049207108782298524260801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8032804739188199016173867 12049207108782298524260801)
                ·
                  refine ⟨9036905331586723893195601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12049207108782298524260801 9036905331586723893195601)
                  ·
                    refine ⟨6777678998690042919896701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9036905331586723893195601 6777678998690042919896701)
                    ·
                      refine ⟨2541629624508766094961263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6777678998690042919896701 2541629624508766094961263)
                      ·
                        rfl

theorem cell23_4949806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 2, 1, 1, 2, 2, 3].length) (baseStart_4949806 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4949806 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4949806 prefixEnd_4949806 := by exact prefixLift 4949806
  have htrace : WordTrace (prefixWord ++ tailWord_4949806) baseStart_4949806 baseEnd_4949806 := by
    simpa [prefixWord, tailWord_4949806, baseEnd_4949806] using wordTrace_append hprefix tailTrace_4949806
  have hstable : (prefixWord ++ tailWord_4949806).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4949806).length < 2 ^ (prefixWord ++ tailWord_4949806).sum := by decide
  have hdescent : baseEnd_4949806 < baseStart_4949806 := by decide
  rcases family_descends (prefixWord ++ tailWord_4949806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4949845 : List Nat := [1, 3, 2, 2, 2, 2, 1, 1, 3, 1, 5]
def baseStart_4949845 : Nat := 118140960795 + 4949845 * 2 ^ 59
def prefixEnd_4949845 : Nat := 4983230072969 + 3 ^ 40 * 4949845 * 2
def baseEnd_4949845 : Nat := 2541649650254291442373583

theorem tailTrace_4949845 : CollatzResearch.WordTrace tailWord_4949845 prefixEnd_4949845 2541649650254291442373583 := by
  unfold tailWord_4949845
  simp only [CollatzResearch.WordTrace]
  refine ⟨180535678752564406068066989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120357119168376270712044659 180535678752564406068066989)
  ·
    refine ⟨67700879532211652275525121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 180535678752564406068066989 67700879532211652275525121)
    ·
      refine ⟨50775659649158739206643841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67700879532211652275525121 50775659649158739206643841)
      ·
        refine ⟨38081744736869054404982881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50775659649158739206643841 38081744736869054404982881)
        ·
          refine ⟨28561308552651790803737161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38081744736869054404982881 28561308552651790803737161)
          ·
            refine ⟨21420981414488843102802871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28561308552651790803737161 21420981414488843102802871)
            ·
              refine ⟨32131472121733264654204307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21420981414488843102802871 32131472121733264654204307)
              ·
                refine ⟨48197208182599896981306461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32131472121733264654204307 48197208182599896981306461)
                ·
                  refine ⟨18073953068474961367989923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 48197208182599896981306461 18073953068474961367989923)
                  ·
                    refine ⟨27110929602712442051984885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18073953068474961367989923 27110929602712442051984885)
                    ·
                      refine ⟨2541649650254291442373583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27110929602712442051984885 2541649650254291442373583)
                      ·
                        rfl

theorem cell23_4949845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 1, 1, 3, 1, 5].length) (baseStart_4949845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4949845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4949845 prefixEnd_4949845 := by exact prefixLift 4949845
  have htrace : WordTrace (prefixWord ++ tailWord_4949845) baseStart_4949845 baseEnd_4949845 := by
    simpa [prefixWord, tailWord_4949845, baseEnd_4949845] using wordTrace_append hprefix tailTrace_4949845
  have hstable : (prefixWord ++ tailWord_4949845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4949845).length < 2 ^ (prefixWord ++ tailWord_4949845).sum := by decide
  have hdescent : baseEnd_4949845 < baseStart_4949845 := by decide
  rcases family_descends (prefixWord ++ tailWord_4949845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4949855 : List Nat := [1, 1, 2, 3, 1, 5, 1, 1, 1, 1, 6]
def baseStart_4949855 : Nat := 118140960795 + 4949855 * 2 ^ 59
def prefixEnd_4949855 : Nat := 4983230072969 + 3 ^ 40 * 4949855 * 2
def baseEnd_4949855 : Nat := 2541654785060836403248537

theorem tailTrace_4949855 : CollatzResearch.WordTrace tailWord_4949855 prefixEnd_4949855 2541654785060836403248537 := by
  unfold tailWord_4949855
  simp only [CollatzResearch.WordTrace]
  refine ⟨180536043482528177775931019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120357362321685451850620679 180536043482528177775931019)
  ·
    refine ⟨270804065223792266663896529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 180536043482528177775931019 270804065223792266663896529)
    ·
      refine ⟨203103048917844199997922397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 270804065223792266663896529 203103048917844199997922397)
      ·
        refine ⟨76163643344191574999220899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 203103048917844199997922397 76163643344191574999220899)
        ·
          refine ⟨114245465016287362498831349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76163643344191574999220899 114245465016287362498831349)
          ·
            refine ⟨10710512345276940234265439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 114245465016287362498831349 10710512345276940234265439)
            ·
              refine ⟨16065768517915410351398159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10710512345276940234265439 16065768517915410351398159)
              ·
                refine ⟨24098652776873115527097239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16065768517915410351398159 24098652776873115527097239)
                ·
                  refine ⟨36147979165309673290645859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24098652776873115527097239 36147979165309673290645859)
                  ·
                    refine ⟨54221968747964509935968789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 36147979165309673290645859 54221968747964509935968789)
                    ·
                      refine ⟨2541654785060836403248537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 54221968747964509935968789 2541654785060836403248537)
                      ·
                        rfl

theorem cell23_4949855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 5, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 5, 1, 1, 1, 1, 6].length) (baseStart_4949855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4949855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4949855 prefixEnd_4949855 := by exact prefixLift 4949855
  have htrace : WordTrace (prefixWord ++ tailWord_4949855) baseStart_4949855 baseEnd_4949855 := by
    simpa [prefixWord, tailWord_4949855, baseEnd_4949855] using wordTrace_append hprefix tailTrace_4949855
  have hstable : (prefixWord ++ tailWord_4949855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4949855).length < 2 ^ (prefixWord ++ tailWord_4949855).sum := by decide
  have hdescent : baseEnd_4949855 < baseStart_4949855 := by decide
  rcases family_descends (prefixWord ++ tailWord_4949855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4949859 : List Nat := [1, 1, 1, 5, 4, 1, 2, 2, 1, 1, 4]
def baseStart_4949859 : Nat := 118140960795 + 4949859 * 2 ^ 59
def prefixEnd_4949859 : Nat := 4983230072969 + 3 ^ 40 * 4949859 * 2
def baseEnd_4949859 : Nat := 2541656838983454387598519

theorem tailTrace_4949859 : CollatzResearch.WordTrace tailWord_4949859 prefixEnd_4949859 2541656838983454387598519 := by
  unfold tailWord_4949859
  simp only [CollatzResearch.WordTrace]
  refine ⟨180536189374513686459076631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120357459583009124306051087 180536189374513686459076631)
  ·
    refine ⟨270804284061770529688614947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 180536189374513686459076631 270804284061770529688614947)
    ·
      refine ⟨406206426092655794532922421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 270804284061770529688614947 406206426092655794532922421)
      ·
        refine ⟨38081852446186480737461477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 406206426092655794532922421 38081852446186480737461477)
        ·
          refine ⟨7140347333659965138274027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 38081852446186480737461477 7140347333659965138274027)
          ·
            refine ⟨10710521000489947707411041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7140347333659965138274027 10710521000489947707411041)
            ·
              refine ⟨8032890750367460780558281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10710521000489947707411041 8032890750367460780558281)
              ·
                refine ⟨6024668062775595585418711, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8032890750367460780558281 6024668062775595585418711)
                ·
                  refine ⟨9037002094163393378128067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6024668062775595585418711 9037002094163393378128067)
                  ·
                    refine ⟨13555503141245090067192101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9037002094163393378128067 13555503141245090067192101)
                    ·
                      refine ⟨2541656838983454387598519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13555503141245090067192101 2541656838983454387598519)
                      ·
                        rfl

theorem cell23_4949859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 1, 2, 2, 1, 1, 4].length) (baseStart_4949859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4949859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4949859 prefixEnd_4949859 := by exact prefixLift 4949859
  have htrace : WordTrace (prefixWord ++ tailWord_4949859) baseStart_4949859 baseEnd_4949859 := by
    simpa [prefixWord, tailWord_4949859, baseEnd_4949859] using wordTrace_append hprefix tailTrace_4949859
  have hstable : (prefixWord ++ tailWord_4949859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4949859).length < 2 ^ (prefixWord ++ tailWord_4949859).sum := by decide
  have hdescent : baseEnd_4949859 < baseStart_4949859 := by decide
  rcases family_descends (prefixWord ++ tailWord_4949859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4949875 : List Nat := [1, 1, 1, 2, 2, 1, 3, 3, 3, 3, 3]
def baseStart_4949875 : Nat := 118140960795 + 4949875 * 2 ^ 59
def prefixEnd_4949875 : Nat := 4983230072969 + 3 ^ 40 * 4949875 * 2
def baseEnd_4949875 : Nat := 2541665054673926324998445

theorem tailTrace_4949875 : CollatzResearch.WordTrace tailWord_4949875 prefixEnd_4949875 2541665054673926324998445 := by
  unfold tailWord_4949875
  simp only [CollatzResearch.WordTrace]
  refine ⟨180536772942455721191659079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120357848628303814127772719 180536772942455721191659079)
  ·
    refine ⟨270805159413683581787488619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 180536772942455721191659079 270805159413683581787488619)
    ·
      refine ⟨406207739120525372681232929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 270805159413683581787488619 406207739120525372681232929)
      ·
        refine ⟨304655804340394029510924697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 406207739120525372681232929 304655804340394029510924697)
        ·
          refine ⟨228491853255295522133193523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 304655804340394029510924697 228491853255295522133193523)
          ·
            refine ⟨342737779882943283199790285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 228491853255295522133193523 342737779882943283199790285)
            ·
              refine ⟨128526667456103731199921357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 342737779882943283199790285 128526667456103731199921357)
              ·
                refine ⟨48197500296038899199970509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 128526667456103731199921357 48197500296038899199970509)
                ·
                  refine ⟨18074062611014587199988941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 48197500296038899199970509 18074062611014587199988941)
                  ·
                    refine ⟨6777773479130470199995853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18074062611014587199988941 6777773479130470199995853)
                    ·
                      refine ⟨2541665054673926324998445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6777773479130470199995853 2541665054673926324998445)
                      ·
                        rfl

theorem cell23_4949875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 3, 3, 3, 3].length) (baseStart_4949875 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4949875 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4949875 prefixEnd_4949875 := by exact prefixLift 4949875
  have htrace : WordTrace (prefixWord ++ tailWord_4949875) baseStart_4949875 baseEnd_4949875 := by
    simpa [prefixWord, tailWord_4949875, baseEnd_4949875] using wordTrace_append hprefix tailTrace_4949875
  have hstable : (prefixWord ++ tailWord_4949875).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4949875).length < 2 ^ (prefixWord ++ tailWord_4949875).sum := by decide
  have hdescent : baseEnd_4949875 < baseStart_4949875 := by decide
  rcases family_descends (prefixWord ++ tailWord_4949875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4949893 : List Nat := [1, 3, 1, 1, 3, 2, 5, 2, 1, 2, 2]
def baseStart_4949893 : Nat := 118140960795 + 4949893 * 2 ^ 59
def prefixEnd_4949893 : Nat := 4983230072969 + 3 ^ 40 * 4949893 * 2
def baseEnd_4949893 : Nat := 2541674297325707254573363

theorem tailTrace_4949893 : CollatzResearch.WordTrace tailWord_4949893 prefixEnd_4949893 2541674297325707254573363 := by
  unfold tailWord_4949893
  simp only [CollatzResearch.WordTrace]
  refine ⟨180537429456390510265814333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120358286304260340177209555 180537429456390510265814333)
  ·
    refine ⟨67701536046146441349680375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 180537429456390510265814333 67701536046146441349680375)
    ·
      refine ⟨101552304069219662024520563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67701536046146441349680375 101552304069219662024520563)
      ·
        refine ⟨152328456103829493036780845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101552304069219662024520563 152328456103829493036780845)
        ·
          refine ⟨57123171038936059888792817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 152328456103829493036780845 57123171038936059888792817)
          ·
            refine ⟨42842378279202044916594613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57123171038936059888792817 42842378279202044916594613)
            ·
              refine ⟨4016472963675191710930745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 42842378279202044916594613 4016472963675191710930745)
              ·
                refine ⟨3012354722756393783198059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4016472963675191710930745 3012354722756393783198059)
                ·
                  refine ⟨4518532084134590674797089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3012354722756393783198059 4518532084134590674797089)
                  ·
                    refine ⟨3388899063100943006097817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4518532084134590674797089 3388899063100943006097817)
                    ·
                      refine ⟨2541674297325707254573363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3388899063100943006097817 2541674297325707254573363)
                      ·
                        rfl

theorem cell23_4949893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 5, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 5, 2, 1, 2, 2].length) (baseStart_4949893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4949893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4949893 prefixEnd_4949893 := by exact prefixLift 4949893
  have htrace : WordTrace (prefixWord ++ tailWord_4949893) baseStart_4949893 baseEnd_4949893 := by
    simpa [prefixWord, tailWord_4949893, baseEnd_4949893] using wordTrace_append hprefix tailTrace_4949893
  have hstable : (prefixWord ++ tailWord_4949893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4949893).length < 2 ^ (prefixWord ++ tailWord_4949893).sum := by decide
  have hdescent : baseEnd_4949893 < baseStart_4949893 := by decide
  rcases family_descends (prefixWord ++ tailWord_4949893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4949909 : List Nat := [1, 3, 2, 1, 1, 3, 3, 3, 2, 1, 3]
def baseStart_4949909 : Nat := 118140960795 + 4949909 * 2 ^ 59
def prefixEnd_4949909 : Nat := 4983230072969 + 3 ^ 40 * 4949909 * 2
def baseEnd_4949909 : Nat := 2541682513016179191973289

theorem tailTrace_4949909 : CollatzResearch.WordTrace tailWord_4949909 prefixEnd_4949909 2541682513016179191973289 := by
  unfold tailWord_4949909
  simp only [CollatzResearch.WordTrace]
  refine ⟨180538013024332544998396781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120358675349555029998931187 180538013024332544998396781)
  ·
    refine ⟨67701754884124704374398793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 180538013024332544998396781 67701754884124704374398793)
    ·
      refine ⟨50776316163093528280799095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67701754884124704374398793 50776316163093528280799095)
      ·
        refine ⟨76164474244640292421198643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50776316163093528280799095 76164474244640292421198643)
        ·
          refine ⟨114246711366960438631797965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76164474244640292421198643 114246711366960438631797965)
          ·
            refine ⟨42842516762610164486924237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 114246711366960438631797965 42842516762610164486924237)
            ·
              refine ⟨16065943785978811682596589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 42842516762610164486924237 16065943785978811682596589)
              ·
                refine ⟨6024728919742054380973721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16065943785978811682596589 6024728919742054380973721)
                ·
                  refine ⟨4518546689806540785730291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6024728919742054380973721 4518546689806540785730291)
                  ·
                    refine ⟨6777820034709811178595437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4518546689806540785730291 6777820034709811178595437)
                    ·
                      refine ⟨2541682513016179191973289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6777820034709811178595437 2541682513016179191973289)
                      ·
                        rfl

theorem cell23_4949909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 3, 3, 2, 1, 3].length) (baseStart_4949909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4949909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4949909 prefixEnd_4949909 := by exact prefixLift 4949909
  have htrace : WordTrace (prefixWord ++ tailWord_4949909) baseStart_4949909 baseEnd_4949909 := by
    simpa [prefixWord, tailWord_4949909, baseEnd_4949909] using wordTrace_append hprefix tailTrace_4949909
  have hstable : (prefixWord ++ tailWord_4949909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4949909).length < 2 ^ (prefixWord ++ tailWord_4949909).sum := by decide
  have hdescent : baseEnd_4949909 < baseStart_4949909 := by decide
  rcases family_descends (prefixWord ++ tailWord_4949909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4949910 : List Nat := [5, 3, 1, 1, 2, 2, 1, 2, 1, 1, 4]
def baseStart_4949910 : Nat := 118140960795 + 4949910 * 2 ^ 59
def prefixEnd_4949910 : Nat := 4983230072969 + 3 ^ 40 * 4949910 * 2
def baseEnd_4949910 : Nat := 2541683026496833688060785

theorem tailTrace_4949910 : CollatzResearch.WordTrace tailWord_4949910 prefixEnd_4949910 2541683026496833688060785 := by
  unfold tailWord_4949910
  simp only [CollatzResearch.WordTrace]
  refine ⟨11283628093583057635573949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 120358699664885948112788789 11283628093583057635573949)
  ·
    refine ⟨4231360535093646613340231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11283628093583057635573949 4231360535093646613340231)
    ·
      refine ⟨6347040802640469920010347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4231360535093646613340231 6347040802640469920010347)
      ·
        refine ⟨9520561203960704880015521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6347040802640469920010347 9520561203960704880015521)
        ·
          refine ⟨7140420902970528660011641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9520561203960704880015521 7140420902970528660011641)
          ·
            refine ⟨5355315677227896495008731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7140420902970528660011641 5355315677227896495008731)
            ·
              refine ⟨8032973515841844742513097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5355315677227896495008731 8032973515841844742513097)
              ·
                refine ⟨6024730136881383556884823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8032973515841844742513097 6024730136881383556884823)
                ·
                  refine ⟨9037095205322075335327235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6024730136881383556884823 9037095205322075335327235)
                  ·
                    refine ⟨13555642807983113002990853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9037095205322075335327235 13555642807983113002990853)
                    ·
                      refine ⟨2541683026496833688060785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13555642807983113002990853 2541683026496833688060785)
                      ·
                        rfl

theorem cell23_4949910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 2, 1, 2, 1, 1, 4].length) (baseStart_4949910 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4949910 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4949910 prefixEnd_4949910 := by exact prefixLift 4949910
  have htrace : WordTrace (prefixWord ++ tailWord_4949910) baseStart_4949910 baseEnd_4949910 := by
    simpa [prefixWord, tailWord_4949910, baseEnd_4949910] using wordTrace_append hprefix tailTrace_4949910
  have hstable : (prefixWord ++ tailWord_4949910).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4949910).length < 2 ^ (prefixWord ++ tailWord_4949910).sum := by decide
  have hdescent : baseEnd_4949910 < baseStart_4949910 := by decide
  rcases family_descends (prefixWord ++ tailWord_4949910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4949935 : List Nat := [1, 1, 2, 1, 2, 2, 3, 3, 2, 1, 5]
def baseStart_4949935 : Nat := 118140960795 + 4949935 * 2 ^ 59
def prefixEnd_4949935 : Nat := 4983230072969 + 3 ^ 40 * 4949935 * 2
def baseEnd_4949935 : Nat := 2541695863513196090248169

theorem tailTrace_4949935 : CollatzResearch.WordTrace tailWord_4949935 prefixEnd_4949935 2541695863513196090248169 := by
  unfold tailWord_4949935
  simp only [CollatzResearch.WordTrace]
  refine ⟨180538961322238351438843259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120359307548158900959228839 180538961322238351438843259)
  ·
    refine ⟨270808441983357527158264889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 180538961322238351438843259 270808441983357527158264889)
    ·
      refine ⟨203106331487518145368698667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 270808441983357527158264889 203106331487518145368698667)
      ·
        refine ⟨304659497231277218053048001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 203106331487518145368698667 304659497231277218053048001)
        ·
          refine ⟨228494622923457913539786001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 304659497231277218053048001 228494622923457913539786001)
          ·
            refine ⟨171370967192593435154839501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 228494622923457913539786001 171370967192593435154839501)
            ·
              refine ⟨64264112697222538183064813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 171370967192593435154839501 64264112697222538183064813)
              ·
                refine ⟨24099042261458451818649305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 64264112697222538183064813 24099042261458451818649305)
                ·
                  refine ⟨18074281696093838863986979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24099042261458451818649305 18074281696093838863986979)
                  ·
                    refine ⟨27111422544140758295980469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18074281696093838863986979 27111422544140758295980469)
                    ·
                      refine ⟨2541695863513196090248169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27111422544140758295980469 2541695863513196090248169)
                      ·
                        rfl

theorem cell23_4949935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 3, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 3, 3, 2, 1, 5].length) (baseStart_4949935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4949935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4949935 prefixEnd_4949935 := by exact prefixLift 4949935
  have htrace : WordTrace (prefixWord ++ tailWord_4949935) baseStart_4949935 baseEnd_4949935 := by
    simpa [prefixWord, tailWord_4949935, baseEnd_4949935] using wordTrace_append hprefix tailTrace_4949935
  have hstable : (prefixWord ++ tailWord_4949935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4949935).length < 2 ^ (prefixWord ++ tailWord_4949935).sum := by decide
  have hdescent : baseEnd_4949935 < baseStart_4949935 := by decide
  rcases family_descends (prefixWord ++ tailWord_4949935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4949966 : List Nat := [4, 1, 1, 1, 2, 2, 1, 5, 2, 2, 2]
def baseStart_4949966 : Nat := 118140960795 + 4949966 * 2 ^ 59
def prefixEnd_4949966 : Nat := 4983230072969 + 3 ^ 40 * 4949966 * 2
def baseEnd_4949966 : Nat := 2541711781413485468960527

theorem tailTrace_4949966 : CollatzResearch.WordTrace tailWord_4949966 prefixEnd_4949966 2541711781413485468960527 := by
  unfold tailWord_4949966
  simp only [CollatzResearch.WordTrace]
  refine ⟨22567511498140755466652719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 120360061323417362488814501 22567511498140755466652719)
  ·
    refine ⟨33851267247211133199979079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22567511498140755466652719 33851267247211133199979079)
    ·
      refine ⟨50776900870816699799968619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33851267247211133199979079 50776900870816699799968619)
      ·
        refine ⟨76165351306225049699952929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50776900870816699799968619 76165351306225049699952929)
        ·
          refine ⟨57124013479668787274964697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 76165351306225049699952929 57124013479668787274964697)
          ·
            refine ⟨42843010109751590456223523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57124013479668787274964697 42843010109751590456223523)
            ·
              refine ⟨64264515164627385684335285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42843010109751590456223523 64264515164627385684335285)
              ·
                refine ⟨6024798296683817407906433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 64264515164627385684335285 6024798296683817407906433)
                ·
                  refine ⟨4518598722512863055929825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6024798296683817407906433 4518598722512863055929825)
                  ·
                    refine ⟨3388949041884647291947369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4518598722512863055929825 3388949041884647291947369)
                    ·
                      refine ⟨2541711781413485468960527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3388949041884647291947369 2541711781413485468960527)
                      ·
                        rfl

theorem cell23_4949966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 1, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 1, 5, 2, 2, 2].length) (baseStart_4949966 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4949966 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4949966 prefixEnd_4949966 := by exact prefixLift 4949966
  have htrace : WordTrace (prefixWord ++ tailWord_4949966) baseStart_4949966 baseEnd_4949966 := by
    simpa [prefixWord, tailWord_4949966, baseEnd_4949966] using wordTrace_append hprefix tailTrace_4949966
  have hstable : (prefixWord ++ tailWord_4949966).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4949966).length < 2 ^ (prefixWord ++ tailWord_4949966).sum := by decide
  have hdescent : baseEnd_4949966 < baseStart_4949966 := by decide
  rcases family_descends (prefixWord ++ tailWord_4949966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4949972 : List Nat := [2, 4, 1, 2, 1, 1, 3, 2, 7]
def baseStart_4949972 : Nat := 118140960795 + 4949972 * 2 ^ 59
def prefixEnd_4949972 : Nat := 4983230072969 + 3 ^ 40 * 4949972 * 2
def baseEnd_4949972 : Nat := 282412762477490271720611

theorem tailTrace_4949972 : CollatzResearch.WordTrace tailWord_4949972 prefixEnd_4949972 282412762477490271720611 := by
  unfold tailWord_4949972
  simp only [CollatzResearch.WordTrace]
  refine ⟨90270155411552153378970085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120360207215402871171960113 90270155411552153378970085)
  ·
    refine ⟨16925654139666028758556891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 90270155411552153378970085 16925654139666028758556891)
    ·
      refine ⟨25388481209499043137835337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16925654139666028758556891 25388481209499043137835337)
      ·
        refine ⟨19041360907124282353376503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25388481209499043137835337 19041360907124282353376503)
        ·
          refine ⟨28562041360686423530064755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19041360907124282353376503 28562041360686423530064755)
          ·
            refine ⟨42843062041029635295097133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28562041360686423530064755 42843062041029635295097133)
            ·
              refine ⟨16066148265386113235661425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 42843062041029635295097133 16066148265386113235661425)
              ·
                refine ⟨12049611199039584926746069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16066148265386113235661425 12049611199039584926746069)
                ·
                  refine ⟨282412762477490271720611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12049611199039584926746069 282412762477490271720611)
                  ·
                    rfl

theorem cell23_4949972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 3, 2, 7].length) (baseStart_4949972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4949972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4949972 prefixEnd_4949972 := by exact prefixLift 4949972
  have htrace : WordTrace (prefixWord ++ tailWord_4949972) baseStart_4949972 baseEnd_4949972 := by
    simpa [prefixWord, tailWord_4949972, baseEnd_4949972] using wordTrace_append hprefix tailTrace_4949972
  have hstable : (prefixWord ++ tailWord_4949972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4949972).length < 2 ^ (prefixWord ++ tailWord_4949972).sum := by decide
  have hdescent : baseEnd_4949972 < baseStart_4949972 := by decide
  rcases family_descends (prefixWord ++ tailWord_4949972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4949995 : List Nat := [1, 1, 1, 1, 2, 3, 1, 3, 3, 2, 5]
def baseStart_4949995 : Nat := 118140960795 + 4949995 * 2 ^ 59
def prefixEnd_4949995 : Nat := 4983230072969 + 3 ^ 40 * 4949995 * 2
def baseEnd_4949995 : Nat := 2541726672352465855497893

theorem tailTrace_4949995 : CollatzResearch.WordTrace tailWord_4949995 prefixEnd_4949995 2541726672352465855497893 := by
  unfold tailWord_4949995
  simp only [CollatzResearch.WordTrace]
  refine ⟨180541149702020981686027439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120360766468013987790684959 180541149702020981686027439)
  ·
    refine ⟨270811724553031472529041159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 180541149702020981686027439 270811724553031472529041159)
    ·
      refine ⟨406217586829547208793561739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 270811724553031472529041159 406217586829547208793561739)
      ·
        refine ⟨609326380244320813190342609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 406217586829547208793561739 609326380244320813190342609)
        ·
          refine ⟨456994785183240609892756957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 609326380244320813190342609 456994785183240609892756957)
          ·
            refine ⟨171373044443715228709783859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 456994785183240609892756957 171373044443715228709783859)
            ·
              refine ⟨257059566665572843064675789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 171373044443715228709783859 257059566665572843064675789)
              ·
                refine ⟨96397337499589816149253421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 257059566665572843064675789 96397337499589816149253421)
                ·
                  refine ⟨36149001562346181055970033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 96397337499589816149253421 36149001562346181055970033)
                  ·
                    refine ⟨27111751171759635791977525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 36149001562346181055970033 27111751171759635791977525)
                    ·
                      refine ⟨2541726672352465855497893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27111751171759635791977525 2541726672352465855497893)
                      ·
                        rfl

theorem cell23_4949995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 3, 3, 2, 5].length) (baseStart_4949995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4949995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4949995 prefixEnd_4949995 := by exact prefixLift 4949995
  have htrace : WordTrace (prefixWord ++ tailWord_4949995) baseStart_4949995 baseEnd_4949995 := by
    simpa [prefixWord, tailWord_4949995, baseEnd_4949995] using wordTrace_append hprefix tailTrace_4949995
  have hstable : (prefixWord ++ tailWord_4949995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4949995).length < 2 ^ (prefixWord ++ tailWord_4949995).sum := by decide
  have hdescent : baseEnd_4949995 < baseStart_4949995 := by decide
  rcases family_descends (prefixWord ++ tailWord_4949995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4950066 : List Nat := [3, 2, 1, 1, 2, 5, 1, 1, 3, 4]
def baseStart_4950066 : Nat := 118140960795 + 4950066 * 2 ^ 59
def prefixEnd_4950066 : Nat := 4983230072969 + 3 ^ 40 * 4950066 * 2
def baseEnd_4950066 : Nat := 847254376492978359236689

theorem tailTrace_4950066 : CollatzResearch.WordTrace tailWord_4950066 prefixEnd_4950066 847254376492978359236689 := by
  unfold tailWord_4950066
  simp only [CollatzResearch.WordTrace]
  refine ⟨45135934821190940202965513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 120362492856509173874574701 45135934821190940202965513)
  ·
    refine ⟨33851951115893205152224135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45135934821190940202965513 33851951115893205152224135)
    ·
      refine ⟨50777926673839807728336203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33851951115893205152224135 50777926673839807728336203)
      ·
        refine ⟨76166890010759711592504305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50777926673839807728336203 76166890010759711592504305)
        ·
          refine ⟨57125167508069783694378229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 76166890010759711592504305 57125167508069783694378229)
          ·
            refine ⟨5355484453881542221347959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 57125167508069783694378229 5355484453881542221347959)
            ·
              refine ⟨8033226680822313332021939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5355484453881542221347959 8033226680822313332021939)
              ·
                refine ⟨12049840021233469998032909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8033226680822313332021939 12049840021233469998032909)
                ·
                  refine ⟨4518690007962551249262341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12049840021233469998032909 4518690007962551249262341)
                  ·
                    refine ⟨847254376492978359236689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4518690007962551249262341 847254376492978359236689)
                    ·
                      rfl

theorem cell23_4950066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 5, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 5, 1, 1, 3, 4].length) (baseStart_4950066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4950066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4950066 prefixEnd_4950066 := by exact prefixLift 4950066
  have htrace : WordTrace (prefixWord ++ tailWord_4950066) baseStart_4950066 baseEnd_4950066 := by
    simpa [prefixWord, tailWord_4950066, baseEnd_4950066] using wordTrace_append hprefix tailTrace_4950066
  have hstable : (prefixWord ++ tailWord_4950066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4950066).length < 2 ^ (prefixWord ++ tailWord_4950066).sum := by decide
  have hdescent : baseEnd_4950066 < baseStart_4950066 := by decide
  rcases family_descends (prefixWord ++ tailWord_4950066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4950079 : List Nat := [1, 1, 2, 2, 3, 1, 6, 1, 6]
def baseStart_4950079 : Nat := 118140960795 + 4950079 * 2 ^ 59
def prefixEnd_4950079 : Nat := 4983230072969 + 3 ^ 40 * 4950079 * 2
def baseEnd_4950079 : Nat := 282418867191938169649723

theorem tailTrace_4950079 : CollatzResearch.WordTrace tailWord_4950079 prefixEnd_4950079 282418867191938169649723 := by
  unfold tailWord_4950079
  simp only [CollatzResearch.WordTrace]
  refine ⟨180544213433716664032085291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120362808955811109354723527 180544213433716664032085291)
  ·
    refine ⟨270816320150574996048127937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 180544213433716664032085291 270816320150574996048127937)
    ·
      refine ⟨203112240112931247036095953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 270816320150574996048127937 203112240112931247036095953)
      ·
        refine ⟨152334180084698435277071965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 203112240112931247036095953 152334180084698435277071965)
        ·
          refine ⟨57125317531761913228901987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 152334180084698435277071965 57125317531761913228901987)
          ·
            refine ⟨85687976297642869843352981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57125317531761913228901987 85687976297642869843352981)
            ·
              refine ⟨4016623888952009523907171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 85687976297642869843352981 4016623888952009523907171)
              ·
                refine ⟨6024935833428014285860757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4016623888952009523907171 6024935833428014285860757)
                ·
                  refine ⟨282418867191938169649723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6024935833428014285860757 282418867191938169649723)
                  ·
                    rfl

theorem cell23_4950079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 6, 1, 6].length) (baseStart_4950079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4950079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4950079 prefixEnd_4950079 := by exact prefixLift 4950079
  have htrace : WordTrace (prefixWord ++ tailWord_4950079) baseStart_4950079 baseEnd_4950079 := by
    simpa [prefixWord, tailWord_4950079, baseEnd_4950079] using wordTrace_append hprefix tailTrace_4950079
  have hstable : (prefixWord ++ tailWord_4950079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4950079).length < 2 ^ (prefixWord ++ tailWord_4950079).sum := by decide
  have hdescent : baseEnd_4950079 < baseStart_4950079 := by decide
  rcases family_descends (prefixWord ++ tailWord_4950079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4950089 : List Nat := [1, 2, 1, 1, 2, 2, 4, 1, 5, 1, 3]
def baseStart_4950089 : Nat := 118140960795 + 4950089 * 2 ^ 59
def prefixEnd_4950089 : Nat := 4983230072969 + 3 ^ 40 * 4950089 * 2
def baseEnd_4950089 : Nat := 2541774939533988487722461

theorem tailTrace_4950089 : CollatzResearch.WordTrace tailWord_4950089 prefixEnd_4950089 2541774939533988487722461 := by
  unfold tailWord_4950089
  simp only [CollatzResearch.WordTrace]
  refine ⟨180544578163680435739949321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120363052109120290493299547 180544578163680435739949321)
  ·
    refine ⟨135408433622760326804961991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 180544578163680435739949321 135408433622760326804961991)
    ·
      refine ⟨203112650434140490207442987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 135408433622760326804961991 203112650434140490207442987)
      ·
        refine ⟨304668975651210735311164481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 203112650434140490207442987 304668975651210735311164481)
        ·
          refine ⟨228501731738408051483373361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 304668975651210735311164481 228501731738408051483373361)
          ·
            refine ⟨171376298803806038612530021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 228501731738408051483373361 171376298803806038612530021)
            ·
              refine ⟨32133056025713632239849379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 171376298803806038612530021 32133056025713632239849379)
              ·
                refine ⟨48199584038570448359774069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32133056025713632239849379 48199584038570448359774069)
                ·
                  refine ⟨4518711003615979533728819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 48199584038570448359774069 4518711003615979533728819)
                  ·
                    refine ⟨6778066505423969300593229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4518711003615979533728819 6778066505423969300593229)
                    ·
                      refine ⟨2541774939533988487722461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6778066505423969300593229 2541774939533988487722461)
                      ·
                        rfl

theorem cell23_4950089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 4, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 4, 1, 5, 1, 3].length) (baseStart_4950089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4950089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4950089 prefixEnd_4950089 := by exact prefixLift 4950089
  have htrace : WordTrace (prefixWord ++ tailWord_4950089) baseStart_4950089 baseEnd_4950089 := by
    simpa [prefixWord, tailWord_4950089, baseEnd_4950089] using wordTrace_append hprefix tailTrace_4950089
  have hstable : (prefixWord ++ tailWord_4950089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4950089).length < 2 ^ (prefixWord ++ tailWord_4950089).sum := by decide
  have hdescent : baseEnd_4950089 < baseStart_4950089 := by decide
  rcases family_descends (prefixWord ++ tailWord_4950089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4950116 : List Nat := [2, 3, 1, 1, 2, 1, 4, 2, 2, 3, 2]
def baseStart_4950116 : Nat := 118140960795 + 4950116 * 2 ^ 59
def prefixEnd_4950116 : Nat := 4983230072969 + 3 ^ 40 * 4950116 * 2
def baseEnd_4950116 : Nat := 2541788803511659882084837

theorem tailTrace_4950116 : CollatzResearch.WordTrace tailWord_4950116 prefixEnd_4950116 2541788803511659882084837 := by
  unfold tailWord_4950116
  simp only [CollatzResearch.WordTrace]
  refine ⟨90272781467291309675591101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120363708623055079567454801 90272781467291309675591101)
  ·
    refine ⟨33852293050234241128346663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 90272781467291309675591101 33852293050234241128346663)
    ·
      refine ⟨50778439575351361692519995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33852293050234241128346663 50778439575351361692519995)
      ·
        refine ⟨76167659363027042538779993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50778439575351361692519995 76167659363027042538779993)
        ·
          refine ⟨57125744522270281904084995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 76167659363027042538779993 57125744522270281904084995)
          ·
            refine ⟨85688616783405422856127493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57125744522270281904084995 85688616783405422856127493)
            ·
              refine ⟨16066615646888516785523905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 85688616783405422856127493 16066615646888516785523905)
              ·
                refine ⟨12049961735166387589142929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16066615646888516785523905 12049961735166387589142929)
                ·
                  refine ⟨9037471301374790691857197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12049961735166387589142929 9037471301374790691857197)
                  ·
                    refine ⟨3389051738015546509446449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9037471301374790691857197 3389051738015546509446449)
                    ·
                      refine ⟨2541788803511659882084837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3389051738015546509446449 2541788803511659882084837)
                      ·
                        rfl

theorem cell23_4950116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 4, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 4, 2, 2, 3, 2].length) (baseStart_4950116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4950116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4950116 prefixEnd_4950116 := by exact prefixLift 4950116
  have htrace : WordTrace (prefixWord ++ tailWord_4950116) baseStart_4950116 baseEnd_4950116 := by
    simpa [prefixWord, tailWord_4950116, baseEnd_4950116] using wordTrace_append hprefix tailTrace_4950116
  have hstable : (prefixWord ++ tailWord_4950116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4950116).length < 2 ^ (prefixWord ++ tailWord_4950116).sum := by decide
  have hdescent : baseEnd_4950116 < baseStart_4950116 := by decide
  rcases family_descends (prefixWord ++ tailWord_4950116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4950173 : List Nat := [1, 4, 2, 1, 1, 5, 1, 2, 2, 4]
def baseStart_4950173 : Nat := 118140960795 + 4950173 * 2 ^ 59
def prefixEnd_4950173 : Nat := 4983230072969 + 3 ^ 40 * 4950173 * 2
def baseEnd_4950173 : Nat := 847272690636322053024025

theorem tailTrace_4950173 : CollatzResearch.WordTrace tailWord_4950173 prefixEnd_4950173 847272690636322053024025 := by
  unfold tailWord_4950173
  simp only [CollatzResearch.WordTrace]
  refine ⟨180547641895376118086007173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120365094596917412057338115 180547641895376118086007173)
  ·
    refine ⟨33852682855383022141126345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 180547641895376118086007173 33852682855383022141126345)
    ·
      refine ⟨25389512141537266605844759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33852682855383022141126345 25389512141537266605844759)
      ·
        refine ⟨38084268212305899908767139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25389512141537266605844759 38084268212305899908767139)
        ·
          refine ⟨57126402318458849863150709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38084268212305899908767139 57126402318458849863150709)
          ·
            refine ⟨5355600217355517174670379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 57126402318458849863150709 5355600217355517174670379)
            ·
              refine ⟨8033400326033275762005569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5355600217355517174670379 8033400326033275762005569)
              ·
                refine ⟨6025050244524956821504177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8033400326033275762005569 6025050244524956821504177)
                ·
                  refine ⟨4518787683393717616128133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6025050244524956821504177 4518787683393717616128133)
                  ·
                    refine ⟨847272690636322053024025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4518787683393717616128133 847272690636322053024025)
                    ·
                      rfl

theorem cell23_4950173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 5, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 5, 1, 2, 2, 4].length) (baseStart_4950173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4950173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4950173 prefixEnd_4950173 := by exact prefixLift 4950173
  have htrace : WordTrace (prefixWord ++ tailWord_4950173) baseStart_4950173 baseEnd_4950173 := by
    simpa [prefixWord, tailWord_4950173, baseEnd_4950173] using wordTrace_append hprefix tailTrace_4950173
  have hstable : (prefixWord ++ tailWord_4950173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4950173).length < 2 ^ (prefixWord ++ tailWord_4950173).sum := by decide
  have hdescent : baseEnd_4950173 < baseStart_4950173 := by decide
  rcases family_descends (prefixWord ++ tailWord_4950173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4950180 : List Nat := [2, 3, 1, 2, 4, 1, 2, 1, 3, 2, 2]
def baseStart_4950180 : Nat := 118140960795 + 4950180 * 2 ^ 59
def prefixEnd_4950180 : Nat := 4983230072969 + 3 ^ 40 * 4950180 * 2
def baseEnd_4950180 : Nat := 2541821666273547631684543

theorem tailTrace_4950180 : CollatzResearch.WordTrace tailWord_4950180 prefixEnd_4950180 2541821666273547631684543 := by
  unfold tailWord_4950180
  simp only [CollatzResearch.WordTrace]
  refine ⟨90273948603175379140755997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120365264804233838854341329 90273948603175379140755997)
  ·
    refine ⟨33852730726190767177783499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 90273948603175379140755997 33852730726190767177783499)
    ·
      refine ⟨50779096089286150766675249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33852730726190767177783499 50779096089286150766675249)
      ·
        refine ⟨38084322066964613075006437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50779096089286150766675249 38084322066964613075006437)
        ·
          refine ⟨7140810387555864951563707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 38084322066964613075006437 7140810387555864951563707)
          ·
            refine ⟨10711215581333797427345561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7140810387555864951563707 10711215581333797427345561)
            ·
              refine ⟨8033411686000348070509171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10711215581333797427345561 8033411686000348070509171)
              ·
                refine ⟨12050117529000522105763757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8033411686000348070509171 12050117529000522105763757)
                ·
                  refine ⟨4518794073375195789661409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12050117529000522105763757 4518794073375195789661409)
                  ·
                    refine ⟨3389095555031396842246057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4518794073375195789661409 3389095555031396842246057)
                    ·
                      refine ⟨2541821666273547631684543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3389095555031396842246057 2541821666273547631684543)
                      ·
                        rfl

theorem cell23_4950180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 1, 2, 1, 3, 2, 2].length) (baseStart_4950180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4950180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4950180 prefixEnd_4950180 := by exact prefixLift 4950180
  have htrace : WordTrace (prefixWord ++ tailWord_4950180) baseStart_4950180 baseEnd_4950180 := by
    simpa [prefixWord, tailWord_4950180, baseEnd_4950180] using wordTrace_append hprefix tailTrace_4950180
  have hstable : (prefixWord ++ tailWord_4950180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4950180).length < 2 ^ (prefixWord ++ tailWord_4950180).sum := by decide
  have hdescent : baseEnd_4950180 < baseStart_4950180 := by decide
  rcases family_descends (prefixWord ++ tailWord_4950180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4950190 : List Nat := [4, 1, 4, 2, 1, 2, 1, 1, 1, 6]
def baseStart_4950190 : Nat := 118140960795 + 4950190 * 2 ^ 59
def prefixEnd_4950190 : Nat := 4983230072969 + 3 ^ 40 * 4950190 * 2
def baseEnd_4950190 : Nat := 847275600360030864186499

theorem tailTrace_4950190 : CollatzResearch.WordTrace tailWord_4950190 prefixEnd_4950190 847275600360030864186499 := by
  unfold tailWord_4950190
  simp only [CollatzResearch.WordTrace]
  refine ⟨22568532742039316248672003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 120365507957543019992917349 22568532742039316248672003)
  ·
    refine ⟨33852799113058974373008005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22568532742039316248672003 33852799113058974373008005)
    ·
      refine ⟨6347399833698557694939001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 33852799113058974373008005 6347399833698557694939001)
      ·
        refine ⟨4760549875273918271204251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6347399833698557694939001 4760549875273918271204251)
        ·
          refine ⟨7140824812910877406806377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4760549875273918271204251 7140824812910877406806377)
          ·
            refine ⟨5355618609683158055104783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7140824812910877406806377 5355618609683158055104783)
            ·
              refine ⟨8033427914524737082657175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5355618609683158055104783 8033427914524737082657175)
              ·
                refine ⟨12050141871787105623985763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8033427914524737082657175 12050141871787105623985763)
                ·
                  refine ⟨18075212807680658435978645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12050141871787105623985763 18075212807680658435978645)
                  ·
                    refine ⟨847275600360030864186499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18075212807680658435978645 847275600360030864186499)
                    ·
                      rfl

theorem cell23_4950190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 2, 1, 1, 1, 6].length) (baseStart_4950190 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4950190 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4950190 prefixEnd_4950190 := by exact prefixLift 4950190
  have htrace : WordTrace (prefixWord ++ tailWord_4950190) baseStart_4950190 baseEnd_4950190 := by
    simpa [prefixWord, tailWord_4950190, baseEnd_4950190] using wordTrace_append hprefix tailTrace_4950190
  have hstable : (prefixWord ++ tailWord_4950190).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4950190).length < 2 ^ (prefixWord ++ tailWord_4950190).sum := by decide
  have hdescent : baseEnd_4950190 < baseStart_4950190 := by decide
  rcases family_descends (prefixWord ++ tailWord_4950190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4950192 : List Nat := [2, 1, 1, 1, 2, 1, 2, 1, 3, 4, 5]
def baseStart_4950192 : Nat := 118140960795 + 4950192 * 2 ^ 59
def prefixEnd_4950192 : Nat := 4983230072969 + 3 ^ 40 * 4950192 * 2
def baseEnd_4950192 : Nat := 2541827828041401584734487

theorem tailTrace_4950192 : CollatzResearch.WordTrace tailWord_4950192 prefixEnd_4950192 2541827828041401584734487 := by
  unfold tailWord_4950192
  simp only [CollatzResearch.WordTrace]
  refine ⟨90274167441153642165474415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120365556588204856220632553 90274167441153642165474415)
  ·
    refine ⟨135411251161730463248211623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90274167441153642165474415 135411251161730463248211623)
    ·
      refine ⟨203116876742595694872317435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 135411251161730463248211623 203116876742595694872317435)
      ·
        refine ⟨304675315113893542308476153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 203116876742595694872317435 304675315113893542308476153)
        ·
          refine ⟨228506486335420156731357115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 304675315113893542308476153 228506486335420156731357115)
          ·
            refine ⟨342759729503130235097035673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 228506486335420156731357115 342759729503130235097035673)
            ·
              refine ⟨257069797127347676322776755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 342759729503130235097035673 257069797127347676322776755)
              ·
                refine ⟨385604695691021514484165133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 257069797127347676322776755 385604695691021514484165133)
                ·
                  refine ⟨144601760884133067931561925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 385604695691021514484165133 144601760884133067931561925)
                  ·
                    refine ⟨27112830165774950237167861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 144601760884133067931561925 27112830165774950237167861)
                    ·
                      refine ⟨2541827828041401584734487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27112830165774950237167861 2541827828041401584734487)
                      ·
                        rfl

theorem cell23_4950192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 1, 3, 4, 5].length) (baseStart_4950192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4950192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4950192 prefixEnd_4950192 := by exact prefixLift 4950192
  have htrace : WordTrace (prefixWord ++ tailWord_4950192) baseStart_4950192 baseEnd_4950192 := by
    simpa [prefixWord, tailWord_4950192, baseEnd_4950192] using wordTrace_append hprefix tailTrace_4950192
  have hstable : (prefixWord ++ tailWord_4950192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4950192).length < 2 ^ (prefixWord ++ tailWord_4950192).sum := by decide
  have hdescent : baseEnd_4950192 < baseStart_4950192 := by decide
  rcases family_descends (prefixWord ++ tailWord_4950192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4950193 : List Nat := [1, 2, 2, 5, 2, 2, 1, 1, 1, 2, 4]
def baseStart_4950193 : Nat := 118140960795 + 4950193 * 2 ^ 59
def prefixEnd_4950193 : Nat := 4983230072969 + 3 ^ 40 * 4950193 * 2
def baseEnd_4950193 : Nat := 2541828341522056080821983

theorem tailTrace_4950193 : CollatzResearch.WordTrace tailWord_4950193 prefixEnd_4950193 2541828341522056080821983 := by
  unfold tailWord_4950193
  simp only [CollatzResearch.WordTrace]
  refine ⟨180548371355303661501735233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120365580903535774334490155 180548371355303661501735233)
  ·
    refine ⟨135411278516477746126301425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 180548371355303661501735233 135411278516477746126301425)
    ·
      refine ⟨101558458887358309594726069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 135411278516477746126301425 101558458887358309594726069)
      ·
        refine ⟨9521105520689841524505569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 101558458887358309594726069 9521105520689841524505569)
        ·
          refine ⟨7140829140517381143379177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9521105520689841524505569 7140829140517381143379177)
          ·
            refine ⟨5355621855388035857534383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7140829140517381143379177 5355621855388035857534383)
            ·
              refine ⟨8033432783082053786301575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5355621855388035857534383 8033432783082053786301575)
              ·
                refine ⟨12050149174623080679452363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8033432783082053786301575 12050149174623080679452363)
                ·
                  refine ⟨18075223761934621019178545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12050149174623080679452363 18075223761934621019178545)
                  ·
                    refine ⟨13556417821450965764383909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18075223761934621019178545 13556417821450965764383909)
                    ·
                      refine ⟨2541828341522056080821983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13556417821450965764383909 2541828341522056080821983)
                      ·
                        rfl

theorem cell23_4950193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 2, 1, 1, 1, 2, 4].length) (baseStart_4950193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4950193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4950193 prefixEnd_4950193 := by exact prefixLift 4950193
  have htrace : WordTrace (prefixWord ++ tailWord_4950193) baseStart_4950193 baseEnd_4950193 := by
    simpa [prefixWord, tailWord_4950193, baseEnd_4950193] using wordTrace_append hprefix tailTrace_4950193
  have hstable : (prefixWord ++ tailWord_4950193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4950193).length < 2 ^ (prefixWord ++ tailWord_4950193).sum := by decide
  have hdescent : baseEnd_4950193 < baseStart_4950193 := by decide
  rcases family_descends (prefixWord ++ tailWord_4950193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4950230 : List Nat := [5, 2, 1, 2, 1, 1, 2, 1, 4, 1, 3]
def baseStart_4950230 : Nat := 118140960795 + 4950230 * 2 ^ 59
def prefixEnd_4950230 : Nat := 4983230072969 + 3 ^ 40 * 4950230 * 2
def baseEnd_4950230 : Nat := 2541847340306272436059313

theorem tailTrace_4950230 : CollatzResearch.WordTrace tailWord_4950230 prefixEnd_4950230 2541847340306272436059313 := by
  unfold tailWord_4950230
  simp only [CollatzResearch.WordTrace]
  refine ⟨11284357553510601051302009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 120366480570779744547221429 11284357553510601051302009)
  ·
    refine ⟨8463268165132950788476507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11284357553510601051302009 8463268165132950788476507)
    ·
      refine ⟨12694902247699426182714761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8463268165132950788476507 12694902247699426182714761)
      ·
        refine ⟨9521176685774569637036071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12694902247699426182714761 9521176685774569637036071)
        ·
          refine ⟨14281765028661854455554107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9521176685774569637036071 14281765028661854455554107)
          ·
            refine ⟨21422647542992781683331161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14281765028661854455554107 21422647542992781683331161)
            ·
              refine ⟨16066985657244586262498371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21422647542992781683331161 16066985657244586262498371)
              ·
                refine ⟨24100478485866879393747557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16066985657244586262498371 24100478485866879393747557)
                ·
                  refine ⟨4518839716100039886327667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24100478485866879393747557 4518839716100039886327667)
                  ·
                    refine ⟨6778259574150059829491501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4518839716100039886327667 6778259574150059829491501)
                    ·
                      refine ⟨2541847340306272436059313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6778259574150059829491501 2541847340306272436059313)
                      ·
                        rfl

theorem cell23_4950230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 2, 1, 4, 1, 3].length) (baseStart_4950230 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4950230 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4950230 prefixEnd_4950230 := by exact prefixLift 4950230
  have htrace : WordTrace (prefixWord ++ tailWord_4950230) baseStart_4950230 baseEnd_4950230 := by
    simpa [prefixWord, tailWord_4950230, baseEnd_4950230] using wordTrace_append hprefix tailTrace_4950230
  have hstable : (prefixWord ++ tailWord_4950230).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4950230).length < 2 ^ (prefixWord ++ tailWord_4950230).sum := by decide
  have hdescent : baseEnd_4950230 < baseStart_4950230 := by decide
  rcases family_descends (prefixWord ++ tailWord_4950230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4950239 : List Nat := [1, 1, 2, 3, 2, 1, 1, 3, 2, 4, 3]
def baseStart_4950239 : Nat := 118140960795 + 4950239 * 2 ^ 59
def prefixEnd_4950239 : Nat := 4983230072969 + 3 ^ 40 * 4950239 * 2
def baseEnd_4950239 : Nat := 2541851961632162900846771

theorem tailTrace_4950239 : CollatzResearch.WordTrace tailWord_4950239 prefixEnd_4950239 2541851961632162900846771 := by
  unfold tailWord_4950239
  simp only [CollatzResearch.WordTrace]
  refine ⟨180550049113137011357909771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120366699408758007571939847 180550049113137011357909771)
  ·
    refine ⟨270825073669705517036864657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 180550049113137011357909771 270825073669705517036864657)
    ·
      refine ⟨203118805252279137777648493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 270825073669705517036864657 203118805252279137777648493)
      ·
        refine ⟨76169551969604676666618185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 203118805252279137777648493 76169551969604676666618185)
        ·
          refine ⟨57127163977203507499963639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 76169551969604676666618185 57127163977203507499963639)
          ·
            refine ⟨85690745965805261249945459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57127163977203507499963639 85690745965805261249945459)
            ·
              refine ⟨128536118948707891874918189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 85690745965805261249945459 128536118948707891874918189)
              ·
                refine ⟨48201044605765459453094321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 128536118948707891874918189 48201044605765459453094321)
                ·
                  refine ⟨36150783454324094589820741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 48201044605765459453094321 36150783454324094589820741)
                  ·
                    refine ⟨6778271897685767735591389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 36150783454324094589820741 6778271897685767735591389)
                    ·
                      refine ⟨2541851961632162900846771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6778271897685767735591389 2541851961632162900846771)
                      ·
                        rfl

theorem cell23_4950239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 3, 2, 4, 3].length) (baseStart_4950239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4950239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4950239 prefixEnd_4950239 := by exact prefixLift 4950239
  have htrace : WordTrace (prefixWord ++ tailWord_4950239) baseStart_4950239 baseEnd_4950239 := by
    simpa [prefixWord, tailWord_4950239, baseEnd_4950239] using wordTrace_append hprefix tailTrace_4950239
  have hstable : (prefixWord ++ tailWord_4950239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4950239).length < 2 ^ (prefixWord ++ tailWord_4950239).sum := by decide
  have hdescent : baseEnd_4950239 < baseStart_4950239 := by decide
  rcases family_descends (prefixWord ++ tailWord_4950239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4950247 : List Nat := [1, 1, 5, 3, 1, 3, 2, 1, 2, 1, 3]
def baseStart_4950247 : Nat := 118140960795 + 4950247 * 2 ^ 59
def prefixEnd_4950247 : Nat := 4983230072969 + 3 ^ 40 * 4950247 * 2
def baseEnd_4950247 : Nat := 2541856069477398869546735

theorem tailTrace_4950247 : CollatzResearch.WordTrace tailWord_4950247 prefixEnd_4950247 2541856069477398869546735 := by
  unfold tailWord_4950247
  simp only [CollatzResearch.WordTrace]
  refine ⟨180550340897108028724200995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120366893931405352482800663 180550340897108028724200995)
  ·
    refine ⟨270825511345662043086301493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 180550340897108028724200995 270825511345662043086301493)
    ·
      refine ⟨25389891688655816539340765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 270825511345662043086301493 25389891688655816539340765)
      ·
        refine ⟨9521209383245931202252787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25389891688655816539340765 9521209383245931202252787)
        ·
          refine ⟨14281814074868896803379181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9521209383245931202252787 14281814074868896803379181)
          ·
            refine ⟨5355680278075836301267193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14281814074868896803379181 5355680278075836301267193)
            ·
              refine ⟨4016760208556877225950395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5355680278075836301267193 4016760208556877225950395)
              ·
                refine ⟨6025140312835315838925593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4016760208556877225950395 6025140312835315838925593)
                ·
                  refine ⟨4518855234626486879194195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6025140312835315838925593 4518855234626486879194195)
                  ·
                    refine ⟨6778282851939730318791293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4518855234626486879194195 6778282851939730318791293)
                    ·
                      refine ⟨2541856069477398869546735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6778282851939730318791293 2541856069477398869546735)
                      ·
                        rfl

theorem cell23_4950247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 3, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 3, 2, 1, 2, 1, 3].length) (baseStart_4950247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4950247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4950247 prefixEnd_4950247 := by exact prefixLift 4950247
  have htrace : WordTrace (prefixWord ++ tailWord_4950247) baseStart_4950247 baseEnd_4950247 := by
    simpa [prefixWord, tailWord_4950247, baseEnd_4950247] using wordTrace_append hprefix tailTrace_4950247
  have hstable : (prefixWord ++ tailWord_4950247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4950247).length < 2 ^ (prefixWord ++ tailWord_4950247).sum := by decide
  have hdescent : baseEnd_4950247 < baseStart_4950247 := by decide
  rcases family_descends (prefixWord ++ tailWord_4950247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4950286 : List Nat := [4, 1, 1, 2, 1, 2, 2, 2, 2, 3, 3]
def baseStart_4950286 : Nat := 118140960795 + 4950286 * 2 ^ 59
def prefixEnd_4950286 : Nat := 4983230072969 + 3 ^ 40 * 4950286 * 2
def baseEnd_4950286 : Nat := 2541876095222924216959055

theorem tailTrace_4950286 : CollatzResearch.WordTrace tailWord_4950286 prefixEnd_4950286 2541876095222924216959055 := by
  unfold tailWord_4950286
  simp only [CollatzResearch.WordTrace]
  refine ⟨22568970417995842298108839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 120367842229311158923247141 22568970417995842298108839)
  ·
    refine ⟨33853455626993763447163259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22568970417995842298108839 33853455626993763447163259)
    ·
      refine ⟨50780183440490645170744889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33853455626993763447163259 50780183440490645170744889)
      ·
        refine ⟨38085137580367983878058667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50780183440490645170744889 38085137580367983878058667)
        ·
          refine ⟨57127706370551975817088001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38085137580367983878058667 57127706370551975817088001)
          ·
            refine ⟨42845779777913981862816001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57127706370551975817088001 42845779777913981862816001)
            ·
              refine ⟨32134334833435486397112001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42845779777913981862816001 32134334833435486397112001)
              ·
                refine ⟨24100751125076614797834001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32134334833435486397112001 24100751125076614797834001)
                ·
                  refine ⟨18075563343807461098375501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24100751125076614797834001 18075563343807461098375501)
                  ·
                    refine ⟨6778336253927797911890813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18075563343807461098375501 6778336253927797911890813)
                    ·
                      refine ⟨2541876095222924216959055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6778336253927797911890813 2541876095222924216959055)
                      ·
                        rfl

theorem cell23_4950286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 2, 2, 2, 3, 3].length) (baseStart_4950286 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4950286 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4950286 prefixEnd_4950286 := by exact prefixLift 4950286
  have htrace : WordTrace (prefixWord ++ tailWord_4950286) baseStart_4950286 baseEnd_4950286 := by
    simpa [prefixWord, tailWord_4950286, baseEnd_4950286] using wordTrace_append hprefix tailTrace_4950286
  have hstable : (prefixWord ++ tailWord_4950286).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4950286).length < 2 ^ (prefixWord ++ tailWord_4950286).sum := by decide
  have hdescent : baseEnd_4950286 < baseStart_4950286 := by decide
  rcases family_descends (prefixWord ++ tailWord_4950286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4950293 : List Nat := [1, 3, 2, 1, 2, 1, 6, 2, 5]
def baseStart_4950293 : Nat := 118140960795 + 4950293 * 2 ^ 59
def prefixEnd_4950293 : Nat := 4983230072969 + 3 ^ 40 * 4950293 * 2
def baseEnd_4950293 : Nat := 282431076620833965507947

theorem tailTrace_4950293 : CollatzResearch.WordTrace tailWord_4950293 prefixEnd_4950293 282431076620833965507947 := by
  unfold tailWord_4950293
  simp only [CollatzResearch.WordTrace]
  refine ⟨180552018654941378580375533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120368012436627585720250355 180552018654941378580375533)
  ·
    refine ⟨67707006995603016967640825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 180552018654941378580375533 67707006995603016967640825)
    ·
      refine ⟨50780255246702262725730619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67707006995603016967640825 50780255246702262725730619)
      ·
        refine ⟨76170382870053394088595929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50780255246702262725730619 76170382870053394088595929)
        ·
          refine ⟨57127787152540045566446947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 76170382870053394088595929 57127787152540045566446947)
          ·
            refine ⟨85691680728810068349670421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57127787152540045566446947 85691680728810068349670421)
            ·
              refine ⟨4016797534162971953890801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 85691680728810068349670421 4016797534162971953890801)
              ·
                refine ⟨3012598150622228965418101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4016797534162971953890801 3012598150622228965418101)
                ·
                  refine ⟨282431076620833965507947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3012598150622228965418101 282431076620833965507947)
                  ·
                    rfl

theorem cell23_4950293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 6, 2, 5].length) (baseStart_4950293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4950293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4950293 prefixEnd_4950293 := by exact prefixLift 4950293
  have htrace : WordTrace (prefixWord ++ tailWord_4950293) baseStart_4950293 baseEnd_4950293 := by
    simpa [prefixWord, tailWord_4950293, baseEnd_4950293] using wordTrace_append hprefix tailTrace_4950293
  have hstable : (prefixWord ++ tailWord_4950293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4950293).length < 2 ^ (prefixWord ++ tailWord_4950293).sum := by decide
  have hdescent : baseEnd_4950293 < baseStart_4950293 := by decide
  rcases family_descends (prefixWord ++ tailWord_4950293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4950296 : List Nat := [2, 1, 2, 3, 1, 2, 1, 1, 1, 7, 2]
def baseStart_4950296 : Nat := 118140960795 + 4950296 * 2 ^ 59
def prefixEnd_4950296 : Nat := 4983230072969 + 3 ^ 40 * 4950296 * 2
def baseEnd_4950296 : Nat := 2541881230029469177834009

theorem tailTrace_4950296 : CollatzResearch.WordTrace tailWord_4950296 prefixEnd_4950296 2541881230029469177834009 := by
  unfold tailWord_4950296
  simp only [CollatzResearch.WordTrace]
  refine ⟨90276064036965255046367371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120368085382620340061823161 90276064036965255046367371)
  ·
    refine ⟨135414096055447882569551057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90276064036965255046367371 135414096055447882569551057)
    ·
      refine ⟨101560572041585911927163293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 135414096055447882569551057 101560572041585911927163293)
      ·
        refine ⟨38085214515594716972686235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 101560572041585911927163293 38085214515594716972686235)
        ·
          refine ⟨57127821773392075459029353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38085214515594716972686235 57127821773392075459029353)
          ·
            refine ⟨42845866330044056594272015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57127821773392075459029353 42845866330044056594272015)
            ·
              refine ⟨64268799495066084891408023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42845866330044056594272015 64268799495066084891408023)
              ·
                refine ⟨96403199242599127337112035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 64268799495066084891408023 96403199242599127337112035)
                ·
                  refine ⟨144604798863898691005668053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 96403199242599127337112035 144604798863898691005668053)
                  ·
                    refine ⟨3389174973372625570445345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 144604798863898691005668053 3389174973372625570445345)
                    ·
                      refine ⟨2541881230029469177834009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3389174973372625570445345 2541881230029469177834009)
                      ·
                        rfl

theorem cell23_4950296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 1, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 1, 1, 1, 7, 2].length) (baseStart_4950296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4950296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4950296 prefixEnd_4950296 := by exact prefixLift 4950296
  have htrace : WordTrace (prefixWord ++ tailWord_4950296) baseStart_4950296 baseEnd_4950296 := by
    simpa [prefixWord, tailWord_4950296, baseEnd_4950296] using wordTrace_append hprefix tailTrace_4950296
  have hstable : (prefixWord ++ tailWord_4950296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4950296).length < 2 ^ (prefixWord ++ tailWord_4950296).sum := by decide
  have hdescent : baseEnd_4950296 < baseStart_4950296 := by decide
  rcases family_descends (prefixWord ++ tailWord_4950296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4950299 : List Nat := [1, 1, 1, 1, 1, 1, 8, 1, 1, 2, 5]
def baseStart_4950299 : Nat := 118140960795 + 4950299 * 2 ^ 59
def prefixEnd_4950299 : Nat := 4983230072969 + 3 ^ 40 * 4950299 * 2
def baseEnd_4950299 : Nat := 2541882770471432666096495

theorem tailTrace_4950299 : CollatzResearch.WordTrace tailWord_4950299 prefixEnd_4950299 2541882770471432666096495 := by
  unfold tailWord_4950299
  simp only [CollatzResearch.WordTrace]
  refine ⟨180552237492919641605093951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120368158328613094403395967 180552237492919641605093951)
  ·
    refine ⟨270828356239379462407640927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 180552237492919641605093951 270828356239379462407640927)
    ·
      refine ⟨406242534359069193611461391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 270828356239379462407640927 406242534359069193611461391)
      ·
        refine ⟨609363801538603790417192087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 406242534359069193611461391 609363801538603790417192087)
        ·
          refine ⟨914045702307905685625788131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 609363801538603790417192087 914045702307905685625788131)
          ·
            refine ⟨1371068553461858528438682197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 914045702307905685625788131 1371068553461858528438682197)
            ·
              refine ⟨16067209610881154630140807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1371068553461858528438682197 16067209610881154630140807)
              ·
                refine ⟨24100814416321731945211211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16067209610881154630140807 24100814416321731945211211)
                ·
                  refine ⟨36151221624482597917816817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24100814416321731945211211 36151221624482597917816817)
                  ·
                    refine ⟨27113416218361948438362613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 36151221624482597917816817 27113416218361948438362613)
                    ·
                      refine ⟨2541882770471432666096495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27113416218361948438362613 2541882770471432666096495)
                      ·
                        rfl

theorem cell23_4950299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 8, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 8, 1, 1, 2, 5].length) (baseStart_4950299 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4950299 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4950299 prefixEnd_4950299 := by exact prefixLift 4950299
  have htrace : WordTrace (prefixWord ++ tailWord_4950299) baseStart_4950299 baseEnd_4950299 := by
    simpa [prefixWord, tailWord_4950299, baseEnd_4950299] using wordTrace_append hprefix tailTrace_4950299
  have hstable : (prefixWord ++ tailWord_4950299).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4950299).length < 2 ^ (prefixWord ++ tailWord_4950299).sum := by decide
  have hdescent : baseEnd_4950299 < baseStart_4950299 := by decide
  rcases family_descends (prefixWord ++ tailWord_4950299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4950339 : List Nat := [1, 1, 1, 3, 1, 3, 3, 1, 2, 1, 6]
def baseStart_4950339 : Nat := 118140960795 + 4950339 * 2 ^ 59
def prefixEnd_4950339 : Nat := 4983230072969 + 3 ^ 40 * 4950339 * 2
def baseEnd_4950339 : Nat := 2541903309697612509596311

theorem tailTrace_4950339 : CollatzResearch.WordTrace tailWord_4950339 prefixEnd_4950339 2541903309697612509596311 := by
  unfold tailWord_4950339
  simp only [CollatzResearch.WordTrace]
  refine ⟨180553696412774728436550071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120369130941849818957700047 180553696412774728436550071)
  ·
    refine ⟨270830544619162092654825107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 180553696412774728436550071 270830544619162092654825107)
    ·
      refine ⟨406245816928743138982237661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 270830544619162092654825107 406245816928743138982237661)
      ·
        refine ⟨152342181348278677118339123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 406245816928743138982237661 152342181348278677118339123)
        ·
          refine ⟨228513272022418015677508685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 152342181348278677118339123 228513272022418015677508685)
          ·
            refine ⟨85692477008406755879065757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 228513272022418015677508685 85692477008406755879065757)
            ·
              refine ⟨32134678878152533454649659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 85692477008406755879065757 32134678878152533454649659)
              ·
                refine ⟨48202018317228800181974489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32134678878152533454649659 48202018317228800181974489)
                ·
                  refine ⟨36151513737921600136480867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 48202018317228800181974489 36151513737921600136480867)
                  ·
                    refine ⟨54227270606882400204721301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 36151513737921600136480867 54227270606882400204721301)
                    ·
                      refine ⟨2541903309697612509596311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 54227270606882400204721301 2541903309697612509596311)
                      ·
                        rfl

theorem cell23_4950339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 3, 1, 2, 1, 6].length) (baseStart_4950339 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4950339 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4950339 prefixEnd_4950339 := by exact prefixLift 4950339
  have htrace : WordTrace (prefixWord ++ tailWord_4950339) baseStart_4950339 baseEnd_4950339 := by
    simpa [prefixWord, tailWord_4950339, baseEnd_4950339] using wordTrace_append hprefix tailTrace_4950339
  have hstable : (prefixWord ++ tailWord_4950339).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4950339).length < 2 ^ (prefixWord ++ tailWord_4950339).sum := by decide
  have hdescent : baseEnd_4950339 < baseStart_4950339 := by decide
  rcases family_descends (prefixWord ++ tailWord_4950339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4950353 : List Nat := [1, 2, 2, 1, 4, 3, 2, 1, 3, 4]
def baseStart_4950353 : Nat := 118140960795 + 4950353 * 2 ^ 59
def prefixEnd_4950353 : Nat := 4983230072969 + 3 ^ 40 * 4950353 * 2
def baseEnd_4950353 : Nat := 847303499475591818273749

theorem tailTrace_4950353 : CollatzResearch.WordTrace tailWord_4950353 prefixEnd_4950353 847303499475591818273749 := by
  unfold tailWord_4950353
  simp only [CollatzResearch.WordTrace]
  refine ⟨180554207034724008827559713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120369471356482672551706475 180554207034724008827559713)
  ·
    refine ⟨135415655276043006620669785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 180554207034724008827559713 135415655276043006620669785)
    ·
      refine ⟨101561741457032254965502339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 135415655276043006620669785 101561741457032254965502339)
      ·
        refine ⟨152342612185548382448253509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101561741457032254965502339 152342612185548382448253509)
        ·
          refine ⟨28564239784790321709047533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 152342612185548382448253509 28564239784790321709047533)
          ·
            refine ⟨10711589919296370640892825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28564239784790321709047533 10711589919296370640892825)
            ·
              refine ⟨8033692439472277980669619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10711589919296370640892825 8033692439472277980669619)
              ·
                refine ⟨12050538659208416971004429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8033692439472277980669619 12050538659208416971004429)
                ·
                  refine ⟨4518951997203156364126661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12050538659208416971004429 4518951997203156364126661)
                  ·
                    refine ⟨847303499475591818273749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4518951997203156364126661 847303499475591818273749)
                    ·
                      rfl

theorem cell23_4950353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 3, 2, 1, 3, 4].length) (baseStart_4950353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4950353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4950353 prefixEnd_4950353 := by exact prefixLift 4950353
  have htrace : WordTrace (prefixWord ++ tailWord_4950353) baseStart_4950353 baseEnd_4950353 := by
    simpa [prefixWord, tailWord_4950353, baseEnd_4950353] using wordTrace_append hprefix tailTrace_4950353
  have hstable : (prefixWord ++ tailWord_4950353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4950353).length < 2 ^ (prefixWord ++ tailWord_4950353).sum := by decide
  have hdescent : baseEnd_4950353 < baseStart_4950353 := by decide
  rcases family_descends (prefixWord ++ tailWord_4950353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4950430 : List Nat := [4, 3, 1, 2, 1, 2, 1, 1, 3, 5]
def baseStart_4950430 : Nat := 118140960795 + 4950430 * 2 ^ 59
def prefixEnd_4950430 : Nat := 4983230072969 + 3 ^ 40 * 4950430 * 2
def baseEnd_4950430 : Nat := 847316678812390551186131

theorem tailTrace_4950430 : CollatzResearch.WordTrace tailWord_4950430 prefixEnd_4950430 847316678812390551186131 := by
  unfold tailWord_4950430
  simp only [CollatzResearch.WordTrace]
  refine ⟨22569626931930631372264093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 120371343636963367318741829 22569626931930631372264093)
  ·
    refine ⟨8463610099473986764599035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22569626931930631372264093 8463610099473986764599035)
    ·
      refine ⟨12695415149210980146898553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8463610099473986764599035 12695415149210980146898553)
      ·
        refine ⟨9521561361908235110173915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12695415149210980146898553 9521561361908235110173915)
        ·
          refine ⟨14282342042862352665260873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9521561361908235110173915 14282342042862352665260873)
          ·
            refine ⟨10711756532146764498945655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14282342042862352665260873 10711756532146764498945655)
            ·
              refine ⟨16067634798220146748418483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10711756532146764498945655 16067634798220146748418483)
              ·
                refine ⟨24101452197330220122627725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16067634798220146748418483 24101452197330220122627725)
                ·
                  refine ⟨9038044573998832545985397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24101452197330220122627725 9038044573998832545985397)
                  ·
                    refine ⟨847316678812390551186131, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9038044573998832545985397 847316678812390551186131)
                    ·
                      rfl

theorem cell23_4950430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 2, 1, 1, 3, 5].length) (baseStart_4950430 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4950430 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4950430 prefixEnd_4950430 := by exact prefixLift 4950430
  have htrace : WordTrace (prefixWord ++ tailWord_4950430) baseStart_4950430 baseEnd_4950430 := by
    simpa [prefixWord, tailWord_4950430, baseEnd_4950430] using wordTrace_append hprefix tailTrace_4950430
  have hstable : (prefixWord ++ tailWord_4950430).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4950430).length < 2 ^ (prefixWord ++ tailWord_4950430).sum := by decide
  have hdescent : baseEnd_4950430 < baseStart_4950430 := by decide
  rcases family_descends (prefixWord ++ tailWord_4950430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4950436 : List Nat := [2, 3, 1, 2, 1, 1, 2, 2, 3, 1, 5]
def baseStart_4950436 : Nat := 118140960795 + 4950436 * 2 ^ 59
def prefixEnd_4950436 : Nat := 4983230072969 + 3 ^ 40 * 4950436 * 2
def baseEnd_4950436 : Nat := 2541953117321098630083365

theorem tailTrace_4950436 : CollatzResearch.WordTrace tailWord_4950436 prefixEnd_4950436 2541953117321098630083365 := by
  unfold tailWord_4950436
  simp only [CollatzResearch.WordTrace]
  refine ⟨90278617146711657001415581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120371489528948876001887441 90278617146711657001415581)
  ·
    refine ⟨33854481430016871375530843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 90278617146711657001415581 33854481430016871375530843)
    ·
      refine ⟨50781722145025307063296265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33854481430016871375530843 50781722145025307063296265)
      ·
        refine ⟨38086291608768980297472199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50781722145025307063296265 38086291608768980297472199)
        ·
          refine ⟨57129437413153470446208299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38086291608768980297472199 57129437413153470446208299)
          ·
            refine ⟨85694156119730205669312449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57129437413153470446208299 85694156119730205669312449)
            ·
              refine ⟨64270617089797654251984337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 85694156119730205669312449 64270617089797654251984337)
              ·
                refine ⟨48202962817348240688988253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 64270617089797654251984337 48202962817348240688988253)
                ·
                  refine ⟨18076111056505590258370595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 48202962817348240688988253 18076111056505590258370595)
                  ·
                    refine ⟨27114166584758385387555893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18076111056505590258370595 27114166584758385387555893)
                    ·
                      refine ⟨2541953117321098630083365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27114166584758385387555893 2541953117321098630083365)
                      ·
                        rfl

theorem cell23_4950436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 2, 2, 3, 1, 5].length) (baseStart_4950436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4950436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4950436 prefixEnd_4950436 := by exact prefixLift 4950436
  have htrace : WordTrace (prefixWord ++ tailWord_4950436) baseStart_4950436 baseEnd_4950436 := by
    simpa [prefixWord, tailWord_4950436, baseEnd_4950436] using wordTrace_append hprefix tailTrace_4950436
  have hstable : (prefixWord ++ tailWord_4950436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4950436).length < 2 ^ (prefixWord ++ tailWord_4950436).sum := by decide
  have hdescent : baseEnd_4950436 < baseStart_4950436 := by decide
  rcases family_descends (prefixWord ++ tailWord_4950436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4950450 : List Nat := [3, 2, 1, 1, 1, 1, 7, 1, 1, 1, 4]
def baseStart_4950450 : Nat := 118140960795 + 4950450 * 2 ^ 59
def prefixEnd_4950450 : Nat := 4983230072969 + 3 ^ 40 * 4950450 * 2
def baseEnd_4950450 : Nat := 2541960306050261575308301

theorem tailTrace_4950450 : CollatzResearch.WordTrace tailWord_4950450 prefixEnd_4950450 2541960306050261575308301 := by
  unfold tailWord_4950450
  simp only [CollatzResearch.WordTrace]
  refine ⟨45139436228843148598460201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 120371829943581729595893869 45139436228843148598460201)
  ·
    refine ⟨33854577171632361448845151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45139436228843148598460201 33854577171632361448845151)
    ·
      refine ⟨50781865757448542173267727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33854577171632361448845151 50781865757448542173267727)
      ·
        refine ⟨76172798636172813259901591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50781865757448542173267727 76172798636172813259901591)
        ·
          refine ⟨114259197954259219889852387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76172798636172813259901591 114259197954259219889852387)
          ·
            refine ⟨171388796931388829834778581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 114259197954259219889852387 171388796931388829834778581)
            ·
              refine ⟨4016924928079425699252623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 171388796931388829834778581 4016924928079425699252623)
              ·
                refine ⟨6025387392119138548878935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4016924928079425699252623 6025387392119138548878935)
                ·
                  refine ⟨9038081088178707823318403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6025387392119138548878935 9038081088178707823318403)
                  ·
                    refine ⟨13557121632268061734977605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9038081088178707823318403 13557121632268061734977605)
                    ·
                      refine ⟨2541960306050261575308301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13557121632268061734977605 2541960306050261575308301)
                      ·
                        rfl

theorem cell23_4950450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 7, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 7, 1, 1, 1, 4].length) (baseStart_4950450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4950450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4950450 prefixEnd_4950450 := by exact prefixLift 4950450
  have htrace : WordTrace (prefixWord ++ tailWord_4950450) baseStart_4950450 baseEnd_4950450 := by
    simpa [prefixWord, tailWord_4950450, baseEnd_4950450] using wordTrace_append hprefix tailTrace_4950450
  have hstable : (prefixWord ++ tailWord_4950450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4950450).length < 2 ^ (prefixWord ++ tailWord_4950450).sum := by decide
  have hdescent : baseEnd_4950450 < baseStart_4950450 := by decide
  rcases family_descends (prefixWord ++ tailWord_4950450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4950460 : List Nat := [2, 2, 2, 4, 1, 1, 1, 4, 2, 4]
def baseStart_4950460 : Nat := 118140960795 + 4950460 * 2 ^ 59
def prefixEnd_4950460 : Nat := 4983230072969 + 3 ^ 40 * 4950460 * 2
def baseEnd_4950460 : Nat := 847321813618935512061085

theorem tailTrace_4950460 : CollatzResearch.WordTrace tailWord_4950460 prefixEnd_4950460 847321813618935512061085 := by
  unfold tailWord_4950460
  simp only [CollatzResearch.WordTrace]
  refine ⟨90279054822668183050852417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120372073096890910734469889 90279054822668183050852417)
  ·
    refine ⟨67709291117001137288139313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90279054822668183050852417 67709291117001137288139313)
    ·
      refine ⟨50781968337750852966104485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67709291117001137288139313 50781968337750852966104485)
      ·
        refine ⟨9521619063328284931144591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 50781968337750852966104485 9521619063328284931144591)
        ·
          refine ⟨14282428594992427396716887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9521619063328284931144591 14282428594992427396716887)
          ·
            refine ⟨21423642892488641095075331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14282428594992427396716887 21423642892488641095075331)
            ·
              refine ⟨32135464338732961642612997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21423642892488641095075331 32135464338732961642612997)
              ·
                refine ⟨6025399563512430307989937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 32135464338732961642612997 6025399563512430307989937)
                ·
                  refine ⟨4519049672634322730992453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6025399563512430307989937 4519049672634322730992453)
                  ·
                    refine ⟨847321813618935512061085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4519049672634322730992453 847321813618935512061085)
                    ·
                      rfl

theorem cell23_4950460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 1, 4, 2, 4].length) (baseStart_4950460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4950460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4950460 prefixEnd_4950460 := by exact prefixLift 4950460
  have htrace : WordTrace (prefixWord ++ tailWord_4950460) baseStart_4950460 baseEnd_4950460 := by
    simpa [prefixWord, tailWord_4950460, baseEnd_4950460] using wordTrace_append hprefix tailTrace_4950460
  have hstable : (prefixWord ++ tailWord_4950460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4950460).length < 2 ^ (prefixWord ++ tailWord_4950460).sum := by decide
  have hdescent : baseEnd_4950460 < baseStart_4950460 := by decide
  rcases family_descends (prefixWord ++ tailWord_4950460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4950496 : List Nat := [2, 1, 1, 3, 1, 1, 4, 1, 2, 2, 5]
def baseStart_4950496 : Nat := 118140960795 + 4950496 * 2 ^ 59
def prefixEnd_4950496 : Nat := 4983230072969 + 3 ^ 40 * 4950496 * 2
def baseEnd_4950496 : Nat := 2541983926160368395333089

theorem tailTrace_4950496 : CollatzResearch.WordTrace tailWord_4950496 prefixEnd_4950496 2541983926160368395333089 := by
  unfold tailWord_4950496
  simp only [CollatzResearch.WordTrace]
  refine ⟨90279711336602972125007671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120372948448803962833343561 90279711336602972125007671)
  ·
    refine ⟨135419567004904458187511507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90279711336602972125007671 135419567004904458187511507)
    ·
      refine ⟨203129350507356687281267261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 135419567004904458187511507 203129350507356687281267261)
      ·
        refine ⟨76173506440258757730475223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 203129350507356687281267261 76173506440258757730475223)
        ·
          refine ⟨114260259660388136595712835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76173506440258757730475223 114260259660388136595712835)
          ·
            refine ⟨171390389490582204893569253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 114260259660388136595712835 171390389490582204893569253)
            ·
              refine ⟨32135698029484163417544235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 171390389490582204893569253 32135698029484163417544235)
              ·
                refine ⟨48203547044226245126316353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32135698029484163417544235 48203547044226245126316353)
                ·
                  refine ⟨36152660283169683844737265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 48203547044226245126316353 36152660283169683844737265)
                  ·
                    refine ⟨27114495212377262883552949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 36152660283169683844737265 27114495212377262883552949)
                    ·
                      refine ⟨2541983926160368395333089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27114495212377262883552949 2541983926160368395333089)
                      ·
                        rfl

theorem cell23_4950496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 4, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 4, 1, 2, 2, 5].length) (baseStart_4950496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4950496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4950496 prefixEnd_4950496 := by exact prefixLift 4950496
  have htrace : WordTrace (prefixWord ++ tailWord_4950496) baseStart_4950496 baseEnd_4950496 := by
    simpa [prefixWord, tailWord_4950496, baseEnd_4950496] using wordTrace_append hprefix tailTrace_4950496
  have hstable : (prefixWord ++ tailWord_4950496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4950496).length < 2 ^ (prefixWord ++ tailWord_4950496).sum := by decide
  have hdescent : baseEnd_4950496 < baseStart_4950496 := by decide
  rcases family_descends (prefixWord ++ tailWord_4950496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4950501 : List Nat := [1, 3, 1, 5, 2, 1, 2, 3, 1, 2, 2]
def baseStart_4950501 : Nat := 118140960795 + 4950501 * 2 ^ 59
def prefixEnd_4950501 : Nat := 4983230072969 + 3 ^ 40 * 4950501 * 2
def baseEnd_4950501 : Nat := 2541986493563640875770567

theorem tailTrace_4950501 : CollatzResearch.WordTrace tailWord_4950501 prefixEnd_4950501 2541986493563640875770567 := by
  unfold tailWord_4950501
  simp only [CollatzResearch.WordTrace]
  refine ⟨180559605038187830103947357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120373070025458553402631571 180559605038187830103947357)
  ·
    refine ⟨67709851889320436288980259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 180559605038187830103947357 67709851889320436288980259)
    ·
      refine ⟨101564777833980654433470389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67709851889320436288980259 101564777833980654433470389)
      ·
        refine ⟨9521697921935686353137849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 101564777833980654433470389 9521697921935686353137849)
        ·
          refine ⟨7141273441451764764853387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9521697921935686353137849 7141273441451764764853387)
          ·
            refine ⟨10711910162177647147280081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7141273441451764764853387 10711910162177647147280081)
            ·
              refine ⟨8033932621633235360460061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10711910162177647147280081 8033932621633235360460061)
              ·
                refine ⟨3012724733112463260172523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8033932621633235360460061 3012724733112463260172523)
                ·
                  refine ⟨4519087099668694890258785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3012724733112463260172523 4519087099668694890258785)
                  ·
                    refine ⟨3389315324751521167694089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4519087099668694890258785 3389315324751521167694089)
                    ·
                      refine ⟨2541986493563640875770567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3389315324751521167694089 2541986493563640875770567)
                      ·
                        rfl

theorem cell23_4950501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 1, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 1, 2, 3, 1, 2, 2].length) (baseStart_4950501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4950501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4950501 prefixEnd_4950501 := by exact prefixLift 4950501
  have htrace : WordTrace (prefixWord ++ tailWord_4950501) baseStart_4950501 baseEnd_4950501 := by
    simpa [prefixWord, tailWord_4950501, baseEnd_4950501] using wordTrace_append hprefix tailTrace_4950501
  have hstable : (prefixWord ++ tailWord_4950501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4950501).length < 2 ^ (prefixWord ++ tailWord_4950501).sum := by decide
  have hdescent : baseEnd_4950501 < baseStart_4950501 := by decide
  rcases family_descends (prefixWord ++ tailWord_4950501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4950557 : List Nat := [1, 4, 2, 2, 1, 2, 1, 2, 4, 2, 2]
def baseStart_4950557 : Nat := 118140960795 + 4950557 * 2 ^ 59
def prefixEnd_4950557 : Nat := 4983230072969 + 3 ^ 40 * 4950557 * 2
def baseEnd_4950557 : Nat := 2542015248480292656670309

theorem tailTrace_4950557 : CollatzResearch.WordTrace tailWord_4950557 prefixEnd_4950557 2542015248480292656670309 := by
  unfold tailWord_4950557
  simp only [CollatzResearch.WordTrace]
  refine ⟨180561647525984951667985925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120374431683989967778657283 180561647525984951667985925)
  ·
    refine ⟨33855308911122178437747361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 180561647525984951667985925 33855308911122178437747361)
    ·
      refine ⟨25391481683341633828310521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33855308911122178437747361 25391481683341633828310521)
      ·
        refine ⟨19043611262506225371232891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25391481683341633828310521 19043611262506225371232891)
        ·
          refine ⟨28565416893759338056849337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19043611262506225371232891 28565416893759338056849337)
          ·
            refine ⟨21424062670319503542637003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28565416893759338056849337 21424062670319503542637003)
            ·
              refine ⟨32136094005479255313955505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21424062670319503542637003 32136094005479255313955505)
              ·
                refine ⟨24102070504109441485466629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32136094005479255313955505 24102070504109441485466629)
                ·
                  refine ⟨4519138219520520278524993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24102070504109441485466629 4519138219520520278524993)
                  ·
                    refine ⟨3389353664640390208893745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4519138219520520278524993 3389353664640390208893745)
                    ·
                      refine ⟨2542015248480292656670309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3389353664640390208893745 2542015248480292656670309)
                      ·
                        rfl

theorem cell23_4950557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 1, 2, 4, 2, 2].length) (baseStart_4950557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4950557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4950557 prefixEnd_4950557 := by exact prefixLift 4950557
  have htrace : WordTrace (prefixWord ++ tailWord_4950557) baseStart_4950557 baseEnd_4950557 := by
    simpa [prefixWord, tailWord_4950557, baseEnd_4950557] using wordTrace_append hprefix tailTrace_4950557
  have hstable : (prefixWord ++ tailWord_4950557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4950557).length < 2 ^ (prefixWord ++ tailWord_4950557).sum := by decide
  have hdescent : baseEnd_4950557 < baseStart_4950557 := by decide
  rcases family_descends (prefixWord ++ tailWord_4950557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4950560 : List Nat := [2, 1, 1, 6, 2, 1, 1, 1, 2, 1, 5]
def baseStart_4950560 : Nat := 118140960795 + 4950560 * 2 ^ 59
def prefixEnd_4950560 : Nat := 4983230072969 + 3 ^ 40 * 4950560 * 2
def baseEnd_4950560 : Nat := 2542016788922256144932795

theorem tailTrace_4950560 : CollatzResearch.WordTrace tailWord_4950560 prefixEnd_4950560 2542016788922256144932795 := by
  unfold tailWord_4950560
  simp only [CollatzResearch.WordTrace]
  refine ⟨90280878472487041590172567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120374504629982722120230089 90280878472487041590172567)
  ·
    refine ⟨135421317708730562385258851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90280878472487041590172567 135421317708730562385258851)
    ·
      refine ⟨203131976563095843577888277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 135421317708730562385258851 203131976563095843577888277)
      ·
        refine ⟨9521811401395117667713513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 203131976563095843577888277 9521811401395117667713513)
        ·
          refine ⟨7141358551046338250785135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9521811401395117667713513 7141358551046338250785135)
          ·
            refine ⟨10712037826569507376177703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7141358551046338250785135 10712037826569507376177703)
            ·
              refine ⟨16068056739854261064266555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10712037826569507376177703 16068056739854261064266555)
              ·
                refine ⟨24102085109781391596399833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16068056739854261064266555 24102085109781391596399833)
                ·
                  refine ⟨18076563832336043697299875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24102085109781391596399833 18076563832336043697299875)
                  ·
                    refine ⟨27114845748504065545949813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18076563832336043697299875 27114845748504065545949813)
                    ·
                      refine ⟨2542016788922256144932795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27114845748504065545949813 2542016788922256144932795)
                      ·
                        rfl

theorem cell23_4950560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 1, 1, 1, 2, 1, 5].length) (baseStart_4950560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4950560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4950560 prefixEnd_4950560 := by exact prefixLift 4950560
  have htrace : WordTrace (prefixWord ++ tailWord_4950560) baseStart_4950560 baseEnd_4950560 := by
    simpa [prefixWord, tailWord_4950560, baseEnd_4950560] using wordTrace_append hprefix tailTrace_4950560
  have hstable : (prefixWord ++ tailWord_4950560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4950560).length < 2 ^ (prefixWord ++ tailWord_4950560).sum := by decide
  have hdescent : baseEnd_4950560 < baseStart_4950560 := by decide
  rcases family_descends (prefixWord ++ tailWord_4950560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4950610 : List Nat := [3, 2, 2, 1, 2, 1, 4, 1, 2, 5]
def baseStart_4950610 : Nat := 118140960795 + 4950610 * 2 ^ 59
def prefixEnd_4950610 : Nat := 4983230072969 + 3 ^ 40 * 4950610 * 2
def baseEnd_4950610 : Nat := 847347487651660316435855

theorem tailTrace_4950610 : CollatzResearch.WordTrace tailWord_4950610 prefixEnd_4950610 847347487651660316435855 := by
  unfold tailWord_4950610
  simp only [CollatzResearch.WordTrace]
  refine ⟨45140895148698235429916321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 120375720396528627813110189 45140895148698235429916321)
  ·
    refine ⟨33855671361523676572437241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45140895148698235429916321 33855671361523676572437241)
    ·
      refine ⟨25391753521142757429327931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33855671361523676572437241 25391753521142757429327931)
      ·
        refine ⟨38087630281714136143991897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25391753521142757429327931 38087630281714136143991897)
        ·
          refine ⟨28565722711285602107993923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38087630281714136143991897 28565722711285602107993923)
          ·
            refine ⟨42848584066928403161990885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28565722711285602107993923 42848584066928403161990885)
            ·
              refine ⟨8034109512549075592873291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 42848584066928403161990885 8034109512549075592873291)
              ·
                refine ⟨12051164268823613389309937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8034109512549075592873291 12051164268823613389309937)
                ·
                  refine ⟨9038373201617710041982453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12051164268823613389309937 9038373201617710041982453)
                  ·
                    refine ⟨847347487651660316435855, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9038373201617710041982453 847347487651660316435855)
                    ·
                      rfl

theorem cell23_4950610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 4, 1, 2, 5].length) (baseStart_4950610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4950610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4950610 prefixEnd_4950610 := by exact prefixLift 4950610
  have htrace : WordTrace (prefixWord ++ tailWord_4950610) baseStart_4950610 baseEnd_4950610 := by
    simpa [prefixWord, tailWord_4950610, baseEnd_4950610] using wordTrace_append hprefix tailTrace_4950610
  have hstable : (prefixWord ++ tailWord_4950610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4950610).length < 2 ^ (prefixWord ++ tailWord_4950610).sum := by decide
  have hdescent : baseEnd_4950610 < baseStart_4950610 := by decide
  rcases family_descends (prefixWord ++ tailWord_4950610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4950613 : List Nat := [1, 3, 2, 2, 1, 1, 2, 3, 1, 3, 4]
def baseStart_4950613 : Nat := 118140960795 + 4950613 * 2 ^ 59
def prefixEnd_4950613 : Nat := 4983230072969 + 3 ^ 40 * 4950613 * 2
def baseEnd_4950613 : Nat := 2542044003396944437570051

theorem tailTrace_4950613 : CollatzResearch.WordTrace tailWord_4950613 prefixEnd_4950613 2542044003396944437570051 := by
  unfold tailWord_4950613
  simp only [CollatzResearch.WordTrace]
  refine ⟨180563690013782073232024493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120375793342521382154682995 180563690013782073232024493)
  ·
    refine ⟨67711383755168277462009185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 180563690013782073232024493 67711383755168277462009185)
    ·
      refine ⟨50783537816376208096506889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67711383755168277462009185 50783537816376208096506889)
      ·
        refine ⟨38087653362282156072380167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50783537816376208096506889 38087653362282156072380167)
        ·
          refine ⟨57131480043423234108570251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38087653362282156072380167 57131480043423234108570251)
          ·
            refine ⟨85697220065134851162855377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57131480043423234108570251 85697220065134851162855377)
            ·
              refine ⟨64272915048851138372141533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 85697220065134851162855377 64272915048851138372141533)
              ·
                refine ⟨24102343143319176889553075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 64272915048851138372141533 24102343143319176889553075)
                ·
                  refine ⟨36153514714978765334329613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24102343143319176889553075 36153514714978765334329613)
                  ·
                    refine ⟨13557568018117037000373605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 36153514714978765334329613 13557568018117037000373605)
                    ·
                      refine ⟨2542044003396944437570051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13557568018117037000373605 2542044003396944437570051)
                      ·
                        rfl

theorem cell23_4950613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 2, 3, 1, 3, 4].length) (baseStart_4950613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4950613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4950613 prefixEnd_4950613 := by exact prefixLift 4950613
  have htrace : WordTrace (prefixWord ++ tailWord_4950613) baseStart_4950613 baseEnd_4950613 := by
    simpa [prefixWord, tailWord_4950613, baseEnd_4950613] using wordTrace_append hprefix tailTrace_4950613
  have hstable : (prefixWord ++ tailWord_4950613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4950613).length < 2 ^ (prefixWord ++ tailWord_4950613).sum := by decide
  have hdescent : baseEnd_4950613 < baseStart_4950613 := by decide
  rcases family_descends (prefixWord ++ tailWord_4950613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4950633 : List Nat := [1, 2, 1, 1, 1, 4, 1, 2, 3, 4, 3]
def baseStart_4950633 : Nat := 118140960795 + 4950633 * 2 ^ 59
def prefixEnd_4950633 : Nat := 4983230072969 + 3 ^ 40 * 4950633 * 2
def baseEnd_4950633 : Nat := 2542054273010034359319959

theorem tailTrace_4950633 : CollatzResearch.WordTrace tailWord_4950633 prefixEnd_4950633 2542054273010034359319959 := by
  unfold tailWord_4950633
  simp only [CollatzResearch.WordTrace]
  refine ⟨180564419473709616647752553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120376279649139744431835035 180564419473709616647752553)
  ·
    refine ⟨135423314605282212485814415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 180564419473709616647752553 135423314605282212485814415)
    ·
      refine ⟨203134971907923318728721623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 135423314605282212485814415 203134971907923318728721623)
      ·
        refine ⟨304702457861884978093082435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 203134971907923318728721623 304702457861884978093082435)
        ·
          refine ⟨457053686792827467139623653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 304702457861884978093082435 457053686792827467139623653)
          ·
            refine ⟨85697566273655150088679435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 457053686792827467139623653 85697566273655150088679435)
            ·
              refine ⟨128546349410482725133019153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 85697566273655150088679435 128546349410482725133019153)
              ·
                refine ⟨96409762057862043849764365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 128546349410482725133019153 96409762057862043849764365)
                ·
                  refine ⟨36153660771698266443661637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 96409762057862043849764365 36153660771698266443661637)
                  ·
                    refine ⟨6778811394693424958186557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 36153660771698266443661637 6778811394693424958186557)
                    ·
                      refine ⟨2542054273010034359319959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6778811394693424958186557 2542054273010034359319959)
                      ·
                        rfl

theorem cell23_4950633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 2, 3, 4, 3].length) (baseStart_4950633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4950633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4950633 prefixEnd_4950633 := by exact prefixLift 4950633
  have htrace : WordTrace (prefixWord ++ tailWord_4950633) baseStart_4950633 baseEnd_4950633 := by
    simpa [prefixWord, tailWord_4950633, baseEnd_4950633] using wordTrace_append hprefix tailTrace_4950633
  have hstable : (prefixWord ++ tailWord_4950633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4950633).length < 2 ^ (prefixWord ++ tailWord_4950633).sum := by decide
  have hdescent : baseEnd_4950633 < baseStart_4950633 := by decide
  rcases family_descends (prefixWord ++ tailWord_4950633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4950674 : List Nat := [3, 2, 3, 1, 2, 1, 1, 5, 1, 4]
def baseStart_4950674 : Nat := 118140960795 + 4950674 * 2 ^ 59
def prefixEnd_4950674 : Nat := 4983230072969 + 3 ^ 40 * 4950674 * 2
def baseEnd_4950674 : Nat := 847358441905622899635757

theorem tailTrace_4950674 : CollatzResearch.WordTrace tailWord_4950674 prefixEnd_4950674 847358441905622899635757 := by
  unfold tailWord_4950674
  simp only [CollatzResearch.WordTrace]
  refine ⟨45141478716640270162498769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 120377276577707387099996717 45141478716640270162498769)
  ·
    refine ⟨33856109037480202621874077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45141478716640270162498769 33856109037480202621874077)
    ·
      refine ⟨12696040889055075983202779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33856109037480202621874077 12696040889055075983202779)
      ·
        refine ⟨19044061333582613974804169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12696040889055075983202779 19044061333582613974804169)
        ·
          refine ⟨14283046000186960481103127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19044061333582613974804169 14283046000186960481103127)
          ·
            refine ⟨21424569000280440721654691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14283046000186960481103127 21424569000280440721654691)
            ·
              refine ⟨32136853500420661082482037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21424569000280440721654691 32136853500420661082482037)
              ·
                refine ⟨3012830015664436976482691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 32136853500420661082482037 3012830015664436976482691)
                ·
                  refine ⟨4519245023496655464724037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3012830015664436976482691 4519245023496655464724037)
                  ·
                    refine ⟨847358441905622899635757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4519245023496655464724037 847358441905622899635757)
                    ·
                      rfl

theorem cell23_4950674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 1, 5, 1, 4].length) (baseStart_4950674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4950674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4950674 prefixEnd_4950674 := by exact prefixLift 4950674
  have htrace : WordTrace (prefixWord ++ tailWord_4950674) baseStart_4950674 baseEnd_4950674 := by
    simpa [prefixWord, tailWord_4950674, baseEnd_4950674] using wordTrace_append hprefix tailTrace_4950674
  have hstable : (prefixWord ++ tailWord_4950674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4950674).length < 2 ^ (prefixWord ++ tailWord_4950674).sum := by decide
  have hdescent : baseEnd_4950674 < baseStart_4950674 := by decide
  rcases family_descends (prefixWord ++ tailWord_4950674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4950717 : List Nat := [1, 4, 1, 2, 1, 4, 2, 2, 1, 5]
def baseStart_4950717 : Nat := 118140960795 + 4950717 * 2 ^ 59
def prefixEnd_4950717 : Nat := 4983230072969 + 3 ^ 40 * 4950717 * 2
def baseEnd_4950717 : Nat := 847365801795004010223191

theorem tailTrace_4950717 : CollatzResearch.WordTrace tailWord_4950717 prefixEnd_4950717 847365801795004010223191 := by
  unfold tailWord_4950717
  simp only [CollatzResearch.WordTrace]
  refine ⟨180567483205405298993810405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120378322136936865995873603 180567483205405298993810405)
  ·
    refine ⟨33856403101013493561339451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 180567483205405298993810405 33856403101013493561339451)
    ·
      refine ⟨50784604651520240342009177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33856403101013493561339451 50784604651520240342009177)
      ·
        refine ⟨38088453488640180256506883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50784604651520240342009177 38088453488640180256506883)
        ·
          refine ⟨57132680232960270384760325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38088453488640180256506883 57132680232960270384760325)
          ·
            refine ⟨10712377543680050697142561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 57132680232960270384760325 10712377543680050697142561)
            ·
              refine ⟨8034283157760038022856921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10712377543680050697142561 8034283157760038022856921)
              ·
                refine ⟨6025712368320028517142691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8034283157760038022856921 6025712368320028517142691)
                ·
                  refine ⟨9038568552480042775714037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6025712368320028517142691 9038568552480042775714037)
                  ·
                    refine ⟨847365801795004010223191, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9038568552480042775714037 847365801795004010223191)
                    ·
                      rfl

theorem cell23_4950717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 4, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 4, 2, 2, 1, 5].length) (baseStart_4950717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4950717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4950717 prefixEnd_4950717 := by exact prefixLift 4950717
  have htrace : WordTrace (prefixWord ++ tailWord_4950717) baseStart_4950717 baseEnd_4950717 := by
    simpa [prefixWord, tailWord_4950717, baseEnd_4950717] using wordTrace_append hprefix tailTrace_4950717
  have hstable : (prefixWord ++ tailWord_4950717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4950717).length < 2 ^ (prefixWord ++ tailWord_4950717).sum := by decide
  have hdescent : baseEnd_4950717 < baseStart_4950717 := by decide
  rcases family_descends (prefixWord ++ tailWord_4950717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4950741 : List Nat := [1, 3, 2, 5, 1, 1, 1, 2, 2, 3, 2]
def baseStart_4950741 : Nat := 118140960795 + 4950741 * 2 ^ 59
def prefixEnd_4950741 : Nat := 4983230072969 + 3 ^ 40 * 4950741 * 2
def baseEnd_4950741 : Nat := 2542109728920719936769463

theorem tailTrace_4950741 : CollatzResearch.WordTrace tailWord_4950741 prefixEnd_4950741 2542109728920719936769463 := by
  unfold tailWord_4950741
  simp only [CollatzResearch.WordTrace]
  refine ⟨180568358557318351092684077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120378905704878900728456051 180568358557318351092684077)
  ·
    refine ⟨67713134458994381659756529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 180568358557318351092684077 67713134458994381659756529)
    ·
      refine ⟨50784850844245786244817397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67713134458994381659756529 50784850844245786244817397)
      ·
        refine ⟨4761079766648042460451631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 50784850844245786244817397 4761079766648042460451631)
        ·
          refine ⟨7141619649972063690677447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4761079766648042460451631 7141619649972063690677447)
          ·
            refine ⟨10712429474958095536016171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7141619649972063690677447 10712429474958095536016171)
            ·
              refine ⟨16068644212437143304024257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10712429474958095536016171 16068644212437143304024257)
              ·
                refine ⟨12051483159327857478018193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16068644212437143304024257 12051483159327857478018193)
                ·
                  refine ⟨9038612369495893108513645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12051483159327857478018193 9038612369495893108513645)
                  ·
                    refine ⟨3389479638560959915692617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9038612369495893108513645 3389479638560959915692617)
                    ·
                      refine ⟨2542109728920719936769463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3389479638560959915692617 2542109728920719936769463)
                      ·
                        rfl

theorem cell23_4950741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 1, 1, 2, 2, 3, 2].length) (baseStart_4950741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4950741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4950741 prefixEnd_4950741 := by exact prefixLift 4950741
  have htrace : WordTrace (prefixWord ++ tailWord_4950741) baseStart_4950741 baseEnd_4950741 := by
    simpa [prefixWord, tailWord_4950741, baseEnd_4950741] using wordTrace_append hprefix tailTrace_4950741
  have hstable : (prefixWord ++ tailWord_4950741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4950741).length < 2 ^ (prefixWord ++ tailWord_4950741).sum := by decide
  have hdescent : baseEnd_4950741 < baseStart_4950741 := by decide
  rcases family_descends (prefixWord ++ tailWord_4950741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4950743 : List Nat := [1, 1, 3, 2, 1, 4, 11]
def baseStart_4950743 : Nat := 118140960795 + 4950743 * 2 ^ 59
def prefixEnd_4950743 : Nat := 4983230072969 + 3 ^ 40 * 4950743 * 2
def baseEnd_4950743 : Nat := 31384083405950974431413

theorem tailTrace_4950743 : CollatzResearch.WordTrace tailWord_4950743 prefixEnd_4950743 31384083405950974431413 := by
  unfold tailWord_4950743
  simp only [CollatzResearch.WordTrace]
  refine ⟨180568431503311105434256883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120378954335540736956171255 180568431503311105434256883)
  ·
    refine ⟨270852647254966658151385325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 180568431503311105434256883 270852647254966658151385325)
    ·
      refine ⟨101569742720612496806769497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 270852647254966658151385325 101569742720612496806769497)
      ·
        refine ⟨76177307040459372605077123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 101569742720612496806769497 76177307040459372605077123)
        ·
          refine ⟨114265960560689058907615685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76177307040459372605077123 114265960560689058907615685)
          ·
            refine ⟨21424867605129198545177941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 114265960560689058907615685 21424867605129198545177941)
            ·
              refine ⟨31384083405950974431413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 21424867605129198545177941 31384083405950974431413)
              ·
                rfl

theorem cell23_4950743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 11].length) (baseStart_4950743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4950743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4950743 prefixEnd_4950743 := by exact prefixLift 4950743
  have htrace : WordTrace (prefixWord ++ tailWord_4950743) baseStart_4950743 baseEnd_4950743 := by
    simpa [prefixWord, tailWord_4950743, baseEnd_4950743] using wordTrace_append hprefix tailTrace_4950743
  have hstable : (prefixWord ++ tailWord_4950743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4950743).length < 2 ^ (prefixWord ++ tailWord_4950743).sum := by decide
  have hdescent : baseEnd_4950743 < baseStart_4950743 := by decide
  rcases family_descends (prefixWord ++ tailWord_4950743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4950763 : List Nat := [1, 1, 1, 1, 2, 4, 1, 1, 1, 4, 6]
def baseStart_4950763 : Nat := 118140960795 + 4950763 * 2 ^ 59
def prefixEnd_4950763 : Nat := 4983230072969 + 3 ^ 40 * 4950763 * 2
def baseEnd_4950763 : Nat := 2542121025495118850694361

theorem tailTrace_4950763 : CollatzResearch.WordTrace tailWord_4950763 prefixEnd_4950763 2542121025495118850694361 := by
  unfold tailWord_4950763
  simp only [CollatzResearch.WordTrace]
  refine ⟨180569160963238648849984943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120379440642159099233323295 180569160963238648849984943)
  ·
    refine ⟨270853741444857973274977415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 180569160963238648849984943 270853741444857973274977415)
    ·
      refine ⟨406280612167286959912466123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 270853741444857973274977415 406280612167286959912466123)
      ·
        refine ⟨609420918250930439868699185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 406280612167286959912466123 609420918250930439868699185)
        ·
          refine ⟨457065688688197829901524389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 609420918250930439868699185 457065688688197829901524389)
          ·
            refine ⟨85699816629037093106535823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 457065688688197829901524389 85699816629037093106535823)
            ·
              refine ⟨128549724943555639659803735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 85699816629037093106535823 128549724943555639659803735)
              ·
                refine ⟨192824587415333459489705603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 128549724943555639659803735 192824587415333459489705603)
                ·
                  refine ⟨289236881123000189234558405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 192824587415333459489705603 289236881123000189234558405)
                  ·
                    refine ⟨54231915210562535481479701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 289236881123000189234558405 54231915210562535481479701)
                    ·
                      refine ⟨2542121025495118850694361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 54231915210562535481479701 2542121025495118850694361)
                      ·
                        rfl

theorem cell23_4950763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 1, 1, 4, 6].length) (baseStart_4950763 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4950763 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4950763 prefixEnd_4950763 := by exact prefixLift 4950763
  have htrace : WordTrace (prefixWord ++ tailWord_4950763) baseStart_4950763 baseEnd_4950763 := by
    simpa [prefixWord, tailWord_4950763, baseEnd_4950763] using wordTrace_append hprefix tailTrace_4950763
  have hstable : (prefixWord ++ tailWord_4950763).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4950763).length < 2 ^ (prefixWord ++ tailWord_4950763).sum := by decide
  have hdescent : baseEnd_4950763 < baseStart_4950763 := by decide
  rcases family_descends (prefixWord ++ tailWord_4950763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4950791 : List Nat := [1, 1, 4, 4, 1, 2, 3, 1, 1, 2, 3]
def baseStart_4950791 : Nat := 118140960795 + 4950791 * 2 ^ 59
def prefixEnd_4950791 : Nat := 4983230072969 + 3 ^ 40 * 4950791 * 2
def baseEnd_4950791 : Nat := 2542135402953444741144233

theorem tailTrace_4950791 : CollatzResearch.WordTrace tailWord_4950791 prefixEnd_4950791 2542135402953444741144233 := by
  unfold tailWord_4950791
  simp only [CollatzResearch.WordTrace]
  refine ⟨180570182207137209632004227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120380121471424806421336151 180570182207137209632004227)
  ·
    refine ⟨270855273310705814448006341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 180570182207137209632004227 270855273310705814448006341)
    ·
      refine ⟨50785363745757340209001189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 270855273310705814448006341 50785363745757340209001189)
      ·
        refine ⟨9522255702329501289187723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 50785363745757340209001189 9522255702329501289187723)
        ·
          refine ⟨14283383553494251933781585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9522255702329501289187723 14283383553494251933781585)
          ·
            refine ⟨10712537665120688950336189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14283383553494251933781585 10712537665120688950336189)
            ·
              refine ⟨4017201624420258356376071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10712537665120688950336189 4017201624420258356376071)
              ·
                refine ⟨6025802436630387534564107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4017201624420258356376071 6025802436630387534564107)
                ·
                  refine ⟨9038703654945581301846161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6025802436630387534564107 9038703654945581301846161)
                  ·
                    refine ⟨6779027741209185976384621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9038703654945581301846161 6779027741209185976384621)
                    ·
                      refine ⟨2542135402953444741144233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6779027741209185976384621 2542135402953444741144233)
                      ·
                        rfl

theorem cell23_4950791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 2, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 2, 3, 1, 1, 2, 3].length) (baseStart_4950791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4950791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4950791 prefixEnd_4950791 := by exact prefixLift 4950791
  have htrace : WordTrace (prefixWord ++ tailWord_4950791) baseStart_4950791 baseEnd_4950791 := by
    simpa [prefixWord, tailWord_4950791, baseEnd_4950791] using wordTrace_append hprefix tailTrace_4950791
  have hstable : (prefixWord ++ tailWord_4950791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4950791).length < 2 ^ (prefixWord ++ tailWord_4950791).sum := by decide
  have hdescent : baseEnd_4950791 < baseStart_4950791 := by decide
  rcases family_descends (prefixWord ++ tailWord_4950791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4950810 : List Nat := [3, 1, 1, 3, 2, 1, 1, 1, 1, 5, 4]
def baseStart_4950810 : Nat := 118140960795 + 4950810 * 2 ^ 59
def prefixEnd_4950810 : Nat := 4983230072969 + 3 ^ 40 * 4950810 * 2
def baseEnd_4950810 : Nat := 2542145159085880166806645

theorem tailTrace_4950810 : CollatzResearch.WordTrace tailWord_4950810 prefixEnd_4950810 2542145159085880166806645 := by
  unfold tailWord_4950810
  simp only [CollatzResearch.WordTrace]
  refine ⟨45142718798517093969236471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 120380583462712250584630589 45142718798517093969236471)
  ·
    refine ⟨67714078197775640953854707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45142718798517093969236471 67714078197775640953854707)
    ·
      refine ⟨101571117296663461430782061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67714078197775640953854707 101571117296663461430782061)
      ·
        refine ⟨38089168986248798036543273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 101571117296663461430782061 38089168986248798036543273)
        ·
          refine ⟨28566876739686598527407455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38089168986248798036543273 28566876739686598527407455)
          ·
            refine ⟨42850315109529897791111183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28566876739686598527407455 42850315109529897791111183)
            ·
              refine ⟨64275472664294846686666775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42850315109529897791111183 64275472664294846686666775)
              ·
                refine ⟨96413208996442270030000163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 64275472664294846686666775 96413208996442270030000163)
                ·
                  refine ⟨144619813494663405045000245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 96413208996442270030000163 144619813494663405045000245)
                  ·
                    refine ⟨13558107515124694222968773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 144619813494663405045000245 13558107515124694222968773)
                    ·
                      refine ⟨2542145159085880166806645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13558107515124694222968773 2542145159085880166806645)
                      ·
                        rfl

theorem cell23_4950810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 1, 1, 1, 5, 4].length) (baseStart_4950810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4950810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4950810 prefixEnd_4950810 := by exact prefixLift 4950810
  have htrace : WordTrace (prefixWord ++ tailWord_4950810) baseStart_4950810 baseEnd_4950810 := by
    simpa [prefixWord, tailWord_4950810, baseEnd_4950810] using wordTrace_append hprefix tailTrace_4950810
  have hstable : (prefixWord ++ tailWord_4950810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4950810).length < 2 ^ (prefixWord ++ tailWord_4950810).sum := by decide
  have hdescent : baseEnd_4950810 < baseStart_4950810 := by decide
  rcases family_descends (prefixWord ++ tailWord_4950810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4950827 : List Nat := [1, 1, 1, 1, 2, 1, 2, 7, 1, 4, 2]
def baseStart_4950827 : Nat := 118140960795 + 4950827 * 2 ^ 59
def prefixEnd_4950827 : Nat := 4983230072969 + 3 ^ 40 * 4950827 * 2
def baseEnd_4950827 : Nat := 2542153888257006600294067

theorem tailTrace_4950827 : CollatzResearch.WordTrace tailWord_4950827 prefixEnd_4950827 2542153888257006600294067 := by
  unfold tailWord_4950827
  simp only [CollatzResearch.WordTrace]
  refine ⟨180571495235006787780314735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120380996823337858520209823 180571495235006787780314735)
  ·
    refine ⟨270857242852510181670472103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 180571495235006787780314735 270857242852510181670472103)
    ·
      refine ⟨406285864278765272505708155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 270857242852510181670472103 406285864278765272505708155)
      ·
        refine ⟨609428796418147908758562233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 406285864278765272505708155 609428796418147908758562233)
        ·
          refine ⟨457071597313610931568921675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 609428796418147908758562233 457071597313610931568921675)
          ·
            refine ⟨685607395970416397353382513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 457071597313610931568921675 685607395970416397353382513)
            ·
              refine ⟨514205546977812298015036885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 685607395970416397353382513 514205546977812298015036885)
              ·
                refine ⟨12051692507292475734727427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 514205546977812298015036885 12051692507292475734727427)
                ·
                  refine ⟨18077538760938713602091141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12051692507292475734727427 18077538760938713602091141)
                  ·
                    refine ⟨3389538517676008800392089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18077538760938713602091141 3389538517676008800392089)
                    ·
                      refine ⟨2542153888257006600294067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3389538517676008800392089 2542153888257006600294067)
                      ·
                        rfl

theorem cell23_4950827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 7, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 7, 1, 4, 2].length) (baseStart_4950827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4950827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4950827 prefixEnd_4950827 := by exact prefixLift 4950827
  have htrace : WordTrace (prefixWord ++ tailWord_4950827) baseStart_4950827 baseEnd_4950827 := by
    simpa [prefixWord, tailWord_4950827, baseEnd_4950827] using wordTrace_append hprefix tailTrace_4950827
  have hstable : (prefixWord ++ tailWord_4950827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4950827).length < 2 ^ (prefixWord ++ tailWord_4950827).sum := by decide
  have hdescent : baseEnd_4950827 < baseStart_4950827 := by decide
  rcases family_descends (prefixWord ++ tailWord_4950827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4950840 : List Nat := [2, 1, 2, 1, 3, 2, 1, 2, 1, 4, 4]
def baseStart_4950840 : Nat := 118140960795 + 4950840 * 2 ^ 59
def prefixEnd_4950840 : Nat := 4983230072969 + 3 ^ 40 * 4950840 * 2
def baseEnd_4950840 : Nat := 2542160563505515049431507

theorem tailTrace_4950840 : CollatzResearch.WordTrace tailWord_4950840 prefixEnd_4950840 2542160563505515049431507 := by
  unfold tailWord_4950840
  simp only [CollatzResearch.WordTrace]
  refine ⟨90285984691979845500268987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120381312922639794000358649 90285984691979845500268987)
  ·
    refine ⟨135428977037969768250403481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90285984691979845500268987 135428977037969768250403481)
    ·
      refine ⟨101571732778477326187802611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 135428977037969768250403481 101571732778477326187802611)
      ·
        refine ⟨152357599167715989281703917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101571732778477326187802611 152357599167715989281703917)
        ·
          refine ⟨57134099687893495980638969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 152357599167715989281703917 57134099687893495980638969)
          ·
            refine ⟨42850574765920121985479227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57134099687893495980638969 42850574765920121985479227)
            ·
              refine ⟨64275862148880182978218841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42850574765920121985479227 64275862148880182978218841)
              ·
                refine ⟨48206896611660137233664131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 64275862148880182978218841 48206896611660137233664131)
                ·
                  refine ⟨72310344917490205850496197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 48206896611660137233664131 72310344917490205850496197)
                  ·
                    refine ⟨13558189672029413596968037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 72310344917490205850496197 13558189672029413596968037)
                    ·
                      refine ⟨2542160563505515049431507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13558189672029413596968037 2542160563505515049431507)
                      ·
                        rfl

theorem cell23_4950840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 1, 2, 1, 4, 4].length) (baseStart_4950840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4950840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4950840 prefixEnd_4950840 := by exact prefixLift 4950840
  have htrace : WordTrace (prefixWord ++ tailWord_4950840) baseStart_4950840 baseEnd_4950840 := by
    simpa [prefixWord, tailWord_4950840, baseEnd_4950840] using wordTrace_append hprefix tailTrace_4950840
  have hstable : (prefixWord ++ tailWord_4950840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4950840).length < 2 ^ (prefixWord ++ tailWord_4950840).sum := by decide
  have hdescent : baseEnd_4950840 < baseStart_4950840 := by decide
  rcases family_descends (prefixWord ++ tailWord_4950840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4950844 : List Nat := [2, 2, 2, 2, 1, 1, 1, 4, 4, 2, 2]
def baseStart_4950844 : Nat := 118140960795 + 4950844 * 2 ^ 59
def prefixEnd_4950844 : Nat := 4983230072969 + 3 ^ 40 * 4950844 * 2
def baseEnd_4950844 : Nat := 2542162617428133033781489

theorem tailTrace_4950844 : CollatzResearch.WordTrace tailWord_4950844 prefixEnd_4950844 2542162617428133033781489 := by
  unfold tailWord_4950844
  simp only [CollatzResearch.WordTrace]
  refine ⟨90286057637972599841841793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120381410183963466455789057 90286057637972599841841793)
  ·
    refine ⟨67714543228479449881381345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90286057637972599841841793 67714543228479449881381345)
    ·
      refine ⟨50785907421359587411036009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67714543228479449881381345 50785907421359587411036009)
      ·
        refine ⟨38089430566019690558277007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50785907421359587411036009 38089430566019690558277007)
        ·
          refine ⟨57134145849029535837415511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38089430566019690558277007 57134145849029535837415511)
          ·
            refine ⟨85701218773544303756123267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57134145849029535837415511 85701218773544303756123267)
            ·
              refine ⟨128551828160316455634184901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 85701218773544303756123267 128551828160316455634184901)
              ·
                refine ⟨24103467780059335431409669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 128551828160316455634184901 24103467780059335431409669)
                ·
                  refine ⟨4519400208761125393389313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24103467780059335431409669 4519400208761125393389313)
                  ·
                    refine ⟨3389550156570844045041985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4519400208761125393389313 3389550156570844045041985)
                    ·
                      refine ⟨2542162617428133033781489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3389550156570844045041985 2542162617428133033781489)
                      ·
                        rfl

theorem cell23_4950844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 4, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 4, 4, 2, 2].length) (baseStart_4950844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4950844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4950844 prefixEnd_4950844 := by exact prefixLift 4950844
  have htrace : WordTrace (prefixWord ++ tailWord_4950844) baseStart_4950844 baseEnd_4950844 := by
    simpa [prefixWord, tailWord_4950844, baseEnd_4950844] using wordTrace_append hprefix tailTrace_4950844
  have hstable : (prefixWord ++ tailWord_4950844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4950844).length < 2 ^ (prefixWord ++ tailWord_4950844).sum := by decide
  have hdescent : baseEnd_4950844 < baseStart_4950844 := by decide
  rcases family_descends (prefixWord ++ tailWord_4950844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4950880 : List Nat := [2, 1, 1, 3, 3, 1, 1, 1, 3, 7]
def baseStart_4950880 : Nat := 118140960795 + 4950880 * 2 ^ 59
def prefixEnd_4950880 : Nat := 4983230072969 + 3 ^ 40 * 4950880 * 2
def baseEnd_4950880 : Nat := 847393700910564964310441

theorem tailTrace_4950880 : CollatzResearch.WordTrace tailWord_4950880 prefixEnd_4950880 847393700910564964310441 := by
  unfold tailWord_4950880
  simp only [CollatzResearch.WordTrace]
  refine ⟨90286714151907388915997047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120382285535876518554662729 90286714151907388915997047)
  ·
    refine ⟨135430071227861083373995571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90286714151907388915997047 135430071227861083373995571)
    ·
      refine ⟨203145106841791625060993357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 135430071227861083373995571 203145106841791625060993357)
      ·
        refine ⟨76179415065671859397872509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 203145106841791625060993357 76179415065671859397872509)
        ·
          refine ⟨28567280649626947274202191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 76179415065671859397872509 28567280649626947274202191)
          ·
            refine ⟨42850920974440420911303287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28567280649626947274202191 42850920974440420911303287)
            ·
              refine ⟨64276381461660631366954931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42850920974440420911303287 64276381461660631366954931)
              ·
                refine ⟨96414572192490947050432397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 64276381461660631366954931 96414572192490947050432397)
                ·
                  refine ⟨36155464572184105143912149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 96414572192490947050432397 36155464572184105143912149)
                  ·
                    refine ⟨847393700910564964310441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 36155464572184105143912149 847393700910564964310441)
                    ·
                      rfl

theorem cell23_4950880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 1, 1, 3, 7].length) (baseStart_4950880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4950880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4950880 prefixEnd_4950880 := by exact prefixLift 4950880
  have htrace : WordTrace (prefixWord ++ tailWord_4950880) baseStart_4950880 baseEnd_4950880 := by
    simpa [prefixWord, tailWord_4950880, baseEnd_4950880] using wordTrace_append hprefix tailTrace_4950880
  have hstable : (prefixWord ++ tailWord_4950880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4950880).length < 2 ^ (prefixWord ++ tailWord_4950880).sum := by decide
  have hdescent : baseEnd_4950880 < baseStart_4950880 := by decide
  rcases family_descends (prefixWord ++ tailWord_4950880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4950901 : List Nat := [1, 3, 4, 1, 1, 4, 1, 3, 5]
def baseStart_4950901 : Nat := 118140960795 + 4950901 * 2 ^ 59
def prefixEnd_4950901 : Nat := 4983230072969 + 3 ^ 40 * 4950901 * 2
def baseEnd_4950901 : Nat := 282465765091715478974303

theorem tailTrace_4950901 : CollatzResearch.WordTrace tailWord_4950901 prefixEnd_4950901 282465765091715478974303 := by
  unfold tailWord_4950901
  simp only [CollatzResearch.WordTrace]
  refine ⟨180574194236738698418508557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120382796157825798945672371 180574194236738698418508557)
  ·
    refine ⟨67715322838777011906940709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 180574194236738698418508557 67715322838777011906940709)
    ·
      refine ⟨12696623032270689732551383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 67715322838777011906940709 12696623032270689732551383)
      ·
        refine ⟨19044934548406034598827075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12696623032270689732551383 19044934548406034598827075)
        ·
          refine ⟨28567401822609051898240613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19044934548406034598827075 28567401822609051898240613)
          ·
            refine ⟨5356387841739197230920115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 28567401822609051898240613 5356387841739197230920115)
            ·
              refine ⟨8034581762608795846380173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5356387841739197230920115 8034581762608795846380173)
              ·
                refine ⟨3012968160978298442392565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8034581762608795846380173 3012968160978298442392565)
                ·
                  refine ⟨282465765091715478974303, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3012968160978298442392565 282465765091715478974303)
                  ·
                    rfl

theorem cell23_4950901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 4, 1, 3, 5].length) (baseStart_4950901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4950901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4950901 prefixEnd_4950901 := by exact prefixLift 4950901
  have htrace : WordTrace (prefixWord ++ tailWord_4950901) baseStart_4950901 baseEnd_4950901 := by
    simpa [prefixWord, tailWord_4950901, baseEnd_4950901] using wordTrace_append hprefix tailTrace_4950901
  have hstable : (prefixWord ++ tailWord_4950901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4950901).length < 2 ^ (prefixWord ++ tailWord_4950901).sum := by decide
  have hdescent : baseEnd_4950901 < baseStart_4950901 := by decide
  rcases family_descends (prefixWord ++ tailWord_4950901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4950917 : List Nat := [1, 3, 1, 1, 3, 3, 1, 1, 4, 1, 4]
def baseStart_4950917 : Nat := 118140960795 + 4950917 * 2 ^ 59
def prefixEnd_4950917 : Nat := 4983230072969 + 3 ^ 40 * 4950917 * 2
def baseEnd_4950917 : Nat := 2542200101515911248168653

theorem tailTrace_4950917 : CollatzResearch.WordTrace tailWord_4950917 prefixEnd_4950917 2542200101515911248168653 := by
  unfold tailWord_4950917
  simp only [CollatzResearch.WordTrace]
  refine ⟨180574777804680733151091005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120383185203120488767394003 180574777804680733151091005)
  ·
    refine ⟨67715541676755274931659127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 180574777804680733151091005 67715541676755274931659127)
    ·
      refine ⟨101573312515132912397488691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67715541676755274931659127 101573312515132912397488691)
      ·
        refine ⟨152359968772699368596233037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101573312515132912397488691 152359968772699368596233037)
        ·
          refine ⟨57134988289762263223587389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 152359968772699368596233037 57134988289762263223587389)
          ·
            refine ⟨21425620608660848708845271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 57134988289762263223587389 21425620608660848708845271)
            ·
              refine ⟨32138430912991273063267907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21425620608660848708845271 32138430912991273063267907)
              ·
                refine ⟨48207646369486909594901861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32138430912991273063267907 48207646369486909594901861)
                ·
                  refine ⟨9038933694278795549044099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 48207646369486909594901861 9038933694278795549044099)
                  ·
                    refine ⟨13558400541418193323566149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9038933694278795549044099 13558400541418193323566149)
                    ·
                      refine ⟨2542200101515911248168653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13558400541418193323566149 2542200101515911248168653)
                      ·
                        rfl

theorem cell23_4950917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 1, 1, 4, 1, 4].length) (baseStart_4950917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4950917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4950917 prefixEnd_4950917 := by exact prefixLift 4950917
  have htrace : WordTrace (prefixWord ++ tailWord_4950917) baseStart_4950917 baseEnd_4950917 := by
    simpa [prefixWord, tailWord_4950917, baseEnd_4950917] using wordTrace_append hprefix tailTrace_4950917
  have hstable : (prefixWord ++ tailWord_4950917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4950917).length < 2 ^ (prefixWord ++ tailWord_4950917).sum := by decide
  have hdescent : baseEnd_4950917 < baseStart_4950917 := by decide
  rcases family_descends (prefixWord ++ tailWord_4950917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4950937 : List Nat := [1, 2, 1, 2, 1, 3, 1, 1, 6, 2, 3]
def baseStart_4950937 : Nat := 118140960795 + 4950937 * 2 ^ 59
def prefixEnd_4950937 : Nat := 4983230072969 + 3 ^ 40 * 4950937 * 2
def baseEnd_4950937 : Nat := 2542210371129001169918561

theorem tailTrace_4950937 : CollatzResearch.WordTrace tailWord_4950937 prefixEnd_4950937 2542210371129001169918561 := by
  unfold tailWord_4950937
  simp only [CollatzResearch.WordTrace]
  refine ⟨180575507264608276566819065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120383671509738851044546043 180575507264608276566819065)
  ·
    refine ⟨135431630448456207425114299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 180575507264608276566819065 135431630448456207425114299)
    ·
      refine ⟨203147445672684311137671449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 135431630448456207425114299 203147445672684311137671449)
      ·
        refine ⟨152360584254513233353253587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 203147445672684311137671449 152360584254513233353253587)
        ·
          refine ⟨228540876381769850029880381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 152360584254513233353253587 228540876381769850029880381)
          ·
            refine ⟨85702828643163693761205143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 228540876381769850029880381 85702828643163693761205143)
            ·
              refine ⟨128554242964745540641807715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 85702828643163693761205143 128554242964745540641807715)
              ·
                refine ⟨192831364447118310962711573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 128554242964745540641807715 192831364447118310962711573)
                ·
                  refine ⟨9038970208458670826377105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 192831364447118310962711573 9038970208458670826377105)
                  ·
                    refine ⟨6779227656344003119782829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9038970208458670826377105 6779227656344003119782829)
                    ·
                      refine ⟨2542210371129001169918561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6779227656344003119782829 2542210371129001169918561)
                      ·
                        rfl

theorem cell23_4950937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 1, 6, 2, 3].length) (baseStart_4950937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4950937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4950937 prefixEnd_4950937 := by exact prefixLift 4950937
  have htrace : WordTrace (prefixWord ++ tailWord_4950937) baseStart_4950937 baseEnd_4950937 := by
    simpa [prefixWord, tailWord_4950937, baseEnd_4950937] using wordTrace_append hprefix tailTrace_4950937
  have hstable : (prefixWord ++ tailWord_4950937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4950937).length < 2 ^ (prefixWord ++ tailWord_4950937).sum := by decide
  have hdescent : baseEnd_4950937 < baseStart_4950937 := by decide
  rcases family_descends (prefixWord ++ tailWord_4950937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4950951 : List Nat := [1, 1, 6, 1, 3, 1, 2, 1, 2, 1, 4]
def baseStart_4950951 : Nat := 118140960795 + 4950951 * 2 ^ 59
def prefixEnd_4950951 : Nat := 4983230072969 + 3 ^ 40 * 4950951 * 2
def baseEnd_4950951 : Nat := 2542217559858164115143497

theorem tailTrace_4950951 : CollatzResearch.WordTrace tailWord_4950951 prefixEnd_4950951 2542217559858164115143497 := by
  unfold tailWord_4950951
  simp only [CollatzResearch.WordTrace]
  refine ⟨180576017886557556957828707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120384011924371704638552471 180576017886557556957828707)
  ·
    refine ⟨270864026829836335436743061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 180576017886557556957828707 270864026829836335436743061)
    ·
      refine ⟨12696751257648578223597331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 270864026829836335436743061 12696751257648578223597331)
      ·
        refine ⟨19045126886472867335395997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12696751257648578223597331 19045126886472867335395997)
        ·
          refine ⟨7141922582427325250773499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19045126886472867335395997 7141922582427325250773499)
          ·
            refine ⟨10712883873640987876160249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7141922582427325250773499 10712883873640987876160249)
            ·
              refine ⟨8034662905230740907120187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10712883873640987876160249 8034662905230740907120187)
              ·
                refine ⟨12051994357846111360680281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8034662905230740907120187 12051994357846111360680281)
                ·
                  refine ⟨9038995768384583520510211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12051994357846111360680281 9038995768384583520510211)
                  ·
                    refine ⟨13558493652576875280765317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9038995768384583520510211 13558493652576875280765317)
                    ·
                      refine ⟨2542217559858164115143497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13558493652576875280765317 2542217559858164115143497)
                      ·
                        rfl

theorem cell23_4950951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 1, 2, 1, 2, 1, 4].length) (baseStart_4950951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4950951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4950951 prefixEnd_4950951 := by exact prefixLift 4950951
  have htrace : WordTrace (prefixWord ++ tailWord_4950951) baseStart_4950951 baseEnd_4950951 := by
    simpa [prefixWord, tailWord_4950951, baseEnd_4950951] using wordTrace_append hprefix tailTrace_4950951
  have hstable : (prefixWord ++ tailWord_4950951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4950951).length < 2 ^ (prefixWord ++ tailWord_4950951).sum := by decide
  have hdescent : baseEnd_4950951 < baseStart_4950951 := by decide
  rcases family_descends (prefixWord ++ tailWord_4950951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4950974 : List Nat := [4, 2, 1, 1, 1, 2, 4, 2, 6]
def baseStart_4950974 : Nat := 118140960795 + 4950974 * 2 ^ 59
def prefixEnd_4950974 : Nat := 4983230072969 + 3 ^ 40 * 4950974 * 2
def baseEnd_4950974 : Nat := 282469929990357502795099

theorem tailTrace_4950974 : CollatzResearch.WordTrace tailWord_4950974 prefixEnd_4950974 282469929990357502795099 := by
  unfold tailWord_4950974
  simp only [CollatzResearch.WordTrace]
  refine ⟨22572107095684278985739497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 120384571176982821257277317 22572107095684278985739497)
  ·
    refine ⟨16929080321763209239304623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22572107095684278985739497 16929080321763209239304623)
    ·
      refine ⟨25393620482644813858956935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16929080321763209239304623 25393620482644813858956935)
      ·
        refine ⟨38090430723967220788435403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25393620482644813858956935 38090430723967220788435403)
        ·
          refine ⟨57135646085950831182653105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38090430723967220788435403 57135646085950831182653105)
          ·
            refine ⟨42851734564463123386989829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57135646085950831182653105 42851734564463123386989829)
            ·
              refine ⟨8034700230836835635060593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 42851734564463123386989829 8034700230836835635060593)
              ·
                refine ⟨6026025173127626726295445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8034700230836835635060593 6026025173127626726295445)
                ·
                  refine ⟨282469929990357502795099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6026025173127626726295445 282469929990357502795099)
                  ·
                    rfl

theorem cell23_4950974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 4, 2, 6].length) (baseStart_4950974 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4950974 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4950974 prefixEnd_4950974 := by exact prefixLift 4950974
  have htrace : WordTrace (prefixWord ++ tailWord_4950974) baseStart_4950974 baseEnd_4950974 := by
    simpa [prefixWord, tailWord_4950974, baseEnd_4950974] using wordTrace_append hprefix tailTrace_4950974
  have hstable : (prefixWord ++ tailWord_4950974).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4950974).length < 2 ^ (prefixWord ++ tailWord_4950974).sum := by decide
  have hdescent : baseEnd_4950974 < baseStart_4950974 := by decide
  rcases family_descends (prefixWord ++ tailWord_4950974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4950987 : List Nat := [1, 1, 1, 1, 3, 5, 1, 2, 3, 5]
def baseStart_4950987 : Nat := 118140960795 + 4950987 * 2 ^ 59
def prefixEnd_4950987 : Nat := 4983230072969 + 3 ^ 40 * 4950987 * 2
def baseEnd_4950987 : Nat := 847412015053908658097777

theorem tailTrace_4950987 : CollatzResearch.WordTrace tailWord_4950987 prefixEnd_4950987 847412015053908658097777 := by
  unfold tailWord_4950987
  simp only [CollatzResearch.WordTrace]
  refine ⟨180577330914427135106139215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120384887276284756737426143 180577330914427135106139215)
  ·
    refine ⟨270865996371640702659208823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 180577330914427135106139215 270865996371640702659208823)
    ·
      refine ⟨406298994557461053988813235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 270865996371640702659208823 406298994557461053988813235)
      ·
        refine ⟨609448491836191580983219853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 406298994557461053988813235 609448491836191580983219853)
        ·
          refine ⟨228543184438571842868707445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 609448491836191580983219853 228543184438571842868707445)
          ·
            refine ⟨21425923541116110268941323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 228543184438571842868707445 21425923541116110268941323)
            ·
              refine ⟨32138885311674165403411985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21425923541116110268941323 32138885311674165403411985)
              ·
                refine ⟨24104163983755624052558989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32138885311674165403411985 24104163983755624052558989)
                ·
                  refine ⟨9039061493908359019709621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24104163983755624052558989 9039061493908359019709621)
                  ·
                    refine ⟨847412015053908658097777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9039061493908359019709621 847412015053908658097777)
                    ·
                      rfl

theorem cell23_4950987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 1, 2, 3, 5].length) (baseStart_4950987 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4950987 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4950987 prefixEnd_4950987 := by exact prefixLift 4950987
  have htrace : WordTrace (prefixWord ++ tailWord_4950987) baseStart_4950987 baseEnd_4950987 := by
    simpa [prefixWord, tailWord_4950987, baseEnd_4950987] using wordTrace_append hprefix tailTrace_4950987
  have hstable : (prefixWord ++ tailWord_4950987).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4950987).length < 2 ^ (prefixWord ++ tailWord_4950987).sum := by decide
  have hdescent : baseEnd_4950987 < baseStart_4950987 := by decide
  rcases family_descends (prefixWord ++ tailWord_4950987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4951001 : List Nat := [1, 2, 1, 2, 5, 2, 1, 2, 3, 1, 3]
def baseStart_4951001 : Nat := 118140960795 + 4951001 * 2 ^ 59
def prefixEnd_4951001 : Nat := 4983230072969 + 3 ^ 40 * 4951001 * 2
def baseEnd_4951001 : Nat := 2542243233890888919518267

theorem tailTrace_4951001 : CollatzResearch.WordTrace tailWord_4951001 prefixEnd_4951001 2542243233890888919518267 := by
  unfold tailWord_4951001
  simp only [CollatzResearch.WordTrace]
  refine ⟨180577841536376415497148857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120385227690917610331432571 180577841536376415497148857)
  ·
    refine ⟨135433381152282311622861643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 180577841536376415497148857 135433381152282311622861643)
    ·
      refine ⟨203150071728423467434292465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 135433381152282311622861643 203150071728423467434292465)
      ·
        refine ⟨152362553796317600575719349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 203150071728423467434292465 152362553796317600575719349)
        ·
          refine ⟨14283989418404775053973689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 152362553796317600575719349 14283989418404775053973689)
          ·
            refine ⟨10712992063803581290480267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14283989418404775053973689 10712992063803581290480267)
            ·
              refine ⟨16069488095705371935720401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10712992063803581290480267 16069488095705371935720401)
              ·
                refine ⟨12052116071779028951790301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16069488095705371935720401 12052116071779028951790301)
                ·
                  refine ⟨4519543526917135856921363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12052116071779028951790301 4519543526917135856921363)
                  ·
                    refine ⟨6779315290375703785382045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4519543526917135856921363 6779315290375703785382045)
                    ·
                      refine ⟨2542243233890888919518267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6779315290375703785382045 2542243233890888919518267)
                      ·
                        rfl

theorem cell23_4951001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 2, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 2, 1, 2, 3, 1, 3].length) (baseStart_4951001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4951001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4951001 prefixEnd_4951001 := by exact prefixLift 4951001
  have htrace : WordTrace (prefixWord ++ tailWord_4951001) baseStart_4951001 baseEnd_4951001 := by
    simpa [prefixWord, tailWord_4951001, baseEnd_4951001] using wordTrace_append hprefix tailTrace_4951001
  have hstable : (prefixWord ++ tailWord_4951001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4951001).length < 2 ^ (prefixWord ++ tailWord_4951001).sum := by decide
  have hdescent : baseEnd_4951001 < baseStart_4951001 := by decide
  rcases family_descends (prefixWord ++ tailWord_4951001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4951018 : List Nat := [3, 1, 3, 1, 2, 2, 1, 5, 1, 1, 3]
def baseStart_4951018 : Nat := 118140960795 + 4951018 * 2 ^ 59
def prefixEnd_4951018 : Nat := 4983230072969 + 3 ^ 40 * 4951018 * 2
def baseEnd_4951018 : Nat := 2542251963062015353005689

theorem tailTrace_4951018 : CollatzResearch.WordTrace tailWord_4951018 prefixEnd_4951018 2542251963062015353005689 := by
  unfold tailWord_4951018
  simp only [CollatzResearch.WordTrace]
  refine ⟨45144615394328706850129427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 120385641051543218267011805 45144615394328706850129427)
  ·
    refine ⟨67716923091493060275194141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45144615394328706850129427 67716923091493060275194141)
    ·
      refine ⟨25393846159309897603197803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 67716923091493060275194141 25393846159309897603197803)
      ·
        refine ⟨38090769238964846404796705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25393846159309897603197803 38090769238964846404796705)
        ·
          refine ⟨28568076929223634803597529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38090769238964846404796705 28568076929223634803597529)
          ·
            refine ⟨21426057696917726102698147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28568076929223634803597529 21426057696917726102698147)
            ·
              refine ⟨32139086545376589154047221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21426057696917726102698147 32139086545376589154047221)
              ·
                refine ⟨3013039363629055233191927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 32139086545376589154047221 3013039363629055233191927)
                ·
                  refine ⟨4519559045443582849787891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3013039363629055233191927 4519559045443582849787891)
                  ·
                    refine ⟨6779338568165374274681837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4519559045443582849787891 6779338568165374274681837)
                    ·
                      refine ⟨2542251963062015353005689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6779338568165374274681837 2542251963062015353005689)
                      ·
                        rfl

theorem cell23_4951018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 1, 5, 1, 1, 3].length) (baseStart_4951018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4951018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4951018 prefixEnd_4951018 := by exact prefixLift 4951018
  have htrace : WordTrace (prefixWord ++ tailWord_4951018) baseStart_4951018 baseEnd_4951018 := by
    simpa [prefixWord, tailWord_4951018, baseEnd_4951018] using wordTrace_append hprefix tailTrace_4951018
  have hstable : (prefixWord ++ tailWord_4951018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4951018).length < 2 ^ (prefixWord ++ tailWord_4951018).sum := by decide
  have hdescent : baseEnd_4951018 < baseStart_4951018 := by decide
  rcases family_descends (prefixWord ++ tailWord_4951018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4951037 : List Nat := [1, 4, 1, 1, 1, 2, 1, 4, 1, 1, 6]
def baseStart_4951037 : Nat := 118140960795 + 4951037 * 2 ^ 59
def prefixEnd_4951037 : Nat := 4983230072969 + 3 ^ 40 * 4951037 * 2
def baseEnd_4951037 : Nat := 2542261719194450778668101

theorem tailTrace_4951037 : CollatzResearch.WordTrace tailWord_4951037 prefixEnd_4951037 2542261719194450778668101 := by
  unfold tailWord_4951037
  simp only [CollatzResearch.WordTrace]
  refine ⟨180579154564245993645459365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120386103042830662430306243 180579154564245993645459365)
  ·
    refine ⟨33858591480796123808523631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 180579154564245993645459365 33858591480796123808523631)
    ·
      refine ⟨50787887221194185712785447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33858591480796123808523631 50787887221194185712785447)
      ·
        refine ⟨76181830831791278569178171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50787887221194185712785447 76181830831791278569178171)
        ·
          refine ⟨114272746247686917853767257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76181830831791278569178171 114272746247686917853767257)
          ·
            refine ⟨85704559685765188390325443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 114272746247686917853767257 85704559685765188390325443)
            ·
              refine ⟨128556839528647782585488165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 85704559685765188390325443 128556839528647782585488165)
              ·
                refine ⟨24104407411621459234779031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 128556839528647782585488165 24104407411621459234779031)
                ·
                  refine ⟨36156611117432188852168547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24104407411621459234779031 36156611117432188852168547)
                  ·
                    refine ⟨54234916676148283278252821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 36156611117432188852168547 54234916676148283278252821)
                    ·
                      refine ⟨2542261719194450778668101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 54234916676148283278252821 2542261719194450778668101)
                      ·
                        rfl

theorem cell23_4951037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 4, 1, 1, 6].length) (baseStart_4951037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4951037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4951037 prefixEnd_4951037 := by exact prefixLift 4951037
  have htrace : WordTrace (prefixWord ++ tailWord_4951037) baseStart_4951037 baseEnd_4951037 := by
    simpa [prefixWord, tailWord_4951037, baseEnd_4951037] using wordTrace_append hprefix tailTrace_4951037
  have hstable : (prefixWord ++ tailWord_4951037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4951037).length < 2 ^ (prefixWord ++ tailWord_4951037).sum := by decide
  have hdescent : baseEnd_4951037 < baseStart_4951037 := by decide
  rcases family_descends (prefixWord ++ tailWord_4951037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4951047 : List Nat := [1, 1, 4, 3, 1, 1, 2, 10]
def baseStart_4951047 : Nat := 118140960795 + 4951047 * 2 ^ 59
def prefixEnd_4951047 : Nat := 4983230072969 + 3 ^ 40 * 4951047 * 2
def baseEnd_4951047 : Nat := 94158031629666508871965

theorem tailTrace_4951047 : CollatzResearch.WordTrace tailWord_4951047 prefixEnd_4951047 94158031629666508871965 := by
  unfold tailWord_4951047
  simp only [CollatzResearch.WordTrace]
  refine ⟨180579519294209765353323395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120386346196139843568882263 180579519294209765353323395)
  ·
    refine ⟨270869278941314648029985093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 180579519294209765353323395 270869278941314648029985093)
    ·
      refine ⟨50787989801496496505622205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 270869278941314648029985093 50787989801496496505622205)
      ·
        refine ⟨19045496175561186189608327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 50787989801496496505622205 19045496175561186189608327)
        ·
          refine ⟨28568244263341779284412491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19045496175561186189608327 28568244263341779284412491)
          ·
            refine ⟨42852366395012668926618737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28568244263341779284412491 42852366395012668926618737)
            ·
              refine ⟨32139274796259501694964053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42852366395012668926618737 32139274796259501694964053)
              ·
                refine ⟨94158031629666508871965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 32139274796259501694964053 94158031629666508871965)
                ·
                  rfl

theorem cell23_4951047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 2, 10].length) (baseStart_4951047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4951047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4951047 prefixEnd_4951047 := by exact prefixLift 4951047
  have htrace : WordTrace (prefixWord ++ tailWord_4951047) baseStart_4951047 baseEnd_4951047 := by
    simpa [prefixWord, tailWord_4951047, baseEnd_4951047] using wordTrace_append hprefix tailTrace_4951047
  have hstable : (prefixWord ++ tailWord_4951047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4951047).length < 2 ^ (prefixWord ++ tailWord_4951047).sum := by decide
  have hdescent : baseEnd_4951047 < baseStart_4951047 := by decide
  rcases family_descends (prefixWord ++ tailWord_4951047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4951054 : List Nat := [4, 1, 1, 2, 2, 3, 1, 1, 1, 1, 6]
def baseStart_4951054 : Nat := 118140960795 + 4951054 * 2 ^ 59
def prefixEnd_4951054 : Nat := 4983230072969 + 3 ^ 40 * 4951054 * 2
def baseEnd_4951054 : Nat := 2542270448365577212155523

theorem tailTrace_4951054 : CollatzResearch.WordTrace tailWord_4951054 prefixEnd_4951054 2542270448365577212155523 := by
  unfold tailWord_4951054
  simp only [CollatzResearch.WordTrace]
  refine ⟨22572471825648050693603527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 120386516403456270365885477 22572471825648050693603527)
  ·
    refine ⟨33858707738472076040405291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22572471825648050693603527 33858707738472076040405291)
    ·
      refine ⟨50788061607708114060607937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33858707738472076040405291 50788061607708114060607937)
      ·
        refine ⟨38091046205781085545455953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50788061607708114060607937 38091046205781085545455953)
        ·
          refine ⟨28568284654335814159091965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38091046205781085545455953 28568284654335814159091965)
          ·
            refine ⟨10713106745375930309659487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28568284654335814159091965 10713106745375930309659487)
            ·
              refine ⟨16069660118063895464489231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10713106745375930309659487 16069660118063895464489231)
              ·
                refine ⟨24104490177095843196733847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16069660118063895464489231 24104490177095843196733847)
                ·
                  refine ⟨36156735265643764795100771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24104490177095843196733847 36156735265643764795100771)
                  ·
                    refine ⟨54235102898465647192651157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 36156735265643764795100771 54235102898465647192651157)
                    ·
                      refine ⟨2542270448365577212155523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 54235102898465647192651157 2542270448365577212155523)
                      ·
                        rfl

theorem cell23_4951054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 3, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 3, 1, 1, 1, 1, 6].length) (baseStart_4951054 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4951054 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4951054 prefixEnd_4951054 := by exact prefixLift 4951054
  have htrace : WordTrace (prefixWord ++ tailWord_4951054) baseStart_4951054 baseEnd_4951054 := by
    simpa [prefixWord, tailWord_4951054, baseEnd_4951054] using wordTrace_append hprefix tailTrace_4951054
  have hstable : (prefixWord ++ tailWord_4951054).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4951054).length < 2 ^ (prefixWord ++ tailWord_4951054).sum := by decide
  have hdescent : baseEnd_4951054 < baseStart_4951054 := by decide
  rcases family_descends (prefixWord ++ tailWord_4951054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4951061 : List Nat := [1, 3, 2, 1, 4, 1, 1, 4, 1, 2, 3]
def baseStart_4951061 : Nat := 118140960795 + 4951061 * 2 ^ 59
def prefixEnd_4951061 : Nat := 4983230072969 + 3 ^ 40 * 4951061 * 2
def baseEnd_4951061 : Nat := 2542274042730158684767991

theorem tailTrace_4951061 : CollatzResearch.WordTrace tailWord_4951061 prefixEnd_4951061 2542274042730158684767991 := by
  unfold tailWord_4951061
  simp only [CollatzResearch.WordTrace]
  refine ⟨180580029916159045744333037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120386686610772697162888691 180580029916159045744333037)
  ·
    refine ⟨67717511218559642154124889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 180580029916159045744333037 67717511218559642154124889)
    ·
      refine ⟨50788133413919731615593667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67717511218559642154124889 50788133413919731615593667)
      ·
        refine ⟨76182200120879597423390501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50788133413919731615593667 76182200120879597423390501)
        ·
          refine ⟨14284162522664924516885719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 76182200120879597423390501 14284162522664924516885719)
          ·
            refine ⟨21426243783997386775328579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14284162522664924516885719 21426243783997386775328579)
            ·
              refine ⟨32139365675996080162992869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21426243783997386775328579 32139365675996080162992869)
              ·
                refine ⟨6026131064249265030561163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 32139365675996080162992869 6026131064249265030561163)
                ·
                  refine ⟨9039196596373897545841745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6026131064249265030561163 9039196596373897545841745)
                  ·
                    refine ⟨6779397447280423159381309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9039196596373897545841745 6779397447280423159381309)
                    ·
                      refine ⟨2542274042730158684767991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6779397447280423159381309 2542274042730158684767991)
                      ·
                        rfl

theorem cell23_4951061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 1, 4, 1, 2, 3].length) (baseStart_4951061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4951061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4951061 prefixEnd_4951061 := by exact prefixLift 4951061
  have htrace : WordTrace (prefixWord ++ tailWord_4951061) baseStart_4951061 baseEnd_4951061 := by
    simpa [prefixWord, tailWord_4951061, baseEnd_4951061] using wordTrace_append hprefix tailTrace_4951061
  have hstable : (prefixWord ++ tailWord_4951061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4951061).length < 2 ^ (prefixWord ++ tailWord_4951061).sum := by decide
  have hdescent : baseEnd_4951061 < baseStart_4951061 := by decide
  rcases family_descends (prefixWord ++ tailWord_4951061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4951064 : List Nat := [2, 1, 2, 3, 2, 2, 4, 7]
def baseStart_4951064 : Nat := 118140960795 + 4951064 * 2 ^ 59
def prefixEnd_4951064 : Nat := 4983230072969 + 3 ^ 40 * 4951064 * 2
def baseEnd_4951064 : Nat := 94158354932300821223351

theorem tailTrace_4951064 : CollatzResearch.WordTrace tailWord_4951064 prefixEnd_4951064 94158354932300821223351 := by
  unfold tailWord_4951064
  simp only [CollatzResearch.WordTrace]
  refine ⟨90290069667574088628346123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120386759556765451504461497 90290069667574088628346123)
  ·
    refine ⟨135435104501361132942519185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90290069667574088628346123 135435104501361132942519185)
    ·
      refine ⟨101576328376020849706889389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 135435104501361132942519185 101576328376020849706889389)
      ·
        refine ⟨38091123141007818640083521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 101576328376020849706889389 38091123141007818640083521)
        ·
          refine ⟨28568342355755863980062641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38091123141007818640083521 28568342355755863980062641)
          ·
            refine ⟨21426256766816897985046981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28568342355755863980062641 21426256766816897985046981)
            ·
              refine ⟨4017423143778168372196309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21426256766816897985046981 4017423143778168372196309)
              ·
                refine ⟨94158354932300821223351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4017423143778168372196309 94158354932300821223351)
                ·
                  rfl

theorem cell23_4951064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 4, 7].length) (baseStart_4951064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4951064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4951064 prefixEnd_4951064 := by exact prefixLift 4951064
  have htrace : WordTrace (prefixWord ++ tailWord_4951064) baseStart_4951064 baseEnd_4951064 := by
    simpa [prefixWord, tailWord_4951064, baseEnd_4951064] using wordTrace_append hprefix tailTrace_4951064
  have hstable : (prefixWord ++ tailWord_4951064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4951064).length < 2 ^ (prefixWord ++ tailWord_4951064).sum := by decide
  have hdescent : baseEnd_4951064 < baseStart_4951064 := by decide
  rcases family_descends (prefixWord ++ tailWord_4951064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4951075 : List Nat := [1, 1, 1, 4, 3, 2, 3, 3, 1, 2, 2]
def baseStart_4951075 : Nat := 118140960795 + 4951075 * 2 ^ 59
def prefixEnd_4951075 : Nat := 4983230072969 + 3 ^ 40 * 4951075 * 2
def baseEnd_4951075 : Nat := 2542281231459321629992927

theorem tailTrace_4951075 : CollatzResearch.WordTrace tailWord_4951075 prefixEnd_4951075 2542281231459321629992927 := by
  unfold tailWord_4951075
  simp only [CollatzResearch.WordTrace]
  refine ⟨180580540538108326135342679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120387027025405550756895119 180580540538108326135342679)
  ·
    refine ⟨270870810807162489203014019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 180580540538108326135342679 270870810807162489203014019)
    ·
      refine ⟨406306216210743733804521029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 270870810807162489203014019 406306216210743733804521029)
      ·
        refine ⟨76182415539514450088347693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 406306216210743733804521029 76182415539514450088347693)
        ·
          refine ⟨28568405827317918783130385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 76182415539514450088347693 28568405827317918783130385)
          ·
            refine ⟨21426304370488439087347789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28568405827317918783130385 21426304370488439087347789)
            ·
              refine ⟨8034864138933164657755421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21426304370488439087347789 8034864138933164657755421)
              ·
                refine ⟨3013074052099936746658283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8034864138933164657755421 3013074052099936746658283)
                ·
                  refine ⟨4519611078149905119987425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3013074052099936746658283 4519611078149905119987425)
                  ·
                    refine ⟨3389708308612428839990569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4519611078149905119987425 3389708308612428839990569)
                    ·
                      refine ⟨2542281231459321629992927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3389708308612428839990569 2542281231459321629992927)
                      ·
                        rfl

theorem cell23_4951075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 3, 3, 1, 2, 2].length) (baseStart_4951075 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4951075 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4951075 prefixEnd_4951075 := by exact prefixLift 4951075
  have htrace : WordTrace (prefixWord ++ tailWord_4951075) baseStart_4951075 baseEnd_4951075 := by
    simpa [prefixWord, tailWord_4951075, baseEnd_4951075] using wordTrace_append hprefix tailTrace_4951075
  have hstable : (prefixWord ++ tailWord_4951075).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4951075).length < 2 ^ (prefixWord ++ tailWord_4951075).sum := by decide
  have hdescent : baseEnd_4951075 < baseStart_4951075 := by decide
  rcases family_descends (prefixWord ++ tailWord_4951075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4951091 : List Nat := [1, 1, 1, 2, 4, 1, 1, 6, 2, 1, 3]
def baseStart_4951091 : Nat := 118140960795 + 4951091 * 2 ^ 59
def prefixEnd_4951091 : Nat := 4983230072969 + 3 ^ 40 * 4951091 * 2
def baseEnd_4951091 : Nat := 2542289447149793567392853

theorem tailTrace_4951091 : CollatzResearch.WordTrace tailWord_4951091 prefixEnd_4951091 2542289447149793567392853 := by
  unfold tailWord_4951091
  simp only [CollatzResearch.WordTrace]
  refine ⟨180581124106050360867925127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120387416070700240578616751 180581124106050360867925127)
  ·
    refine ⟨270871686159075541301887691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 180581124106050360867925127 270871686159075541301887691)
    ·
      refine ⟨406307529238613311952831537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 270871686159075541301887691 406307529238613311952831537)
      ·
        refine ⟨304730646928959983964623653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 406307529238613311952831537 304730646928959983964623653)
        ·
          refine ⟨57136996299179996993366935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 304730646928959983964623653 57136996299179996993366935)
          ·
            refine ⟨85705494448769995490050403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57136996299179996993366935 85705494448769995490050403)
            ·
              refine ⟨128558241673154993235075605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 85705494448769995490050403 128558241673154993235075605)
              ·
                refine ⟨6026167578429140307894169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 128558241673154993235075605 6026167578429140307894169)
                ·
                  refine ⟨4519625683821855230920627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6026167578429140307894169 4519625683821855230920627)
                  ·
                    refine ⟨6779438525732782846380941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4519625683821855230920627 6779438525732782846380941)
                    ·
                      refine ⟨2542289447149793567392853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6779438525732782846380941 2542289447149793567392853)
                      ·
                        rfl

theorem cell23_4951091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 6, 2, 1, 3].length) (baseStart_4951091 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4951091 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4951091 prefixEnd_4951091 := by exact prefixLift 4951091
  have htrace : WordTrace (prefixWord ++ tailWord_4951091) baseStart_4951091 baseEnd_4951091 := by
    simpa [prefixWord, tailWord_4951091, baseEnd_4951091] using wordTrace_append hprefix tailTrace_4951091
  have hstable : (prefixWord ++ tailWord_4951091).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4951091).length < 2 ^ (prefixWord ++ tailWord_4951091).sum := by decide
  have hdescent : baseEnd_4951091 < baseStart_4951091 := by decide
  rcases family_descends (prefixWord ++ tailWord_4951091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4951092 : List Nat := [2, 5, 1, 2, 1, 3, 1, 1, 3, 2, 2]
def baseStart_4951092 : Nat := 118140960795 + 4951092 * 2 ^ 59
def prefixEnd_4951092 : Nat := 4983230072969 + 3 ^ 40 * 4951092 * 2
def baseEnd_4951092 : Nat := 2542289960630448063480349

theorem tailTrace_4951092 : CollatzResearch.WordTrace tailWord_4951092 prefixEnd_4951092 2542289960630448063480349 := by
  unfold tailWord_4951092
  simp only [CollatzResearch.WordTrace]
  refine ⟨90290580289523369019355765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120387440386031158692474353 90290580289523369019355765)
  ·
    refine ⟨8464741902142815845564603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 90290580289523369019355765 8464741902142815845564603)
    ·
      refine ⟨12697112853214223768346905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8464741902142815845564603 12697112853214223768346905)
      ·
        refine ⟨9522834639910667826260179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12697112853214223768346905 9522834639910667826260179)
        ·
          refine ⟨14284251959866001739390269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9522834639910667826260179 14284251959866001739390269)
          ·
            refine ⟨5356594484949750652271351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14284251959866001739390269 5356594484949750652271351)
            ·
              refine ⟨8034891727424625978407027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5356594484949750652271351 8034891727424625978407027)
              ·
                refine ⟨12052337591136938967610541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8034891727424625978407027 12052337591136938967610541)
                ·
                  refine ⟨4519626596676352112853953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12052337591136938967610541 4519626596676352112853953)
                  ·
                    refine ⟨3389719947507264084640465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4519626596676352112853953 3389719947507264084640465)
                    ·
                      refine ⟨2542289960630448063480349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3389719947507264084640465 2542289960630448063480349)
                      ·
                        rfl

theorem cell23_4951092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 3, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 3, 1, 1, 3, 2, 2].length) (baseStart_4951092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4951092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4951092 prefixEnd_4951092 := by exact prefixLift 4951092
  have htrace : WordTrace (prefixWord ++ tailWord_4951092) baseStart_4951092 baseEnd_4951092 := by
    simpa [prefixWord, tailWord_4951092, baseEnd_4951092] using wordTrace_append hprefix tailTrace_4951092
  have hstable : (prefixWord ++ tailWord_4951092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4951092).length < 2 ^ (prefixWord ++ tailWord_4951092).sum := by decide
  have hdescent : baseEnd_4951092 < baseStart_4951092 := by decide
  rcases family_descends (prefixWord ++ tailWord_4951092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4951107 : List Nat := [1, 1, 1, 3, 1, 2, 4, 1, 1, 8]
def baseStart_4951107 : Nat := 118140960795 + 4951107 * 2 ^ 59
def prefixEnd_4951107 : Nat := 4983230072969 + 3 ^ 40 * 4951107 * 2
def baseEnd_4951107 : Nat := 847432554280088501597593

theorem tailTrace_4951107 : CollatzResearch.WordTrace tailWord_4951107 prefixEnd_4951107 847432554280088501597593 := by
  unfold tailWord_4951107
  simp only [CollatzResearch.WordTrace]
  refine ⟨180581707673992395600507575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120387805115994930400338383 180581707673992395600507575)
  ·
    refine ⟨270872561510988593400761363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 180581707673992395600507575 270872561510988593400761363)
    ·
      refine ⟨406308842266482890101142045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 270872561510988593400761363 406308842266482890101142045)
      ·
        refine ⟨152365815849931083787928267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 406308842266482890101142045 152365815849931083787928267)
        ·
          refine ⟨228548723774896625681892401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 152365815849931083787928267 228548723774896625681892401)
          ·
            refine ⟨171411542831172469261419301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 228548723774896625681892401 171411542831172469261419301)
            ·
              refine ⟨32139664280844837986516119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 171411542831172469261419301 32139664280844837986516119)
              ·
                refine ⟨48209496421267256979774179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32139664280844837986516119 48209496421267256979774179)
                ·
                  refine ⟨72314244631900885469661269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 48209496421267256979774179 72314244631900885469661269)
                  ·
                    refine ⟨847432554280088501597593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 72314244631900885469661269 847432554280088501597593)
                    ·
                      rfl

theorem cell23_4951107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 4, 1, 1, 8].length) (baseStart_4951107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4951107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4951107 prefixEnd_4951107 := by exact prefixLift 4951107
  have htrace : WordTrace (prefixWord ++ tailWord_4951107) baseStart_4951107 baseEnd_4951107 := by
    simpa [prefixWord, tailWord_4951107, baseEnd_4951107] using wordTrace_append hprefix tailTrace_4951107
  have hstable : (prefixWord ++ tailWord_4951107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4951107).length < 2 ^ (prefixWord ++ tailWord_4951107).sum := by decide
  have hdescent : baseEnd_4951107 < baseStart_4951107 := by decide
  rcases family_descends (prefixWord ++ tailWord_4951107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4951154 : List Nat := [3, 2, 1, 2, 2, 1, 2, 3, 7]
def baseStart_4951154 : Nat := 118140960795 + 4951154 * 2 ^ 59
def prefixEnd_4951154 : Nat := 4983230072969 + 3 ^ 40 * 4951154 * 2
def baseEnd_4951154 : Nat := 282480199603447424545007

theorem tailTrace_4951154 : CollatzResearch.WordTrace tailWord_4951154 prefixEnd_4951154 282480199603447424545007 := by
  unfold tailWord_4951154
  simp only [CollatzResearch.WordTrace]
  refine ⟨45145855476205530656867129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 120388947936548081751645677 45145855476205530656867129)
  ·
    refine ⟨33859391607154147992650347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45145855476205530656867129 33859391607154147992650347)
    ·
      refine ⟨50789087410731221988975521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33859391607154147992650347 50789087410731221988975521)
      ·
        refine ⟨38091815558048416491731641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50789087410731221988975521 38091815558048416491731641)
        ·
          refine ⟨28568861668536312368798731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38091815558048416491731641 28568861668536312368798731)
          ·
            refine ⟨42853292502804468553198097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28568861668536312368798731 42853292502804468553198097)
            ·
              refine ⟨32139969377103351414898573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42853292502804468553198097 32139969377103351414898573)
              ·
                refine ⟨12052488516413756780586965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32139969377103351414898573 12052488516413756780586965)
                ·
                  refine ⟨282480199603447424545007, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12052488516413756780586965 282480199603447424545007)
                  ·
                    rfl

theorem cell23_4951154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 2, 3, 7].length) (baseStart_4951154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4951154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4951154 prefixEnd_4951154 := by exact prefixLift 4951154
  have htrace : WordTrace (prefixWord ++ tailWord_4951154) baseStart_4951154 baseEnd_4951154 := by
    simpa [prefixWord, tailWord_4951154, baseEnd_4951154] using wordTrace_append hprefix tailTrace_4951154
  have hstable : (prefixWord ++ tailWord_4951154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4951154).length < 2 ^ (prefixWord ++ tailWord_4951154).sum := by decide
  have hdescent : baseEnd_4951154 < baseStart_4951154 := by decide
  rcases family_descends (prefixWord ++ tailWord_4951154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4951161 : List Nat := [1, 2, 1, 3, 5, 1, 1, 1, 2, 2, 4]
def baseStart_4951161 : Nat := 118140960795 + 4951161 * 2 ^ 59
def prefixEnd_4951161 : Nat := 4983230072969 + 3 ^ 40 * 4951161 * 2
def baseEnd_4951161 : Nat := 2542325390795608293517531

theorem tailTrace_4951161 : CollatzResearch.WordTrace tailWord_4951161 prefixEnd_4951161 2542325390795608293517531 := by
  unfold tailWord_4951161
  simp only [CollatzResearch.WordTrace]
  refine ⟨180583677215796762822973337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120389118143864508548648891 180583677215796762822973337)
  ·
    refine ⟨135437757911847572117230003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 180583677215796762822973337 135437757911847572117230003)
    ·
      refine ⟨203156636867771358175845005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 135437757911847572117230003 203156636867771358175845005)
      ·
        refine ⟨76183738825414259315941877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 203156636867771358175845005 76183738825414259315941877)
        ·
          refine ⟨7142225514882586810869551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 76183738825414259315941877 7142225514882586810869551)
          ·
            refine ⟨10713338272323880216304327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7142225514882586810869551 10713338272323880216304327)
            ·
              refine ⟨16070007408485820324456491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10713338272323880216304327 16070007408485820324456491)
              ·
                refine ⟨24105011112728730486684737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16070007408485820324456491 24105011112728730486684737)
                ·
                  refine ⟨18078758334546547865013553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24105011112728730486684737 18078758334546547865013553)
                  ·
                    refine ⟨13559068750909910898760165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18078758334546547865013553 13559068750909910898760165)
                    ·
                      refine ⟨2542325390795608293517531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13559068750909910898760165 2542325390795608293517531)
                      ·
                        rfl

theorem cell23_4951161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 1, 1, 1, 2, 2, 4].length) (baseStart_4951161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4951161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4951161 prefixEnd_4951161 := by exact prefixLift 4951161
  have htrace : WordTrace (prefixWord ++ tailWord_4951161) baseStart_4951161 baseEnd_4951161 := by
    simpa [prefixWord, tailWord_4951161, baseEnd_4951161] using wordTrace_append hprefix tailTrace_4951161
  have hstable : (prefixWord ++ tailWord_4951161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4951161).length < 2 ^ (prefixWord ++ tailWord_4951161).sum := by decide
  have hdescent : baseEnd_4951161 < baseStart_4951161 := by decide
  rcases family_descends (prefixWord ++ tailWord_4951161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4951184 : List Nat := [2, 1, 1, 1, 1, 1, 4, 5, 2, 5]
def baseStart_4951184 : Nat := 118140960795 + 4951184 * 2 ^ 59
def prefixEnd_4951184 : Nat := 4983230072969 + 3 ^ 40 * 4951184 * 2
def baseEnd_4951184 : Nat := 847445733616887234509975

theorem tailTrace_4951184 : CollatzResearch.WordTrace tailWord_4951184 prefixEnd_4951184 847445733616887234509975 := by
  unfold tailWord_4951184
  simp only [CollatzResearch.WordTrace]
  refine ⟨90292258047356718875530303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120389677396475625167373737 90292258047356718875530303)
  ·
    refine ⟨135438387071035078313295455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90292258047356718875530303 135438387071035078313295455)
    ·
      refine ⟨203157580606552617469943183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 135438387071035078313295455 203157580606552617469943183)
      ·
        refine ⟨304736370909828926204914775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 203157580606552617469943183 304736370909828926204914775)
        ·
          refine ⟨457104556364743389307372163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 304736370909828926204914775 457104556364743389307372163)
          ·
            refine ⟨685656834547115083961058245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 457104556364743389307372163 685656834547115083961058245)
            ·
              refine ⟨128560656477584078242698421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 685656834547115083961058245 128560656477584078242698421)
              ·
                refine ⟨12052561544773507335252977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 128560656477584078242698421 12052561544773507335252977)
                ·
                  refine ⟨9039421158580130501439733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12052561544773507335252977 9039421158580130501439733)
                  ·
                    refine ⟨847445733616887234509975, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9039421158580130501439733 847445733616887234509975)
                    ·
                      rfl

theorem cell23_4951184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 5, 2, 5].length) (baseStart_4951184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4951184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4951184 prefixEnd_4951184 := by exact prefixLift 4951184
  have htrace : WordTrace (prefixWord ++ tailWord_4951184) baseStart_4951184 baseEnd_4951184 := by
    simpa [prefixWord, tailWord_4951184, baseEnd_4951184] using wordTrace_append hprefix tailTrace_4951184
  have hstable : (prefixWord ++ tailWord_4951184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4951184).length < 2 ^ (prefixWord ++ tailWord_4951184).sum := by decide
  have hdescent : baseEnd_4951184 < baseStart_4951184 := by decide
  rcases family_descends (prefixWord ++ tailWord_4951184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4951198 : List Nat := [4, 3, 1, 1, 2, 1, 1, 2, 2, 3, 3]
def baseStart_4951198 : Nat := 118140960795 + 4951198 * 2 ^ 59
def prefixEnd_4951198 : Nat := 4983230072969 + 3 ^ 40 * 4951198 * 2
def baseEnd_4951198 : Nat := 2542344389579824648754861

theorem tailTrace_4951198 : CollatzResearch.WordTrace tailWord_4951198 prefixEnd_4951198 2542344389579824648754861 := by
  unfold tailWord_4951198
  simp only [CollatzResearch.WordTrace]
  refine ⟨22573128339582839767758781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 120390017811108478761380165 22573128339582839767758781)
  ·
    refine ⟨8464923127343564912909543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22573128339582839767758781 8464923127343564912909543)
    ·
      refine ⟨12697384691015347369364315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8464923127343564912909543 12697384691015347369364315)
      ·
        refine ⟨19046077036523021054046473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12697384691015347369364315 19046077036523021054046473)
        ·
          refine ⟨14284557777392265790534855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19046077036523021054046473 14284557777392265790534855)
          ·
            refine ⟨21426836666088398685802283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14284557777392265790534855 21426836666088398685802283)
            ·
              refine ⟨32140254999132598028703425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21426836666088398685802283 32140254999132598028703425)
              ·
                refine ⟨24105191249349448521527569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32140254999132598028703425 24105191249349448521527569)
                ·
                  refine ⟨18078893437012086391145677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24105191249349448521527569 18078893437012086391145677)
                  ·
                    refine ⟨6779585038879532396679629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18078893437012086391145677 6779585038879532396679629)
                    ·
                      refine ⟨2542344389579824648754861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6779585038879532396679629 2542344389579824648754861)
                      ·
                        rfl

theorem cell23_4951198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 1, 2, 2, 3, 3].length) (baseStart_4951198 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4951198 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4951198 prefixEnd_4951198 := by exact prefixLift 4951198
  have htrace : WordTrace (prefixWord ++ tailWord_4951198) baseStart_4951198 baseEnd_4951198 := by
    simpa [prefixWord, tailWord_4951198, baseEnd_4951198] using wordTrace_append hprefix tailTrace_4951198
  have hstable : (prefixWord ++ tailWord_4951198).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4951198).length < 2 ^ (prefixWord ++ tailWord_4951198).sum := by decide
  have hdescent : baseEnd_4951198 < baseStart_4951198 := by decide
  rcases family_descends (prefixWord ++ tailWord_4951198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4951199 : List Nat := [1, 1, 2, 6, 3, 1, 1, 2, 2, 2, 2]
def baseStart_4951199 : Nat := 118140960795 + 4951199 * 2 ^ 59
def prefixEnd_4951199 : Nat := 4983230072969 + 3 ^ 40 * 4951199 * 2
def baseEnd_4951199 : Nat := 2542344903060479144842357

theorem tailTrace_4951199 : CollatzResearch.WordTrace tailWord_4951199 prefixEnd_4951199 2542344903060479144842357 := by
  unfold tailWord_4951199
  simp only [CollatzResearch.WordTrace]
  refine ⟨180585063189659095312856651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120390042126439396875237767 180585063189659095312856651)
  ·
    refine ⟨270877594784488642969284977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 180585063189659095312856651 270877594784488642969284977)
    ·
      refine ⟨203158196088366482226963733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 270877594784488642969284977 203158196088366482226963733)
      ·
        refine ⟨9523040441642178854388925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 203158196088366482226963733 9523040441642178854388925)
        ·
          refine ⟨3571140165615817070395847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9523040441642178854388925 3571140165615817070395847)
          ·
            refine ⟨5356710248423725605593771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3571140165615817070395847 5356710248423725605593771)
            ·
              refine ⟨8035065372635588408390657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5356710248423725605593771 8035065372635588408390657)
              ·
                refine ⟨6026299029476691306292993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8035065372635588408390657 6026299029476691306292993)
                ·
                  refine ⟨4519724272107518479719745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6026299029476691306292993 4519724272107518479719745)
                  ·
                    refine ⟨3389793204080638859789809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4519724272107518479719745 3389793204080638859789809)
                    ·
                      refine ⟨2542344903060479144842357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3389793204080638859789809 2542344903060479144842357)
                      ·
                        rfl

theorem cell23_4951199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 3, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 3, 1, 1, 2, 2, 2, 2].length) (baseStart_4951199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4951199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4951199 prefixEnd_4951199 := by exact prefixLift 4951199
  have htrace : WordTrace (prefixWord ++ tailWord_4951199) baseStart_4951199 baseEnd_4951199 := by
    simpa [prefixWord, tailWord_4951199, baseEnd_4951199] using wordTrace_append hprefix tailTrace_4951199
  have hstable : (prefixWord ++ tailWord_4951199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4951199).length < 2 ^ (prefixWord ++ tailWord_4951199).sum := by decide
  have hdescent : baseEnd_4951199 < baseStart_4951199 := by decide
  rcases family_descends (prefixWord ++ tailWord_4951199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4951231 : List Nat := [1, 1, 2, 2, 2, 2, 4, 2, 3, 4]
def baseStart_4951231 : Nat := 118140960795 + 4951231 * 2 ^ 59
def prefixEnd_4951231 : Nat := 4983230072969 + 3 ^ 40 * 4951231 * 2
def baseEnd_4951231 : Nat := 847453778147141006547403

theorem tailTrace_4951231 : CollatzResearch.WordTrace tailWord_4951231 prefixEnd_4951231 847453778147141006547403 := by
  unfold tailWord_4951231
  simp only [CollatzResearch.WordTrace]
  refine ⟨180586230325543164778021547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120390820217028776518681031 180586230325543164778021547)
  ·
    refine ⟨270879345488314747167032321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 180586230325543164778021547 270879345488314747167032321)
    ·
      refine ⟨203159509116236060375274241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 270879345488314747167032321 203159509116236060375274241)
      ·
        refine ⟨152369631837177045281455681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 203159509116236060375274241 152369631837177045281455681)
        ·
          refine ⟨114277223877882783961091761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 152369631837177045281455681 114277223877882783961091761)
          ·
            refine ⟨85707917908412087970818821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 114277223877882783961091761 85707917908412087970818821)
            ·
              refine ⟨16070234607827266494528529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 85707917908412087970818821 16070234607827266494528529)
              ·
                refine ⟨12052675955870449870896397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16070234607827266494528529 12052675955870449870896397)
                ·
                  refine ⟨4519753483451418701586149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12052675955870449870896397 4519753483451418701586149)
                  ·
                    refine ⟨847453778147141006547403, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4519753483451418701586149 847453778147141006547403)
                    ·
                      rfl

theorem cell23_4951231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 4, 2, 3, 4].length) (baseStart_4951231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4951231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4951231 prefixEnd_4951231 := by exact prefixLift 4951231
  have htrace : WordTrace (prefixWord ++ tailWord_4951231) baseStart_4951231 baseEnd_4951231 := by
    simpa [prefixWord, tailWord_4951231, baseEnd_4951231] using wordTrace_append hprefix tailTrace_4951231
  have hstable : (prefixWord ++ tailWord_4951231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4951231).length < 2 ^ (prefixWord ++ tailWord_4951231).sum := by decide
  have hdescent : baseEnd_4951231 < baseStart_4951231 := by decide
  rcases family_descends (prefixWord ++ tailWord_4951231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4951278 : List Nat := [4, 1, 2, 1, 1, 1, 6, 1, 6]
def baseStart_4951278 : Nat := 118140960795 + 4951278 * 2 ^ 59
def prefixEnd_4951278 : Nat := 4983230072969 + 3 ^ 40 * 4951278 * 2
def baseEnd_4951278 : Nat := 282487274225798259528277

theorem tailTrace_4951278 : CollatzResearch.WordTrace tailWord_4951278 prefixEnd_4951278 282487274225798259528277 := by
  unfold tailWord_4951278
  simp only [CollatzResearch.WordTrace]
  refine ⟨22573493069546611475622811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 120391963037581927869988325 22573493069546611475622811)
  ·
    refine ⟨33860239604319917213434217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22573493069546611475622811 33860239604319917213434217)
    ·
      refine ⟨25395179703239937910075663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33860239604319917213434217 25395179703239937910075663)
      ·
        refine ⟨38092769554859906865113495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25395179703239937910075663 38092769554859906865113495)
        ·
          refine ⟨57139154332289860297670243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38092769554859906865113495 57139154332289860297670243)
          ·
            refine ⟨85708731498434790446505365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57139154332289860297670243 85708731498434790446505365)
            ·
              refine ⟨4017596788989130802179939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 85708731498434790446505365 4017596788989130802179939)
              ·
                refine ⟨6026395183483696203269909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4017596788989130802179939 6026395183483696203269909)
                ·
                  refine ⟨282487274225798259528277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6026395183483696203269909 282487274225798259528277)
                  ·
                    rfl

theorem cell23_4951278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 6, 1, 6].length) (baseStart_4951278 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4951278 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4951278 prefixEnd_4951278 := by exact prefixLift 4951278
  have htrace : WordTrace (prefixWord ++ tailWord_4951278) baseStart_4951278 baseEnd_4951278 := by
    simpa [prefixWord, tailWord_4951278, baseEnd_4951278] using wordTrace_append hprefix tailTrace_4951278
  have hstable : (prefixWord ++ tailWord_4951278).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4951278).length < 2 ^ (prefixWord ++ tailWord_4951278).sum := by decide
  have hdescent : baseEnd_4951278 < baseStart_4951278 := by decide
  rcases family_descends (prefixWord ++ tailWord_4951278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4951305 : List Nat := [1, 2, 1, 1, 3, 3, 2, 5, 1, 1, 3]
def baseStart_4951305 : Nat := 118140960795 + 4951305 * 2 ^ 59
def prefixEnd_4951305 : Nat := 4983230072969 + 3 ^ 40 * 4951305 * 2
def baseEnd_4951305 : Nat := 2542399332009855730116869

theorem tailTrace_4951305 : CollatzResearch.WordTrace tailWord_4951305 prefixEnd_4951305 2542399332009855730116869 := by
  unfold tailWord_4951305
  simp only [CollatzResearch.WordTrace]
  refine ⟨180588929327275075416215369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120392619551516716944143579 180588929327275075416215369)
  ·
    refine ⟨135441696995456306562161527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 180588929327275075416215369 135441696995456306562161527)
    ·
      refine ⟨203162545493184459843242291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 135441696995456306562161527 203162545493184459843242291)
      ·
        refine ⟨304743818239776689764863437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 203162545493184459843242291 304743818239776689764863437)
        ·
          refine ⟨114278931839916258661823789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 304743818239776689764863437 114278931839916258661823789)
          ·
            refine ⟨42854599439968596998183921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 114278931839916258661823789 42854599439968596998183921)
            ·
              refine ⟨32140949579976447748637941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42854599439968596998183921 32140949579976447748637941)
              ·
                refine ⟨3013214023122791976434807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 32140949579976447748637941 3013214023122791976434807)
                ·
                  refine ⟨4519821034684187964652211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3013214023122791976434807 4519821034684187964652211)
                  ·
                    refine ⟨6779731552026281946978317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4519821034684187964652211 6779731552026281946978317)
                    ·
                      refine ⟨2542399332009855730116869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6779731552026281946978317 2542399332009855730116869)
                      ·
                        rfl

theorem cell23_4951305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 2, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 2, 5, 1, 1, 3].length) (baseStart_4951305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4951305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4951305 prefixEnd_4951305 := by exact prefixLift 4951305
  have htrace : WordTrace (prefixWord ++ tailWord_4951305) baseStart_4951305 baseEnd_4951305 := by
    simpa [prefixWord, tailWord_4951305, baseEnd_4951305] using wordTrace_append hprefix tailTrace_4951305
  have hstable : (prefixWord ++ tailWord_4951305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4951305).length < 2 ^ (prefixWord ++ tailWord_4951305).sum := by decide
  have hdescent : baseEnd_4951305 < baseStart_4951305 := by decide
  rcases family_descends (prefixWord ++ tailWord_4951305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4951322 : List Nat := [3, 1, 1, 3, 3, 2, 1, 4, 1, 1, 3]
def baseStart_4951322 : Nat := 118140960795 + 4951322 * 2 ^ 59
def prefixEnd_4951322 : Nat := 4983230072969 + 3 ^ 40 * 4951322 * 2
def baseEnd_4951322 : Nat := 2542408061180982163604291

theorem tailTrace_4951322 : CollatzResearch.WordTrace tailWord_4951322 prefixEnd_4951322 2542408061180982163604291 := by
  unfold tailWord_4951322
  simp only [CollatzResearch.WordTrace]
  refine ⟨45147387342053371829896055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 120393032912142324879722813 45147387342053371829896055)
  ·
    refine ⟨67721081013080057744844083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45147387342053371829896055 67721081013080057744844083)
    ·
      refine ⟨101581621519620086617266125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67721081013080057744844083 101581621519620086617266125)
      ·
        refine ⟨38093108069857532481474797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 101581621519620086617266125 38093108069857532481474797)
        ·
          refine ⟨14284915526196574680553049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38093108069857532481474797 14284915526196574680553049)
          ·
            refine ⟨10713686644647431010414787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14284915526196574680553049 10713686644647431010414787)
            ·
              refine ⟨16070529966971146515622181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10713686644647431010414787 16070529966971146515622181)
              ·
                refine ⟨3013224368807089971679159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16070529966971146515622181 3013224368807089971679159)
                ·
                  refine ⟨4519836553210634957518739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3013224368807089971679159 4519836553210634957518739)
                  ·
                    refine ⟨6779754829815952436278109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4519836553210634957518739 6779754829815952436278109)
                    ·
                      refine ⟨2542408061180982163604291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6779754829815952436278109 2542408061180982163604291)
                      ·
                        rfl

theorem cell23_4951322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 2, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 2, 1, 4, 1, 1, 3].length) (baseStart_4951322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4951322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4951322 prefixEnd_4951322 := by exact prefixLift 4951322
  have htrace : WordTrace (prefixWord ++ tailWord_4951322) baseStart_4951322 baseEnd_4951322 := by
    simpa [prefixWord, tailWord_4951322, baseEnd_4951322] using wordTrace_append hprefix tailTrace_4951322
  have hstable : (prefixWord ++ tailWord_4951322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4951322).length < 2 ^ (prefixWord ++ tailWord_4951322).sum := by decide
  have hdescent : baseEnd_4951322 < baseStart_4951322 := by decide
  rcases family_descends (prefixWord ++ tailWord_4951322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4951338 : List Nat := [3, 1, 4, 2, 1, 1, 1, 3, 1, 6]
def baseStart_4951338 : Nat := 118140960795 + 4951338 * 2 ^ 59
def prefixEnd_4951338 : Nat := 4983230072969 + 3 ^ 40 * 4951338 * 2
def baseEnd_4951338 : Nat := 847472092290484700334739

theorem tailTrace_4951338 : CollatzResearch.WordTrace tailWord_4951338 prefixEnd_4951338 847472092290484700334739 := by
  unfold tailWord_4951338
  simp only [CollatzResearch.WordTrace]
  refine ⟨45147533234038880513041667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 120393421957437014701444445 45147533234038880513041667)
  ·
    refine ⟨67721299851058320769562501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45147533234038880513041667 67721299851058320769562501)
    ·
      refine ⟨12697743722073435144292969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 67721299851058320769562501 12697743722073435144292969)
      ·
        refine ⟨9523307791555076358219727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12697743722073435144292969 9523307791555076358219727)
        ·
          refine ⟨14284961687332614537329591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9523307791555076358219727 14284961687332614537329591)
          ·
            refine ⟨21427442530998921805994387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14284961687332614537329591 21427442530998921805994387)
            ·
              refine ⟨32141163796498382708991581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21427442530998921805994387 32141163796498382708991581)
              ·
                refine ⟨12052936423686893515871843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32141163796498382708991581 12052936423686893515871843)
                ·
                  refine ⟨18079404635530340273807765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12052936423686893515871843 18079404635530340273807765)
                  ·
                    refine ⟨847472092290484700334739, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18079404635530340273807765 847472092290484700334739)
                    ·
                      rfl

theorem cell23_4951338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 1, 3, 1, 6].length) (baseStart_4951338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4951338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4951338 prefixEnd_4951338 := by exact prefixLift 4951338
  have htrace : WordTrace (prefixWord ++ tailWord_4951338) baseStart_4951338 baseEnd_4951338 := by
    simpa [prefixWord, tailWord_4951338, baseEnd_4951338] using wordTrace_append hprefix tailTrace_4951338
  have hstable : (prefixWord ++ tailWord_4951338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4951338).length < 2 ^ (prefixWord ++ tailWord_4951338).sum := by decide
  have hdescent : baseEnd_4951338 < baseStart_4951338 := by decide
  rcases family_descends (prefixWord ++ tailWord_4951338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4951345 : List Nat := [1, 2, 2, 3, 3, 1, 1, 1, 5, 2, 2]
def baseStart_4951345 : Nat := 118140960795 + 4951345 * 2 ^ 59
def prefixEnd_4951345 : Nat := 4983230072969 + 3 ^ 40 * 4951345 * 2
def baseEnd_4951345 : Nat := 2542419871236035573616685

theorem tailTrace_4951345 : CollatzResearch.WordTrace tailWord_4951345 prefixEnd_4951345 2542419871236035573616685 := by
  unfold tailWord_4951345
  simp only [CollatzResearch.WordTrace]
  refine ⟨180590388247130162247671489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120393592164753441498447659 180590388247130162247671489)
  ·
    refine ⟨135442791185347621685753617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 180590388247130162247671489 135442791185347621685753617)
    ·
      refine ⟨101582093389010716264315213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 135442791185347621685753617 101582093389010716264315213)
      ·
        refine ⟨38093285020879018599118205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 101582093389010716264315213 38093285020879018599118205)
        ·
          refine ⟨14284981882829631974669327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38093285020879018599118205 14284981882829631974669327)
          ·
            refine ⟨21427472824244447962003991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14284981882829631974669327 21427472824244447962003991)
            ·
              refine ⟨32141209236366671943005987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21427472824244447962003991 32141209236366671943005987)
              ·
                refine ⟨48211813854550007914508981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32141209236366671943005987 48211813854550007914508981)
                ·
                  refine ⟨4519857548864063241985217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 48211813854550007914508981 4519857548864063241985217)
                  ·
                    refine ⟨3389893161648047431488913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4519857548864063241985217 3389893161648047431488913)
                    ·
                      refine ⟨2542419871236035573616685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3389893161648047431488913 2542419871236035573616685)
                      ·
                        rfl

theorem cell23_4951345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 1, 1, 5, 2, 2].length) (baseStart_4951345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4951345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4951345 prefixEnd_4951345 := by exact prefixLift 4951345
  have htrace : WordTrace (prefixWord ++ tailWord_4951345) baseStart_4951345 baseEnd_4951345 := by
    simpa [prefixWord, tailWord_4951345, baseEnd_4951345] using wordTrace_append hprefix tailTrace_4951345
  have hstable : (prefixWord ++ tailWord_4951345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4951345).length < 2 ^ (prefixWord ++ tailWord_4951345).sum := by decide
  have hdescent : baseEnd_4951345 < baseStart_4951345 := by decide
  rcases family_descends (prefixWord ++ tailWord_4951345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4951358 : List Nat := [4, 2, 1, 2, 1, 1, 1, 4, 1, 2, 4]
def baseStart_4951358 : Nat := 118140960795 + 4951358 * 2 ^ 59
def prefixEnd_4951358 : Nat := 4983230072969 + 3 ^ 40 * 4951358 * 2
def baseEnd_4951358 : Nat := 2542426546484544022754125

theorem tailTrace_4951358 : CollatzResearch.WordTrace tailWord_4951358 prefixEnd_4951358 2542426546484544022754125 := by
  unfold tailWord_4951358
  simp only [CollatzResearch.WordTrace]
  refine ⟨22573857799510383183486841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 120393908264055376978596485 22573857799510383183486841)
  ·
    refine ⟨16930393349632787387615131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22573857799510383183486841 16930393349632787387615131)
    ·
      refine ⟨25395590024449181081422697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16930393349632787387615131 25395590024449181081422697)
      ·
        refine ⟨19046692518336885811067023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25395590024449181081422697 19046692518336885811067023)
        ·
          refine ⟨28570038777505328716600535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19046692518336885811067023 28570038777505328716600535)
          ·
            refine ⟨42855058166257993074900803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28570038777505328716600535 42855058166257993074900803)
            ·
              refine ⟨64282587249386989612351205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42855058166257993074900803 64282587249386989612351205)
              ·
                refine ⟨12052985109260060552315851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 64282587249386989612351205 12052985109260060552315851)
                ·
                  refine ⟨18079477663890090828473777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12052985109260060552315851 18079477663890090828473777)
                  ·
                    refine ⟨13559608247917568121355333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18079477663890090828473777 13559608247917568121355333)
                    ·
                      refine ⟨2542426546484544022754125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13559608247917568121355333 2542426546484544022754125)
                      ·
                        rfl

theorem cell23_4951358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 1, 4, 1, 2, 4].length) (baseStart_4951358 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4951358 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4951358 prefixEnd_4951358 := by exact prefixLift 4951358
  have htrace : WordTrace (prefixWord ++ tailWord_4951358) baseStart_4951358 baseEnd_4951358 := by
    simpa [prefixWord, tailWord_4951358, baseEnd_4951358] using wordTrace_append hprefix tailTrace_4951358
  have hstable : (prefixWord ++ tailWord_4951358).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4951358).length < 2 ^ (prefixWord ++ tailWord_4951358).sum := by decide
  have hdescent : baseEnd_4951358 < baseStart_4951358 := by decide
  rcases family_descends (prefixWord ++ tailWord_4951358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4951389 : List Nat := [1, 4, 5, 1, 1, 2, 1, 1, 1, 6]
def baseStart_4951389 : Nat := 118140960795 + 4951389 * 2 ^ 59
def prefixEnd_4951389 : Nat := 4983230072969 + 3 ^ 40 * 4951389 * 2
def baseEnd_4951389 : Nat := 847480821461611133822161

theorem tailTrace_4951389 : CollatzResearch.WordTrace tailWord_4951389 prefixEnd_4951389 847480821461611133822161 := by
  unfold tailWord_4951389
  simp only [CollatzResearch.WordTrace]
  refine ⟨180591993058970757762273221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120394662039313838508182147 180591993058970757762273221)
  ·
    refine ⟨33860998698557017080426229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 180591993058970757762273221 33860998698557017080426229)
    ·
      refine ⟨3174468627989720351289959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 33860998698557017080426229 3174468627989720351289959)
      ·
        refine ⟨4761702941984580526934939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3174468627989720351289959 4761702941984580526934939)
        ·
          refine ⟨7142554412976870790402409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4761702941984580526934939 7142554412976870790402409)
          ·
            refine ⟨5356915809732653092801807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7142554412976870790402409 5356915809732653092801807)
            ·
              refine ⟨8035373714598979639202711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5356915809732653092801807 8035373714598979639202711)
              ·
                refine ⟨12053060571898469458804067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8035373714598979639202711 12053060571898469458804067)
                ·
                  refine ⟨18079590857847704188206101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12053060571898469458804067 18079590857847704188206101)
                  ·
                    refine ⟨847480821461611133822161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18079590857847704188206101 847480821461611133822161)
                    ·
                      rfl

theorem cell23_4951389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 2, 1, 1, 1, 6].length) (baseStart_4951389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4951389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4951389 prefixEnd_4951389 := by exact prefixLift 4951389
  have htrace : WordTrace (prefixWord ++ tailWord_4951389) baseStart_4951389 baseEnd_4951389 := by
    simpa [prefixWord, tailWord_4951389, baseEnd_4951389] using wordTrace_append hprefix tailTrace_4951389
  have hstable : (prefixWord ++ tailWord_4951389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4951389).length < 2 ^ (prefixWord ++ tailWord_4951389).sum := by decide
  have hdescent : baseEnd_4951389 < baseStart_4951389 := by decide
  rcases family_descends (prefixWord ++ tailWord_4951389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4951395 : List Nat := [1, 1, 1, 5, 2, 4, 1, 1, 1, 3, 3]
def baseStart_4951395 : Nat := 118140960795 + 4951395 * 2 ^ 59
def prefixEnd_4951395 : Nat := 4983230072969 + 3 ^ 40 * 4951395 * 2
def baseEnd_4951395 : Nat := 2542445545268760377991455

theorem tailTrace_4951395 : CollatzResearch.WordTrace tailWord_4951395 prefixEnd_4951395 2542445545268760377991455 := by
  unfold tailWord_4951395
  simp only [CollatzResearch.WordTrace]
  refine ⟨180592211896949020786991639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120394807931299347191327759 180592211896949020786991639)
  ·
    refine ⟨270888317845423531180487459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 180592211896949020786991639 270888317845423531180487459)
    ·
      refine ⟨406332476768135296770731189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 270888317845423531180487459 406332476768135296770731189)
      ·
        refine ⟨38093669697012684072256049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 406332476768135296770731189 38093669697012684072256049)
        ·
          refine ⟨28570252272759513054192037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38093669697012684072256049 28570252272759513054192037)
          ·
            refine ⟨5356922301142408697661007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 28570252272759513054192037 5356922301142408697661007)
            ·
              refine ⟨8035383451713613046491511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5356922301142408697661007 8035383451713613046491511)
              ·
                refine ⟨12053075177570419569737267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8035383451713613046491511 12053075177570419569737267)
                ·
                  refine ⟨18079612766355629354605901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12053075177570419569737267 18079612766355629354605901)
                  ·
                    refine ⟨6779854787383361007977213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18079612766355629354605901 6779854787383361007977213)
                    ·
                      refine ⟨2542445545268760377991455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6779854787383361007977213 2542445545268760377991455)
                      ·
                        rfl

theorem cell23_4951395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 4, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 4, 1, 1, 1, 3, 3].length) (baseStart_4951395 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4951395 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4951395 prefixEnd_4951395 := by exact prefixLift 4951395
  have htrace : WordTrace (prefixWord ++ tailWord_4951395) baseStart_4951395 baseEnd_4951395 := by
    simpa [prefixWord, tailWord_4951395, baseEnd_4951395] using wordTrace_append hprefix tailTrace_4951395
  have hstable : (prefixWord ++ tailWord_4951395).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4951395).length < 2 ^ (prefixWord ++ tailWord_4951395).sum := by decide
  have hdescent : baseEnd_4951395 < baseStart_4951395 := by decide
  rcases family_descends (prefixWord ++ tailWord_4951395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4951402 : List Nat := [3, 1, 3, 3, 3, 1, 2, 7]
def baseStart_4951402 : Nat := 118140960795 + 4951402 * 2 ^ 59
def prefixEnd_4951402 : Nat := 4983230072969 + 3 ^ 40 * 4951402 * 2
def baseEnd_4951402 : Nat := 94164782949383031503849

theorem tailTrace_4951402 : CollatzResearch.WordTrace tailWord_4951402 prefixEnd_4951402 94164782949383031503849 := by
  unfold tailWord_4951402
  simp only [CollatzResearch.WordTrace]
  refine ⟨45148116801980915245624115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 120394978138615773988330973 45148116801980915245624115)
  ·
    refine ⟨67722175202971372868436173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45148116801980915245624115 67722175202971372868436173)
    ·
      refine ⟨25395815701114264825663565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 67722175202971372868436173 25395815701114264825663565)
      ·
        refine ⟨9523430887917849309623837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25395815701114264825663565 9523430887917849309623837)
        ·
          refine ⟨3571286582969193491108939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9523430887917849309623837 3571286582969193491108939)
          ·
            refine ⟨5356929874453790236663409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3571286582969193491108939 5356929874453790236663409)
            ·
              refine ⟨4017697405840342677497557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5356929874453790236663409 4017697405840342677497557)
              ·
                refine ⟨94164782949383031503849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4017697405840342677497557 94164782949383031503849)
                ·
                  rfl

theorem cell23_4951402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 3, 1, 2, 7].length) (baseStart_4951402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4951402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4951402 prefixEnd_4951402 := by exact prefixLift 4951402
  have htrace : WordTrace (prefixWord ++ tailWord_4951402) baseStart_4951402 baseEnd_4951402 := by
    simpa [prefixWord, tailWord_4951402, baseEnd_4951402] using wordTrace_append hprefix tailTrace_4951402
  have hstable : (prefixWord ++ tailWord_4951402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4951402).length < 2 ^ (prefixWord ++ tailWord_4951402).sum := by decide
  have hdescent : baseEnd_4951402 < baseStart_4951402 := by decide
  rcases family_descends (prefixWord ++ tailWord_4951402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4951413 : List Nat := [1, 3, 4, 1, 4, 1, 1, 3, 1, 2, 2]
def baseStart_4951413 : Nat := 118140960795 + 4951413 * 2 ^ 59
def prefixEnd_4951413 : Nat := 4983230072969 + 3 ^ 40 * 4951413 * 2
def baseEnd_4951413 : Nat := 2542454787920541307566373

theorem tailTrace_4951413 : CollatzResearch.WordTrace tailWord_4951413 prefixEnd_4951413 2542454787920541307566373 := by
  unfold tailWord_4951413
  simp only [CollatzResearch.WordTrace]
  refine ⟨180592868410883809861146893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120395245607255873240764595 180592868410883809861146893)
  ·
    refine ⟨67722325654081428697930085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 180592868410883809861146893 67722325654081428697930085)
    ·
      refine ⟨12697936060140267880861891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 67722325654081428697930085 12697936060140267880861891)
      ·
        refine ⟨19046904090210401821292837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12697936060140267880861891 19046904090210401821292837)
        ·
          refine ⟨3571294516914450341492407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19046904090210401821292837 3571294516914450341492407)
          ·
            refine ⟨5356941775371675512238611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3571294516914450341492407 5356941775371675512238611)
            ·
              refine ⟨8035412663057513268357917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5356941775371675512238611 8035412663057513268357917)
              ·
                refine ⟨3013279748646567475634219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8035412663057513268357917 3013279748646567475634219)
                ·
                  refine ⟨4519919622969851213451329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3013279748646567475634219 4519919622969851213451329)
                  ·
                    refine ⟨3389939717227388410088497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4519919622969851213451329 3389939717227388410088497)
                    ·
                      refine ⟨2542454787920541307566373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3389939717227388410088497 2542454787920541307566373)
                      ·
                        rfl

theorem cell23_4951413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 4, 1, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 4, 1, 1, 3, 1, 2, 2].length) (baseStart_4951413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4951413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4951413 prefixEnd_4951413 := by exact prefixLift 4951413
  have htrace : WordTrace (prefixWord ++ tailWord_4951413) baseStart_4951413 baseEnd_4951413 := by
    simpa [prefixWord, tailWord_4951413, baseEnd_4951413] using wordTrace_append hprefix tailTrace_4951413
  have hstable : (prefixWord ++ tailWord_4951413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4951413).length < 2 ^ (prefixWord ++ tailWord_4951413).sum := by decide
  have hdescent : baseEnd_4951413 < baseStart_4951413 := by decide
  rcases family_descends (prefixWord ++ tailWord_4951413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4951435 : List Nat := [1, 1, 1, 1, 4, 3, 1, 3, 4, 2, 2]
def baseStart_4951435 : Nat := 118140960795 + 4951435 * 2 ^ 59
def prefixEnd_4951435 : Nat := 4983230072969 + 3 ^ 40 * 4951435 * 2
def baseEnd_4951435 : Nat := 2542466084494940221491271

theorem tailTrace_4951435 : CollatzResearch.WordTrace tailWord_4951435 prefixEnd_4951435 2542466084494940221491271 := by
  unfold tailWord_4951435
  simp only [CollatzResearch.WordTrace]
  refine ⟨180593670816804107618447759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120395780544536071745631839 180593670816804107618447759)
  ·
    refine ⟨270890506225206161427671639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 180593670816804107618447759 270890506225206161427671639)
    ·
      refine ⟨406335759337809242141507459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 270890506225206161427671639 406335759337809242141507459)
      ·
        refine ⟨609503639006713863212261189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 406335759337809242141507459 609503639006713863212261189)
        ·
          refine ⟨114281932313758849352298973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 609503639006713863212261189 114281932313758849352298973)
          ·
            refine ⟨42855724617659568507112115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 114281932313758849352298973 42855724617659568507112115)
            ·
              refine ⟨64283586926489352760668173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42855724617659568507112115 64283586926489352760668173)
              ·
                refine ⟨24106345097433507285250565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 64283586926489352760668173 24106345097433507285250565)
                ·
                  refine ⟨4519939705768782615984481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24106345097433507285250565 4519939705768782615984481)
                  ·
                    refine ⟨3389954779326586961988361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4519939705768782615984481 3389954779326586961988361)
                    ·
                      refine ⟨2542466084494940221491271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3389954779326586961988361 2542466084494940221491271)
                      ·
                        rfl

theorem cell23_4951435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 1, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 1, 3, 4, 2, 2].length) (baseStart_4951435 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4951435 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4951435 prefixEnd_4951435 := by exact prefixLift 4951435
  have htrace : WordTrace (prefixWord ++ tailWord_4951435) baseStart_4951435 baseEnd_4951435 := by
    simpa [prefixWord, tailWord_4951435, baseEnd_4951435] using wordTrace_append hprefix tailTrace_4951435
  have hstable : (prefixWord ++ tailWord_4951435).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4951435).length < 2 ^ (prefixWord ++ tailWord_4951435).sum := by decide
  have hdescent : baseEnd_4951435 < baseStart_4951435 := by decide
  rcases family_descends (prefixWord ++ tailWord_4951435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4951471 : List Nat := [1, 1, 2, 1, 2, 2, 1, 5, 1, 7]
def baseStart_4951471 : Nat := 118140960795 + 4951471 * 2 ^ 59
def prefixEnd_4951471 : Nat := 4983230072969 + 3 ^ 40 * 4951471 * 2
def baseEnd_4951471 : Nat := 847494856599500693547035

theorem tailTrace_4951471 : CollatzResearch.WordTrace tailWord_4951471 prefixEnd_4951471 847494856599500693547035 := by
  unfold tailWord_4951471
  simp only [CollatzResearch.WordTrace]
  refine ⟨180594983844673685766758267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120396655896449123844505511 180594983844673685766758267)
  ·
    refine ⟨270892475767010528650137401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 180594983844673685766758267 270892475767010528650137401)
    ·
      refine ⟨203169356825257896487603051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 270892475767010528650137401 203169356825257896487603051)
      ·
        refine ⟨304754035237886844731404577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 203169356825257896487603051 304754035237886844731404577)
        ·
          refine ⟨228565526428415133548553433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 304754035237886844731404577 228565526428415133548553433)
          ·
            refine ⟨171424144821311350161415075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 228565526428415133548553433 171424144821311350161415075)
            ·
              refine ⟨257136217231967025242122613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 171424144821311350161415075 257136217231967025242122613)
              ·
                refine ⟨24106520365496908616448995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 257136217231967025242122613 24106520365496908616448995)
                ·
                  refine ⟨36159780548245362924673493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24106520365496908616448995 36159780548245362924673493)
                  ·
                    refine ⟨847494856599500693547035, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 36159780548245362924673493 847494856599500693547035)
                    ·
                      rfl

theorem cell23_4951471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 5, 1, 7].length) (baseStart_4951471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4951471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4951471 prefixEnd_4951471 := by exact prefixLift 4951471
  have htrace : WordTrace (prefixWord ++ tailWord_4951471) baseStart_4951471 baseEnd_4951471 := by
    simpa [prefixWord, tailWord_4951471, baseEnd_4951471] using wordTrace_append hprefix tailTrace_4951471
  have hstable : (prefixWord ++ tailWord_4951471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4951471).length < 2 ^ (prefixWord ++ tailWord_4951471).sum := by decide
  have hdescent : baseEnd_4951471 < baseStart_4951471 := by decide
  rcases family_descends (prefixWord ++ tailWord_4951471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4951488 : List Nat := [2, 1, 1, 2, 3, 1, 4, 2, 2, 5]
def baseStart_4951488 : Nat := 118140960795 + 4951488 * 2 ^ 59
def prefixEnd_4951488 : Nat := 4983230072969 + 3 ^ 40 * 4951488 * 2
def baseEnd_4951488 : Nat := 847497766323209504709509

theorem tailTrace_4951488 : CollatzResearch.WordTrace tailWord_4951488 prefixEnd_4951488 847497766323209504709509 := by
  unfold tailWord_4951488
  simp only [CollatzResearch.WordTrace]
  refine ⟨90297801942806048835063559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120397069257074731780084745 90297801942806048835063559)
  ·
    refine ⟨135446702914209073252595339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90297801942806048835063559 135446702914209073252595339)
    ·
      refine ⟨203170054371313609878893009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 135446702914209073252595339 203170054371313609878893009)
      ·
        refine ⟨152377540778485207409169757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 203170054371313609878893009 152377540778485207409169757)
        ·
          refine ⟨57141577791931952778438659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 152377540778485207409169757 57141577791931952778438659)
          ·
            refine ⟨85712366687897929167657989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57141577791931952778438659 85712366687897929167657989)
            ·
              refine ⟨16071068753980861718935873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 85712366687897929167657989 16071068753980861718935873)
              ·
                refine ⟨12053301565485646289201905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16071068753980861718935873 12053301565485646289201905)
                ·
                  refine ⟨9039976174114234716901429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12053301565485646289201905 9039976174114234716901429)
                  ·
                    refine ⟨847497766323209504709509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9039976174114234716901429 847497766323209504709509)
                    ·
                      rfl

theorem cell23_4951488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 4, 2, 2, 5].length) (baseStart_4951488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4951488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4951488 prefixEnd_4951488 := by exact prefixLift 4951488
  have htrace : WordTrace (prefixWord ++ tailWord_4951488) baseStart_4951488 baseEnd_4951488 := by
    simpa [prefixWord, tailWord_4951488, baseEnd_4951488] using wordTrace_append hprefix tailTrace_4951488
  have hstable : (prefixWord ++ tailWord_4951488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4951488).length < 2 ^ (prefixWord ++ tailWord_4951488).sum := by decide
  have hdescent : baseEnd_4951488 < baseStart_4951488 := by decide
  rcases family_descends (prefixWord ++ tailWord_4951488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4951492 : List Nat := [2, 3, 3, 2, 1, 2, 1, 4, 5]
def baseStart_4951492 : Nat := 118140960795 + 4951492 * 2 ^ 59
def prefixEnd_4951492 : Nat := 4983230072969 + 3 ^ 40 * 4951492 * 2
def baseEnd_4951492 : Nat := 282499483654694055386501

theorem tailTrace_4951492 : CollatzResearch.WordTrace tailWord_4951492 prefixEnd_4951492 282499483654694055386501 := by
  unfold tailWord_4951492
  simp only [CollatzResearch.WordTrace]
  refine ⟨90297874888798803176636365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120397166518398404235515153 90297874888798803176636365)
  ·
    refine ⟨33861703083299551191238637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 90297874888798803176636365 33861703083299551191238637)
    ·
      refine ⟨12698138656237331696714489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33861703083299551191238637 12698138656237331696714489)
      ·
        refine ⟨9523603992177998772535867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12698138656237331696714489 9523603992177998772535867)
        ·
          refine ⟨14285405988266998158803801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9523603992177998772535867 14285405988266998158803801)
          ·
            refine ⟨10714054491200248619102851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14285405988266998158803801 10714054491200248619102851)
            ·
              refine ⟨16071081736800372928654277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10714054491200248619102851 16071081736800372928654277)
              ·
                refine ⟨3013327825650069924122677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16071081736800372928654277 3013327825650069924122677)
                ·
                  refine ⟨282499483654694055386501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3013327825650069924122677 282499483654694055386501)
                  ·
                    rfl

theorem cell23_4951492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 2, 1, 4, 5].length) (baseStart_4951492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4951492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4951492 prefixEnd_4951492 := by exact prefixLift 4951492
  have htrace : WordTrace (prefixWord ++ tailWord_4951492) baseStart_4951492 baseEnd_4951492 := by
    simpa [prefixWord, tailWord_4951492, baseEnd_4951492] using wordTrace_append hprefix tailTrace_4951492
  have hstable : (prefixWord ++ tailWord_4951492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4951492).length < 2 ^ (prefixWord ++ tailWord_4951492).sum := by decide
  have hdescent : baseEnd_4951492 < baseStart_4951492 := by decide
  rcases family_descends (prefixWord ++ tailWord_4951492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4951498 : List Nat := [3, 1, 2, 1, 2, 3, 2, 1, 1, 2, 5]
def baseStart_4951498 : Nat := 118140960795 + 4951498 * 2 ^ 59
def prefixEnd_4951498 : Nat := 4983230072969 + 3 ^ 40 * 4951498 * 2
def baseEnd_4951498 : Nat := 2542498433776173475003481

theorem tailTrace_4951498 : CollatzResearch.WordTrace tailWord_4951498 prefixEnd_4951498 2542498433776173475003481 := by
  unfold tailWord_4951498
  simp only [CollatzResearch.WordTrace]
  refine ⟨45148992153893967344497787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 120397312410383912918660765 45148992153893967344497787)
  ·
    refine ⟨67723488230840951016746681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45148992153893967344497787 67723488230840951016746681)
    ·
      refine ⟨50792616173130713262560011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67723488230840951016746681 50792616173130713262560011)
      ·
        refine ⟨76188924259696069893840017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50792616173130713262560011 76188924259696069893840017)
        ·
          refine ⟨57141693194772052420380013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 76188924259696069893840017 57141693194772052420380013)
          ·
            refine ⟨21428134948039519657642505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 57141693194772052420380013 21428134948039519657642505)
            ·
              refine ⟨16071101211029639743231879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21428134948039519657642505 16071101211029639743231879)
              ·
                refine ⟨24106651816544459614847819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16071101211029639743231879 24106651816544459614847819)
                ·
                  refine ⟨36159977724816689422271729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24106651816544459614847819 36159977724816689422271729)
                  ·
                    refine ⟨27119983293612517066703797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 36159977724816689422271729 27119983293612517066703797)
                    ·
                      refine ⟨2542498433776173475003481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27119983293612517066703797 2542498433776173475003481)
                      ·
                        rfl

theorem cell23_4951498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 2, 1, 1, 2, 5].length) (baseStart_4951498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4951498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4951498 prefixEnd_4951498 := by exact prefixLift 4951498
  have htrace : WordTrace (prefixWord ++ tailWord_4951498) baseStart_4951498 baseEnd_4951498 := by
    simpa [prefixWord, tailWord_4951498, baseEnd_4951498] using wordTrace_append hprefix tailTrace_4951498
  have hstable : (prefixWord ++ tailWord_4951498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4951498).length < 2 ^ (prefixWord ++ tailWord_4951498).sum := by decide
  have hdescent : baseEnd_4951498 < baseStart_4951498 := by decide
  rcases family_descends (prefixWord ++ tailWord_4951498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4951525 : List Nat := [1, 3, 1, 5, 1, 2, 1, 1, 1, 3, 4]
def baseStart_4951525 : Nat := 118140960795 + 4951525 * 2 ^ 59
def prefixEnd_4951525 : Nat := 4983230072969 + 3 ^ 40 * 4951525 * 2
def baseEnd_4951525 : Nat := 2542512297753844869365857

theorem tailTrace_4951525 : CollatzResearch.WordTrace tailWord_4951525 prefixEnd_4951525 2542512297753844869365857 := by
  unfold tailWord_4951525
  simp only [CollatzResearch.WordTrace]
  refine ⟨180596953386478052989224029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120397968924318701992816019 180596953386478052989224029)
  ·
    refine ⟨67723857519929269870959011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 180596953386478052989224029 67723857519929269870959011)
    ·
      refine ⟨101585786279893904806438517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67723857519929269870959011 101585786279893904806438517)
      ·
        refine ⟨9523667463740053575603611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 101585786279893904806438517 9523667463740053575603611)
        ·
          refine ⟨14285501195610080363405417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9523667463740053575603611 14285501195610080363405417)
          ·
            refine ⟨10714125896707560272554063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14285501195610080363405417 10714125896707560272554063)
            ·
              refine ⟨16071188845061340408831095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10714125896707560272554063 16071188845061340408831095)
              ·
                refine ⟨24106783267592010613246643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16071188845061340408831095 24106783267592010613246643)
                ·
                  refine ⟨36160174901388015919869965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24106783267592010613246643 36160174901388015919869965)
                  ·
                    refine ⟨13560065588020505969951237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 36160174901388015919869965 13560065588020505969951237)
                    ·
                      refine ⟨2542512297753844869365857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13560065588020505969951237 2542512297753844869365857)
                      ·
                        rfl

theorem cell23_4951525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 2, 1, 1, 1, 3, 4].length) (baseStart_4951525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4951525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4951525 prefixEnd_4951525 := by exact prefixLift 4951525
  have htrace : WordTrace (prefixWord ++ tailWord_4951525) baseStart_4951525 baseEnd_4951525 := by
    simpa [prefixWord, tailWord_4951525, baseEnd_4951525] using wordTrace_append hprefix tailTrace_4951525
  have hstable : (prefixWord ++ tailWord_4951525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4951525).length < 2 ^ (prefixWord ++ tailWord_4951525).sum := by decide
  have hdescent : baseEnd_4951525 < baseStart_4951525 := by decide
  rcases family_descends (prefixWord ++ tailWord_4951525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4951542 : List Nat := [5, 1, 1, 1, 2, 2, 1, 2, 2, 4, 2]
def baseStart_4951542 : Nat := 118140960795 + 4951542 * 2 ^ 59
def prefixEnd_4951542 : Nat := 4983230072969 + 3 ^ 40 * 4951542 * 2
def baseEnd_4951542 : Nat := 2542521026924971302853279

theorem tailTrace_4951542 : CollatzResearch.WordTrace tailWord_4951542 prefixEnd_4951542 2542521026924971302853279 := by
  unfold tailWord_4951542
  simp only [CollatzResearch.WordTrace]
  refine ⟨11287348339213529055787055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 120398382284944309928395253 11287348339213529055787055)
  ·
    refine ⟨16931022508820293583680583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11287348339213529055787055 16931022508820293583680583)
    ·
      refine ⟨25396533763230440375520875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16931022508820293583680583 25396533763230440375520875)
      ·
        refine ⟨38094800644845660563281313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25396533763230440375520875 38094800644845660563281313)
        ·
          refine ⟨28571100483634245422460985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38094800644845660563281313 28571100483634245422460985)
          ·
            refine ⟨21428325362725684066845739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28571100483634245422460985 21428325362725684066845739)
            ·
              refine ⟨32142488044088526100268609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21428325362725684066845739 32142488044088526100268609)
              ·
                refine ⟨24106866033066394575201457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32142488044088526100268609 24106866033066394575201457)
                ·
                  refine ⟨18080149524799795931401093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24106866033066394575201457 18080149524799795931401093)
                  ·
                    refine ⟨3390028035899961737137705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18080149524799795931401093 3390028035899961737137705)
                    ·
                      refine ⟨2542521026924971302853279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3390028035899961737137705 2542521026924971302853279)
                      ·
                        rfl

theorem cell23_4951542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 1, 2, 2, 4, 2].length) (baseStart_4951542 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4951542 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4951542 prefixEnd_4951542 := by exact prefixLift 4951542
  have htrace : WordTrace (prefixWord ++ tailWord_4951542) baseStart_4951542 baseEnd_4951542 := by
    simpa [prefixWord, tailWord_4951542, baseEnd_4951542] using wordTrace_append hprefix tailTrace_4951542
  have hstable : (prefixWord ++ tailWord_4951542).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4951542).length < 2 ^ (prefixWord ++ tailWord_4951542).sum := by decide
  have hdescent : baseEnd_4951542 < baseStart_4951542 := by decide
  rcases family_descends (prefixWord ++ tailWord_4951542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4951609 : List Nat := [1, 2, 1, 5, 1, 4, 1, 1, 3, 1, 3]
def baseStart_4951609 : Nat := 118140960795 + 4951609 * 2 ^ 59
def prefixEnd_4951609 : Nat := 4983230072969 + 3 ^ 40 * 4951609 * 2
def baseEnd_4951609 : Nat := 2542555430128822540715471

theorem tailTrace_4951609 : CollatzResearch.WordTrace tailWord_4951609 prefixEnd_4951609 2542555430128822540715471 := by
  unfold tailWord_4951609
  simp only [CollatzResearch.WordTrace]
  refine ⟨180600017118173735335281881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120400011412115823556854587 180600017118173735335281881)
  ·
    refine ⟨135450012838630301501461411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 180600017118173735335281881 135450012838630301501461411)
    ·
      refine ⟨203175019257945452252192117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 135450012838630301501461411 203175019257945452252192117)
      ·
        refine ⟨19047658055432386148643011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 203175019257945452252192117 19047658055432386148643011)
        ·
          refine ⟨28571487083148579222964517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19047658055432386148643011 28571487083148579222964517)
          ·
            refine ⟨5357153828090358604305847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 28571487083148579222964517 5357153828090358604305847)
            ·
              refine ⟨8035730742135537906458771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5357153828090358604305847 8035730742135537906458771)
              ·
                refine ⟨12053596113203306859688157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8035730742135537906458771 12053596113203306859688157)
                ·
                  refine ⟨4520098542451240072383059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12053596113203306859688157 4520098542451240072383059)
                  ·
                    refine ⟨6780147813676860108574589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4520098542451240072383059 6780147813676860108574589)
                    ·
                      refine ⟨2542555430128822540715471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6780147813676860108574589 2542555430128822540715471)
                      ·
                        rfl

theorem cell23_4951609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 4, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 4, 1, 1, 3, 1, 3].length) (baseStart_4951609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4951609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4951609 prefixEnd_4951609 := by exact prefixLift 4951609
  have htrace : WordTrace (prefixWord ++ tailWord_4951609) baseStart_4951609 baseEnd_4951609 := by
    simpa [prefixWord, tailWord_4951609, baseEnd_4951609] using wordTrace_append hprefix tailTrace_4951609
  have hstable : (prefixWord ++ tailWord_4951609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4951609).length < 2 ^ (prefixWord ++ tailWord_4951609).sum := by decide
  have hdescent : baseEnd_4951609 < baseStart_4951609 := by decide
  rcases family_descends (prefixWord ++ tailWord_4951609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4951632 : List Nat := [2, 1, 1, 1, 1, 3, 4, 1, 5, 2, 2]
def baseStart_4951632 : Nat := 118140960795 + 4951632 * 2 ^ 59
def prefixEnd_4951632 : Nat := 4983230072969 + 3 ^ 40 * 4951632 * 2
def baseEnd_4951632 : Nat := 2542567240183875950727865

theorem tailTrace_4951632 : CollatzResearch.WordTrace tailWord_4951632 prefixEnd_4951632 2542567240183875950727865 := by
  unfold tailWord_4951632
  simp only [CollatzResearch.WordTrace]
  refine ⟨90300427998545205131684575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120400570664726940175579433 90300427998545205131684575)
  ·
    refine ⟨135450641997817807697526863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90300427998545205131684575 135450641997817807697526863)
    ·
      refine ⟨203175962996726711546290295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 135450641997817807697526863 203175962996726711546290295)
      ·
        refine ⟨304763944495090067319435443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 203175962996726711546290295 304763944495090067319435443)
        ·
          refine ⟨457145916742635100979153165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 304763944495090067319435443 457145916742635100979153165)
          ·
            refine ⟨171429718778488162867182437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 457145916742635100979153165 171429718778488162867182437)
            ·
              refine ⟨32143072270966530537596707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 171429718778488162867182437 32143072270966530537596707)
              ·
                refine ⟨48214608406449795806395061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32143072270966530537596707 48214608406449795806395061)
                ·
                  refine ⟨4520119538104668356849537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 48214608406449795806395061 4520119538104668356849537)
                  ·
                    refine ⟨3390089653578501267637153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4520119538104668356849537 3390089653578501267637153)
                    ·
                      refine ⟨2542567240183875950727865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3390089653578501267637153 2542567240183875950727865)
                      ·
                        rfl

theorem cell23_4951632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 4, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 4, 1, 5, 2, 2].length) (baseStart_4951632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4951632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4951632 prefixEnd_4951632 := by exact prefixLift 4951632
  have htrace : WordTrace (prefixWord ++ tailWord_4951632) baseStart_4951632 baseEnd_4951632 := by
    simpa [prefixWord, tailWord_4951632, baseEnd_4951632] using wordTrace_append hprefix tailTrace_4951632
  have hstable : (prefixWord ++ tailWord_4951632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4951632).length < 2 ^ (prefixWord ++ tailWord_4951632).sum := by decide
  have hdescent : baseEnd_4951632 < baseStart_4951632 := by decide
  rcases family_descends (prefixWord ++ tailWord_4951632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4951652 : List Nat := [2, 3, 1, 1, 2, 5, 1, 1, 1, 1, 5]
def baseStart_4951652 : Nat := 118140960795 + 4951652 * 2 ^ 59
def prefixEnd_4951652 : Nat := 4983230072969 + 3 ^ 40 * 4951652 * 2
def baseEnd_4951652 : Nat := 2542577509796965872477773

theorem tailTrace_4951652 : CollatzResearch.WordTrace tailWord_4951652 prefixEnd_4951652 2542577509796965872477773 := by
  unfold tailWord_4951652
  simp only [CollatzResearch.WordTrace]
  refine ⟨90300792728508976839548605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120401056971345302452731473 90300792728508976839548605)
  ·
    refine ⟨33862797273190866314830727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 90300792728508976839548605 33862797273190866314830727)
    ·
      refine ⟨50794195909786299472246091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33862797273190866314830727 50794195909786299472246091)
      ·
        refine ⟨76191293864679449208369137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50794195909786299472246091 76191293864679449208369137)
        ·
          refine ⟨57143470398509586906276853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 76191293864679449208369137 57143470398509586906276853)
          ·
            refine ⟨5357200349860273772463455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 57143470398509586906276853 5357200349860273772463455)
            ·
              refine ⟨8035800524790410658695183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5357200349860273772463455 8035800524790410658695183)
              ·
                refine ⟨12053700787185615988042775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8035800524790410658695183 12053700787185615988042775)
                ·
                  refine ⟨18080551180778423982064163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12053700787185615988042775 18080551180778423982064163)
                  ·
                    refine ⟨27120826771167635973096245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18080551180778423982064163 27120826771167635973096245)
                    ·
                      refine ⟨2542577509796965872477773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27120826771167635973096245 2542577509796965872477773)
                      ·
                        rfl

theorem cell23_4951652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 5, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 5, 1, 1, 1, 1, 5].length) (baseStart_4951652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4951652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4951652 prefixEnd_4951652 := by exact prefixLift 4951652
  have htrace : WordTrace (prefixWord ++ tailWord_4951652) baseStart_4951652 baseEnd_4951652 := by
    simpa [prefixWord, tailWord_4951652, baseEnd_4951652] using wordTrace_append hprefix tailTrace_4951652
  have hstable : (prefixWord ++ tailWord_4951652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4951652).length < 2 ^ (prefixWord ++ tailWord_4951652).sum := by decide
  have hdescent : baseEnd_4951652 < baseStart_4951652 := by decide
  rcases family_descends (prefixWord ++ tailWord_4951652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4951692 : List Nat := [2, 2, 1, 2, 1, 1, 3, 3, 3, 3, 2]
def baseStart_4951692 : Nat := 118140960795 + 4951692 * 2 ^ 59
def prefixEnd_4951692 : Nat := 4983230072969 + 3 ^ 40 * 4951692 * 2
def baseEnd_4951692 : Nat := 2542598049023145715977589

theorem tailTrace_4951692 : CollatzResearch.WordTrace tailWord_4951692 prefixEnd_4951692 2542598049023145715977589 := by
  unfold tailWord_4951692
  simp only [CollatzResearch.WordTrace]
  refine ⟨90301522188436520255276665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120402029584582027007035553 90301522188436520255276665)
  ·
    refine ⟨67726141641327390191457499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90301522188436520255276665 67726141641327390191457499)
    ·
      refine ⟨101589212461991085287186249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67726141641327390191457499 101589212461991085287186249)
      ·
        refine ⟨76191909346493313965389687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 101589212461991085287186249 76191909346493313965389687)
        ·
          refine ⟨114287864019739970948084531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76191909346493313965389687 114287864019739970948084531)
          ·
            refine ⟨171431796029609956422126797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 114287864019739970948084531 171431796029609956422126797)
            ·
              refine ⟨64286923511103733658297549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 171431796029609956422126797 64286923511103733658297549)
              ·
                refine ⟨24107596316663900121861581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 64286923511103733658297549 24107596316663900121861581)
                ·
                  refine ⟨9040348618748962545698093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24107596316663900121861581 9040348618748962545698093)
                  ·
                    refine ⟨3390130732030860954636785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9040348618748962545698093 3390130732030860954636785)
                    ·
                      refine ⟨2542598049023145715977589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3390130732030860954636785 2542598049023145715977589)
                      ·
                        rfl

theorem cell23_4951692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 3, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 3, 3, 3, 3, 2].length) (baseStart_4951692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4951692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4951692 prefixEnd_4951692 := by exact prefixLift 4951692
  have htrace : WordTrace (prefixWord ++ tailWord_4951692) baseStart_4951692 baseEnd_4951692 := by
    simpa [prefixWord, tailWord_4951692, baseEnd_4951692] using wordTrace_append hprefix tailTrace_4951692
  have hstable : (prefixWord ++ tailWord_4951692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4951692).length < 2 ^ (prefixWord ++ tailWord_4951692).sum := by decide
  have hdescent : baseEnd_4951692 < baseStart_4951692 := by decide
  rcases family_descends (prefixWord ++ tailWord_4951692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4951700 : List Nat := [2, 4, 2, 2, 2, 1, 2, 3, 1, 2, 2]
def baseStart_4951700 : Nat := 118140960795 + 4951700 * 2 ^ 59
def prefixEnd_4951700 : Nat := 4983230072969 + 3 ^ 40 * 4951700 * 2
def baseEnd_4951700 : Nat := 2542602156868381684677553

theorem tailTrace_4951700 : CollatzResearch.WordTrace tailWord_4951700 prefixEnd_4951700 2542602156868381684677553 := by
  unfold tailWord_4951700
  simp only [CollatzResearch.WordTrace]
  refine ⟨90301668080422028938422277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120402224107229371917896369 90301668080422028938422277)
  ·
    refine ⟨16931562765079130425954177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 90301668080422028938422277 16931562765079130425954177)
    ·
      refine ⟨12698672073809347819465633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16931562765079130425954177 12698672073809347819465633)
      ·
        refine ⟨9524004055357010864599225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12698672073809347819465633 9524004055357010864599225)
        ·
          refine ⟨7143003041517758148449419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9524004055357010864599225 7143003041517758148449419)
          ·
            refine ⟨10714504562276637222674129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7143003041517758148449419 10714504562276637222674129)
            ·
              refine ⟨8035878421707477917005597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10714504562276637222674129 8035878421707477917005597)
              ·
                refine ⟨3013454408140304218877099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8035878421707477917005597 3013454408140304218877099)
                ·
                  refine ⟨4520181612210456328315649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3013454408140304218877099 4520181612210456328315649)
                  ·
                    refine ⟨3390136209157842246236737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4520181612210456328315649 3390136209157842246236737)
                    ·
                      refine ⟨2542602156868381684677553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3390136209157842246236737 2542602156868381684677553)
                      ·
                        rfl

theorem cell23_4951700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 1, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 1, 2, 3, 1, 2, 2].length) (baseStart_4951700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4951700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4951700 prefixEnd_4951700 := by exact prefixLift 4951700
  have htrace : WordTrace (prefixWord ++ tailWord_4951700) baseStart_4951700 baseEnd_4951700 := by
    simpa [prefixWord, tailWord_4951700, baseEnd_4951700] using wordTrace_append hprefix tailTrace_4951700
  have hstable : (prefixWord ++ tailWord_4951700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4951700).length < 2 ^ (prefixWord ++ tailWord_4951700).sum := by decide
  have hdescent : baseEnd_4951700 < baseStart_4951700 := by decide
  rcases family_descends (prefixWord ++ tailWord_4951700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4951716 : List Nat := [2, 3, 1, 2, 2, 4, 1, 2, 2, 1, 3]
def baseStart_4951716 : Nat := 118140960795 + 4951716 * 2 ^ 59
def prefixEnd_4951716 : Nat := 4983230072969 + 3 ^ 40 * 4951716 * 2
def baseEnd_4951716 : Nat := 2542610372558853622077479

theorem tailTrace_4951716 : CollatzResearch.WordTrace tailWord_4951716 prefixEnd_4951716 2542610372558853622077479 := by
  unfold tailWord_4951716
  simp only [CollatzResearch.WordTrace]
  refine ⟨90301959864393046304713501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120402613152524061739618001 90301959864393046304713501)
  ·
    refine ⟨33863234949147392364267563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 90301959864393046304713501 33863234949147392364267563)
    ·
      refine ⟨50794852423721088546401345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33863234949147392364267563 50794852423721088546401345)
      ·
        refine ⟨38096139317790816409801009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50794852423721088546401345 38096139317790816409801009)
        ·
          refine ⟨28572104488343112307350757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38096139317790816409801009 28572104488343112307350757)
          ·
            refine ⟨5357269591564333557628267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 28572104488343112307350757 5357269591564333557628267)
            ·
              refine ⟨8035904387346500336442401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5357269591564333557628267 8035904387346500336442401)
              ·
                refine ⟨6026928290509875252331801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8035904387346500336442401 6026928290509875252331801)
                ·
                  refine ⟨4520196217882406439248851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6026928290509875252331801 4520196217882406439248851)
                  ·
                    refine ⟨6780294326823609658873277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4520196217882406439248851 6780294326823609658873277)
                    ·
                      refine ⟨2542610372558853622077479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6780294326823609658873277 2542610372558853622077479)
                      ·
                        rfl

theorem cell23_4951716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 4, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 4, 1, 2, 2, 1, 3].length) (baseStart_4951716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4951716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4951716 prefixEnd_4951716 := by exact prefixLift 4951716
  have htrace : WordTrace (prefixWord ++ tailWord_4951716) baseStart_4951716 baseEnd_4951716 := by
    simpa [prefixWord, tailWord_4951716, baseEnd_4951716] using wordTrace_append hprefix tailTrace_4951716
  have hstable : (prefixWord ++ tailWord_4951716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4951716).length < 2 ^ (prefixWord ++ tailWord_4951716).sum := by decide
  have hdescent : baseEnd_4951716 < baseStart_4951716 := by decide
  rcases family_descends (prefixWord ++ tailWord_4951716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4951733 : List Nat := [1, 3, 3, 3, 2, 1, 3, 1, 2, 1, 3]
def baseStart_4951733 : Nat := 118140960795 + 4951733 * 2 ^ 59
def prefixEnd_4951733 : Nat := 4983230072969 + 3 ^ 40 * 4951733 * 2
def baseEnd_4951733 : Nat := 2542619101729980055564901

theorem tailTrace_4951733 : CollatzResearch.WordTrace tailWord_4951733 prefixEnd_4951733 2542619101729980055564901 := by
  unfold tailWord_4951733
  simp only [CollatzResearch.WordTrace]
  refine ⟨180604539769724504512795853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120403026513149669675197235 180604539769724504512795853)
  ·
    refine ⟨67726702413646689192298445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 180604539769724504512795853 67726702413646689192298445)
    ·
      refine ⟨25397513405117508447111917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 67726702413646689192298445 25397513405117508447111917)
      ·
        refine ⟨9524067526919065667666969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25397513405117508447111917 9524067526919065667666969)
        ·
          refine ⟨7143050645189299250750227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9524067526919065667666969 7143050645189299250750227)
          ·
            refine ⟨10714575967783948876125341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7143050645189299250750227 10714575967783948876125341)
            ·
              refine ⟨4017965987918980828547003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10714575967783948876125341 4017965987918980828547003)
              ·
                refine ⟨6026948981878471242820505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4017965987918980828547003 6026948981878471242820505)
                ·
                  refine ⟨4520211736408853432115379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6026948981878471242820505 4520211736408853432115379)
                  ·
                    refine ⟨6780317604613280148173069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4520211736408853432115379 6780317604613280148173069)
                    ·
                      refine ⟨2542619101729980055564901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6780317604613280148173069 2542619101729980055564901)
                      ·
                        rfl

theorem cell23_4951733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 1, 3, 1, 2, 1, 3].length) (baseStart_4951733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4951733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4951733 prefixEnd_4951733 := by exact prefixLift 4951733
  have htrace : WordTrace (prefixWord ++ tailWord_4951733) baseStart_4951733 baseEnd_4951733 := by
    simpa [prefixWord, tailWord_4951733, baseEnd_4951733] using wordTrace_append hprefix tailTrace_4951733
  have hstable : (prefixWord ++ tailWord_4951733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4951733).length < 2 ^ (prefixWord ++ tailWord_4951733).sum := by decide
  have hdescent : baseEnd_4951733 < baseStart_4951733 := by decide
  rcases family_descends (prefixWord ++ tailWord_4951733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4951739 : List Nat := [1, 1, 1, 1, 1, 2, 3, 7, 2, 2, 2]
def baseStart_4951739 : Nat := 118140960795 + 4951739 * 2 ^ 59
def prefixEnd_4951739 : Nat := 4983230072969 + 3 ^ 40 * 4951739 * 2
def baseEnd_4951739 : Nat := 2542622182613907032089873

theorem tailTrace_4951739 : CollatzResearch.WordTrace tailWord_4951739 prefixEnd_4951739 2542622182613907032089873 := by
  unfold tailWord_4951739
  simp only [CollatzResearch.WordTrace]
  refine ⟨180604758607702767537514271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120403172405135178358342847 180604758607702767537514271)
  ·
    refine ⟨270907137911554151306271407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 180604758607702767537514271 270907137911554151306271407)
    ·
      refine ⟨406360706867331226959407111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 270907137911554151306271407 406360706867331226959407111)
      ·
        refine ⟨609541060300996840439110667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 406360706867331226959407111 609541060300996840439110667)
        ·
          refine ⟨914311590451495260658666001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 609541060300996840439110667 914311590451495260658666001)
          ·
            refine ⟨685733692838621445493999501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 914311590451495260658666001 685733692838621445493999501)
            ·
              refine ⟨257150134814483042060249813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 685733692838621445493999501 257150134814483042060249813)
              ·
                refine ⟨6026956284714446298287105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 257150134814483042060249813 6026956284714446298287105)
                ·
                  refine ⟨4520217213535834723715329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6026956284714446298287105 4520217213535834723715329)
                  ·
                    refine ⟨3390162910151876042786497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4520217213535834723715329 3390162910151876042786497)
                    ·
                      refine ⟨2542622182613907032089873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3390162910151876042786497 2542622182613907032089873)
                      ·
                        rfl

theorem cell23_4951739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 7, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 7, 2, 2, 2].length) (baseStart_4951739 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4951739 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4951739 prefixEnd_4951739 := by exact prefixLift 4951739
  have htrace : WordTrace (prefixWord ++ tailWord_4951739) baseStart_4951739 baseEnd_4951739 := by
    simpa [prefixWord, tailWord_4951739, baseEnd_4951739] using wordTrace_append hprefix tailTrace_4951739
  have hstable : (prefixWord ++ tailWord_4951739).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4951739).length < 2 ^ (prefixWord ++ tailWord_4951739).sum := by decide
  have hdescent : baseEnd_4951739 < baseStart_4951739 := by decide
  rcases family_descends (prefixWord ++ tailWord_4951739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4951755 : List Nat := [1, 1, 1, 1, 3, 2, 1, 4, 1, 5, 3]
def baseStart_4951755 : Nat := 118140960795 + 4951755 * 2 ^ 59
def prefixEnd_4951755 : Nat := 4983230072969 + 3 ^ 40 * 4951755 * 2
def baseEnd_4951755 : Nat := 2542630398304378969489799

theorem tailTrace_4951755 : CollatzResearch.WordTrace tailWord_4951755 prefixEnd_4951755 2542630398304378969489799 := by
  unfold tailWord_4951755
  simp only [CollatzResearch.WordTrace]
  refine ⟨180605342175644802270096719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120403561450429868180064479 180605342175644802270096719)
  ·
    refine ⟨270908013263467203405145079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 180605342175644802270096719 270908013263467203405145079)
    ·
      refine ⟨406362019895200805107717619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 270908013263467203405145079 406362019895200805107717619)
      ·
        refine ⟨609543029842801207661576429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 406362019895200805107717619 609543029842801207661576429)
        ·
          refine ⟨228578636191050452873091161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 609543029842801207661576429 228578636191050452873091161)
          ·
            refine ⟨171433977143287839654818371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 228578636191050452873091161 171433977143287839654818371)
            ·
              refine ⟨257150965714931759482227557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 171433977143287839654818371 257150965714931759482227557)
              ·
                refine ⟨48215806071549704902917667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 257150965714931759482227557 48215806071549704902917667)
                ·
                  refine ⟨72323709107324557354376501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 48215806071549704902917667 72323709107324557354376501)
                  ·
                    refine ⟨6780347728811677251972797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 72323709107324557354376501 6780347728811677251972797)
                    ·
                      refine ⟨2542630398304378969489799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6780347728811677251972797 2542630398304378969489799)
                      ·
                        rfl

theorem cell23_4951755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 4, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 4, 1, 5, 3].length) (baseStart_4951755 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4951755 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4951755 prefixEnd_4951755 := by exact prefixLift 4951755
  have htrace : WordTrace (prefixWord ++ tailWord_4951755) baseStart_4951755 baseEnd_4951755 := by
    simpa [prefixWord, tailWord_4951755, baseEnd_4951755] using wordTrace_append hprefix tailTrace_4951755
  have hstable : (prefixWord ++ tailWord_4951755).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4951755).length < 2 ^ (prefixWord ++ tailWord_4951755).sum := by decide
  have hdescent : baseEnd_4951755 < baseStart_4951755 := by decide
  rcases family_descends (prefixWord ++ tailWord_4951755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4951779 : List Nat := [1, 1, 1, 7, 2, 2, 1, 1, 7]
def baseStart_4951779 : Nat := 118140960795 + 4951779 * 2 ^ 59
def prefixEnd_4951779 : Nat := 4983230072969 + 3 ^ 40 * 4951779 * 2
def baseEnd_4951779 : Nat := 282515857982231875065521

theorem tailTrace_4951779 : CollatzResearch.WordTrace tailWord_4951779 prefixEnd_4951779 282515857982231875065521 := by
  unfold tailWord_4951779
  simp only [CollatzResearch.WordTrace]
  refine ⟨180606217527557854368970391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120404145018371902912646927 180606217527557854368970391)
  ·
    refine ⟨270909326291336781553455587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 180606217527557854368970391 270909326291336781553455587)
    ·
      refine ⟨406363989437005172330183381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 270909326291336781553455587 406363989437005172330183381)
      ·
        refine ⟨9524156002429808726488673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 406363989437005172330183381 9524156002429808726488673)
        ·
          refine ⟨7143117001822356544866505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9524156002429808726488673 7143117001822356544866505)
          ·
            refine ⟨5357337751366767408649879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7143117001822356544866505 5357337751366767408649879)
            ·
              refine ⟨8036006627050151112974819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5357337751366767408649879 8036006627050151112974819)
              ·
                refine ⟨12054009940575226669462229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8036006627050151112974819 12054009940575226669462229)
                ·
                  refine ⟨282515857982231875065521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12054009940575226669462229 282515857982231875065521)
                  ·
                    rfl

theorem cell23_4951779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 2, 1, 1, 7].length) (baseStart_4951779 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4951779 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4951779 prefixEnd_4951779 := by exact prefixLift 4951779
  have htrace : WordTrace (prefixWord ++ tailWord_4951779) baseStart_4951779 baseEnd_4951779 := by
    simpa [prefixWord, tailWord_4951779, baseEnd_4951779] using wordTrace_append hprefix tailTrace_4951779
  have hstable : (prefixWord ++ tailWord_4951779).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4951779).length < 2 ^ (prefixWord ++ tailWord_4951779).sum := by decide
  have hdescent : baseEnd_4951779 < baseStart_4951779 := by decide
  rcases family_descends (prefixWord ++ tailWord_4951779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4951795 : List Nat := [1, 1, 1, 2, 2, 3, 2, 1, 3, 3, 4]
def baseStart_4951795 : Nat := 118140960795 + 4951795 * 2 ^ 59
def prefixEnd_4951795 : Nat := 4983230072969 + 3 ^ 40 * 4951795 * 2
def baseEnd_4951795 : Nat := 2542650937530558812989615

theorem tailTrace_4951795 : CollatzResearch.WordTrace tailWord_4951795 prefixEnd_4951795 2542650937530558812989615 := by
  unfold tailWord_4951795
  simp only [CollatzResearch.WordTrace]
  refine ⟨180606801095499889101552839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120404534063666592734368559 180606801095499889101552839)
  ·
    refine ⟨270910201643249833652329259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 180606801095499889101552839 270910201643249833652329259)
    ·
      refine ⟨406365302464874750478493889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 270910201643249833652329259 406365302464874750478493889)
      ·
        refine ⟨304773976848656062858870417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 406365302464874750478493889 304773976848656062858870417)
        ·
          refine ⟨228580482636492047144152813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 304773976848656062858870417 228580482636492047144152813)
          ·
            refine ⟨85717680988684517679057305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 228580482636492047144152813 85717680988684517679057305)
            ·
              refine ⟨64288260741513388259292979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 85717680988684517679057305 64288260741513388259292979)
              ·
                refine ⟨96432391112270082388939469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 64288260741513388259292979 96432391112270082388939469)
                ·
                  refine ⟨36162146667101280895852301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 96432391112270082388939469 36162146667101280895852301)
                  ·
                    refine ⟨13560805000162980335944613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 36162146667101280895852301 13560805000162980335944613)
                    ·
                      refine ⟨2542650937530558812989615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13560805000162980335944613 2542650937530558812989615)
                      ·
                        rfl

theorem cell23_4951795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 2, 1, 3, 3, 4].length) (baseStart_4951795 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4951795 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4951795 prefixEnd_4951795 := by exact prefixLift 4951795
  have htrace : WordTrace (prefixWord ++ tailWord_4951795) baseStart_4951795 baseEnd_4951795 := by
    simpa [prefixWord, tailWord_4951795, baseEnd_4951795] using wordTrace_append hprefix tailTrace_4951795
  have hstable : (prefixWord ++ tailWord_4951795).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4951795).length < 2 ^ (prefixWord ++ tailWord_4951795).sum := by decide
  have hdescent : baseEnd_4951795 < baseStart_4951795 := by decide
  rcases family_descends (prefixWord ++ tailWord_4951795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4951825 : List Nat := [1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 6]
def baseStart_4951825 : Nat := 118140960795 + 4951825 * 2 ^ 59
def prefixEnd_4951825 : Nat := 4983230072969 + 3 ^ 40 * 4951825 * 2
def baseEnd_4951825 : Nat := 2542666341950193695614477

theorem tailTrace_4951825 : CollatzResearch.WordTrace tailWord_4951825 prefixEnd_4951825 2542666341950193695614477 := by
  unfold tailWord_4951825
  simp only [CollatzResearch.WordTrace]
  refine ⟨180607895285391204225144929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120405263523594136150096619 180607895285391204225144929)
  ·
    refine ⟨135455921464043403168858697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 180607895285391204225144929 135455921464043403168858697)
    ·
      refine ⟨101591941098032552376644023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 135455921464043403168858697 101591941098032552376644023)
      ·
        refine ⟨152387911647048828564966035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101591941098032552376644023 152387911647048828564966035)
        ·
          refine ⟨228581867470573242847449053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 152387911647048828564966035 228581867470573242847449053)
          ·
            refine ⟨85718200301464966067793395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 228581867470573242847449053 85718200301464966067793395)
            ·
              refine ⟨128577300452197449101690093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 85718200301464966067793395 128577300452197449101690093)
              ·
                refine ⟨48216487669574043413133785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 128577300452197449101690093 48216487669574043413133785)
                ·
                  refine ⟨36162365752180532559850339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 48216487669574043413133785 36162365752180532559850339)
                  ·
                    refine ⟨54243548628270798839775509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 36162365752180532559850339 54243548628270798839775509)
                    ·
                      refine ⟨2542666341950193695614477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 54243548628270798839775509 2542666341950193695614477)
                      ·
                        rfl

theorem cell23_4951825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 6].length) (baseStart_4951825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4951825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4951825 prefixEnd_4951825 := by exact prefixLift 4951825
  have htrace : WordTrace (prefixWord ++ tailWord_4951825) baseStart_4951825 baseEnd_4951825 := by
    simpa [prefixWord, tailWord_4951825, baseEnd_4951825] using wordTrace_append hprefix tailTrace_4951825
  have hstable : (prefixWord ++ tailWord_4951825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4951825).length < 2 ^ (prefixWord ++ tailWord_4951825).sum := by decide
  have hdescent : baseEnd_4951825 < baseStart_4951825 := by decide
  rcases family_descends (prefixWord ++ tailWord_4951825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4951852 : List Nat := [2, 2, 1, 1, 1, 5, 2, 3, 6]
def baseStart_4951852 : Nat := 118140960795 + 4951852 * 2 ^ 59
def prefixEnd_4951852 : Nat := 4983230072969 + 3 ^ 40 * 4951852 * 2
def baseEnd_4951852 : Nat := 282520022880873898886317

theorem tailTrace_4951852 : CollatzResearch.WordTrace tailWord_4951852 prefixEnd_4951852 282520022880873898886317 := by
  unfold tailWord_4951852
  simp only [CollatzResearch.WordTrace]
  refine ⟨90304440028146693918188905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120405920037528925224251873 90304440028146693918188905)
  ·
    refine ⟨67728330021110020438641679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90304440028146693918188905 67728330021110020438641679)
    ·
      refine ⟨101592495031665030657962519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67728330021110020438641679 101592495031665030657962519)
      ·
        refine ⟨152388742547497545986943779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101592495031665030657962519 152388742547497545986943779)
        ·
          refine ⟨228583113821246318980415669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 152388742547497545986943779 228583113821246318980415669)
          ·
            refine ⟨21429666920741842404413969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 228583113821246318980415669 21429666920741842404413969)
            ·
              refine ⟨16072250190556381803310477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21429666920741842404413969 16072250190556381803310477)
              ·
                refine ⟨6027093821458643176241429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16072250190556381803310477 6027093821458643176241429)
                ·
                  refine ⟨282520022880873898886317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6027093821458643176241429 282520022880873898886317)
                  ·
                    rfl

theorem cell23_4951852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 6].length) (baseStart_4951852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4951852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4951852 prefixEnd_4951852 := by exact prefixLift 4951852
  have htrace : WordTrace (prefixWord ++ tailWord_4951852) baseStart_4951852 baseEnd_4951852 := by
    simpa [prefixWord, tailWord_4951852, baseEnd_4951852] using wordTrace_append hprefix tailTrace_4951852
  have hstable : (prefixWord ++ tailWord_4951852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4951852).length < 2 ^ (prefixWord ++ tailWord_4951852).sum := by decide
  have hdescent : baseEnd_4951852 < baseStart_4951852 := by decide
  rcases family_descends (prefixWord ++ tailWord_4951852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4951855 : List Nat := [1, 1, 2, 1, 2, 1, 2, 4, 1, 2, 6]
def baseStart_4951855 : Nat := 118140960795 + 4951855 * 2 ^ 59
def prefixEnd_4951855 : Nat := 4983230072969 + 3 ^ 40 * 4951855 * 2
def baseEnd_4951855 : Nat := 2542681746369828578239339

theorem tailTrace_4951855 : CollatzResearch.WordTrace tailWord_4951855 prefixEnd_4951855 2542681746369828578239339 := by
  unfold tailWord_4951855
  simp only [CollatzResearch.WordTrace]
  refine ⟨180608989475282519348737019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120405992983521679565824679 180608989475282519348737019)
  ·
    refine ⟨270913484212923779023105529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 180608989475282519348737019 270913484212923779023105529)
    ·
      refine ⟨203185113159692834267329147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 270913484212923779023105529 203185113159692834267329147)
      ·
        refine ⟨304777669739539251400993721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 203185113159692834267329147 304777669739539251400993721)
        ·
          refine ⟨228583252304654438550745291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 304777669739539251400993721 228583252304654438550745291)
          ·
            refine ⟨342874878456981657826117937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 228583252304654438550745291 342874878456981657826117937)
            ·
              refine ⟨257156158842736243369588453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 342874878456981657826117937 257156158842736243369588453)
              ·
                refine ⟨48216779783013045631797835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 257156158842736243369588453 48216779783013045631797835)
                ·
                  refine ⟨72325169674519568447696753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 48216779783013045631797835 72325169674519568447696753)
                  ·
                    refine ⟨54243877255889676335772565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 72325169674519568447696753 54243877255889676335772565)
                    ·
                      refine ⟨2542681746369828578239339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 54243877255889676335772565 2542681746369828578239339)
                      ·
                        rfl

theorem cell23_4951855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 4, 1, 2, 6].length) (baseStart_4951855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4951855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4951855 prefixEnd_4951855 := by exact prefixLift 4951855
  have htrace : WordTrace (prefixWord ++ tailWord_4951855) baseStart_4951855 baseEnd_4951855 := by
    simpa [prefixWord, tailWord_4951855, baseEnd_4951855] using wordTrace_append hprefix tailTrace_4951855
  have hstable : (prefixWord ++ tailWord_4951855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4951855).length < 2 ^ (prefixWord ++ tailWord_4951855).sum := by decide
  have hdescent : baseEnd_4951855 < baseStart_4951855 := by decide
  rcases family_descends (prefixWord ++ tailWord_4951855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4951866 : List Nat := [3, 1, 1, 1, 5, 3, 1, 1, 2, 2, 3]
def baseStart_4951866 : Nat := 118140960795 + 4951866 * 2 ^ 59
def prefixEnd_4951866 : Nat := 4983230072969 + 3 ^ 40 * 4951866 * 2
def baseEnd_4951866 : Nat := 2542687394657028035201789

theorem tailTrace_4951866 : CollatzResearch.WordTrace tailWord_4951866 prefixEnd_4951866 2542687394657028035201789 := by
  unfold tailWord_4951866
  simp only [CollatzResearch.WordTrace]
  refine ⟨45152347669560667056846863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 120406260452161778818258301 45152347669560667056846863)
  ·
    refine ⟨67728521504341000585270295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45152347669560667056846863 67728521504341000585270295)
    ·
      refine ⟨101592782256511500877905443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67728521504341000585270295 101592782256511500877905443)
      ·
        refine ⟨152389173384767251316858165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101592782256511500877905443 152389173384767251316858165)
        ·
          refine ⟨14286485004821929810955453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 152389173384767251316858165 14286485004821929810955453)
          ·
            refine ⟨5357431876808223679108295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14286485004821929810955453 5357431876808223679108295)
            ·
              refine ⟨8036147815212335518662443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5357431876808223679108295 8036147815212335518662443)
              ·
                refine ⟨12054221722818503277993665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8036147815212335518662443 12054221722818503277993665)
                ·
                  refine ⟨9040666292113877458495249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12054221722818503277993665 9040666292113877458495249)
                  ·
                    refine ⟨6780499719085408093871437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9040666292113877458495249 6780499719085408093871437)
                    ·
                      refine ⟨2542687394657028035201789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6780499719085408093871437 2542687394657028035201789)
                      ·
                        rfl

theorem cell23_4951866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 3, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 3, 1, 1, 2, 2, 3].length) (baseStart_4951866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4951866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4951866 prefixEnd_4951866 := by exact prefixLift 4951866
  have htrace : WordTrace (prefixWord ++ tailWord_4951866) baseStart_4951866 baseEnd_4951866 := by
    simpa [prefixWord, tailWord_4951866, baseEnd_4951866] using wordTrace_append hprefix tailTrace_4951866
  have hstable : (prefixWord ++ tailWord_4951866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4951866).length < 2 ^ (prefixWord ++ tailWord_4951866).sum := by decide
  have hdescent : baseEnd_4951866 < baseStart_4951866 := by decide
  rcases family_descends (prefixWord ++ tailWord_4951866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4951906 : List Nat := [3, 3, 2, 1, 2, 1, 1, 2, 1, 5, 2]
def baseStart_4951906 : Nat := 118140960795 + 4951906 * 2 ^ 59
def prefixEnd_4951906 : Nat := 4983230072969 + 3 ^ 40 * 4951906 * 2
def baseEnd_4951906 : Nat := 2542707933883207878701605

theorem tailTrace_4951906 : CollatzResearch.WordTrace tailWord_4951906 prefixEnd_4951906 2542707933883207878701605 := by
  unfold tailWord_4951906
  simp only [CollatzResearch.WordTrace]
  refine ⟨45152712399524438764710893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 120407233065398503372562381 45152712399524438764710893)
  ·
    refine ⟨16932267149821664536766585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45152712399524438764710893 16932267149821664536766585)
    ·
      refine ⟨12699200362366248402574939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16932267149821664536766585 12699200362366248402574939)
      ·
        refine ⟨19048800543549372603862409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12699200362366248402574939 19048800543549372603862409)
        ·
          refine ⟨14286600407662029452896807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19048800543549372603862409 14286600407662029452896807)
          ·
            refine ⟨21429900611493044179345211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14286600407662029452896807 21429900611493044179345211)
            ·
              refine ⟨32144850917239566269017817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21429900611493044179345211 32144850917239566269017817)
              ·
                refine ⟨24108638187929674701763363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32144850917239566269017817 24108638187929674701763363)
                ·
                  refine ⟨36162957281894512052645045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24108638187929674701763363 36162957281894512052645045)
                  ·
                    refine ⟨3390277245177610504935473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 36162957281894512052645045 3390277245177610504935473)
                    ·
                      refine ⟨2542707933883207878701605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3390277245177610504935473 2542707933883207878701605)
                      ·
                        rfl

theorem cell23_4951906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 1, 2, 1, 5, 2].length) (baseStart_4951906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4951906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4951906 prefixEnd_4951906 := by exact prefixLift 4951906
  have htrace : WordTrace (prefixWord ++ tailWord_4951906) baseStart_4951906 baseEnd_4951906 := by
    simpa [prefixWord, tailWord_4951906, baseEnd_4951906] using wordTrace_append hprefix tailTrace_4951906
  have hstable : (prefixWord ++ tailWord_4951906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4951906).length < 2 ^ (prefixWord ++ tailWord_4951906).sum := by decide
  have hdescent : baseEnd_4951906 < baseStart_4951906 := by decide
  rcases family_descends (prefixWord ++ tailWord_4951906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4951922 : List Nat := [3, 2, 1, 2, 1, 1, 1, 1, 5, 1, 5]
def baseStart_4951922 : Nat := 118140960795 + 4951922 * 2 ^ 59
def prefixEnd_4951922 : Nat := 4983230072969 + 3 ^ 40 * 4951922 * 2
def baseEnd_4951922 : Nat := 2542716149573679816101531

theorem tailTrace_4951922 : CollatzResearch.WordTrace tailWord_4951922 prefixEnd_4951922 2542716149573679816101531 := by
  unfold tailWord_4951922
  simp only [CollatzResearch.WordTrace]
  refine ⟨45152858291509947447856505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 120407622110693193194284013 45152858291509947447856505)
  ·
    refine ⟨33864643718632460585892379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45152858291509947447856505 33864643718632460585892379)
    ·
      refine ⟨50796965577948690878838569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33864643718632460585892379 50796965577948690878838569)
      ·
        refine ⟨38097724183461518159128927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50796965577948690878838569 38097724183461518159128927)
        ·
          refine ⟨57146586275192277238693391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38097724183461518159128927 57146586275192277238693391)
          ·
            refine ⟨85719879412788415858040087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57146586275192277238693391 85719879412788415858040087)
            ·
              refine ⟨128579819119182623787060131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 85719879412788415858040087 128579819119182623787060131)
              ·
                refine ⟨192869728678773935680590197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 128579819119182623787060131 192869728678773935680590197)
                ·
                  refine ⟨18081537063635056470055331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 192869728678773935680590197 18081537063635056470055331)
                  ·
                    refine ⟨27122305595452584705082997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18081537063635056470055331 27122305595452584705082997)
                    ·
                      refine ⟨2542716149573679816101531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27122305595452584705082997 2542716149573679816101531)
                      ·
                        rfl

theorem cell23_4951922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 1, 5, 1, 5].length) (baseStart_4951922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4951922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4951922 prefixEnd_4951922 := by exact prefixLift 4951922
  have htrace : WordTrace (prefixWord ++ tailWord_4951922) baseStart_4951922 baseEnd_4951922 := by
    simpa [prefixWord, tailWord_4951922, baseEnd_4951922] using wordTrace_append hprefix tailTrace_4951922
  have hstable : (prefixWord ++ tailWord_4951922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4951922).length < 2 ^ (prefixWord ++ tailWord_4951922).sum := by decide
  have hdescent : baseEnd_4951922 < baseStart_4951922 := by decide
  rcases family_descends (prefixWord ++ tailWord_4951922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4951939 : List Nat := [1, 1, 1, 3, 4, 3, 2, 1, 1, 1, 5]
def baseStart_4951939 : Nat := 118140960795 + 4951939 * 2 ^ 59
def prefixEnd_4951939 : Nat := 4983230072969 + 3 ^ 40 * 4951939 * 2
def baseEnd_4951939 : Nat := 2542724878744806249588953

theorem tailTrace_4951939 : CollatzResearch.WordTrace tailWord_4951939 prefixEnd_4951939 2542724878744806249588953 := by
  unfold tailWord_4951939
  simp only [CollatzResearch.WordTrace]
  refine ⟨180612053206978201694794871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120408035471318801129863247 180612053206978201694794871)
  ·
    refine ⟨270918079810467302542192307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 180612053206978201694794871 270918079810467302542192307)
    ·
      refine ⟨406377119715700953813288461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 270918079810467302542192307 406377119715700953813288461)
      ·
        refine ⟨152391419893387857679983173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 406377119715700953813288461 152391419893387857679983173)
        ·
          refine ⟨28573391230010223314996845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 152391419893387857679983173 28573391230010223314996845)
          ·
            refine ⟨10715021711253833743123817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28573391230010223314996845 10715021711253833743123817)
            ·
              refine ⟨8036266283440375307342863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10715021711253833743123817 8036266283440375307342863)
              ·
                refine ⟨12054399425160562961014295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8036266283440375307342863 12054399425160562961014295)
                ·
                  refine ⟨18081599137740844441521443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12054399425160562961014295 18081599137740844441521443)
                  ·
                    refine ⟨27122398706611266662282165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18081599137740844441521443 27122398706611266662282165)
                    ·
                      refine ⟨2542724878744806249588953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27122398706611266662282165 2542724878744806249588953)
                      ·
                        rfl

theorem cell23_4951939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 3, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 3, 2, 1, 1, 1, 5].length) (baseStart_4951939 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4951939 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4951939 prefixEnd_4951939 := by exact prefixLift 4951939
  have htrace : WordTrace (prefixWord ++ tailWord_4951939) baseStart_4951939 baseEnd_4951939 := by
    simpa [prefixWord, tailWord_4951939, baseEnd_4951939] using wordTrace_append hprefix tailTrace_4951939
  have hstable : (prefixWord ++ tailWord_4951939).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4951939).length < 2 ^ (prefixWord ++ tailWord_4951939).sum := by decide
  have hdescent : baseEnd_4951939 < baseStart_4951939 := by decide
  rcases family_descends (prefixWord ++ tailWord_4951939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4951953 : List Nat := [1, 2, 2, 1, 1, 1, 4, 6, 1, 2, 2]
def baseStart_4951953 : Nat := 118140960795 + 4951953 * 2 ^ 59
def prefixEnd_4951953 : Nat := 4983230072969 + 3 ^ 40 * 4951953 * 2
def baseEnd_4951953 : Nat := 2542732067473969194813889

theorem tailTrace_4951953 : CollatzResearch.WordTrace tailWord_4951953 prefixEnd_4951953 2542732067473969194813889 := by
  unfold tailWord_4951953
  simp only [CollatzResearch.WordTrace]
  refine ⟨180612563828927482085804513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120408375885951654723869675 180612563828927482085804513)
  ·
    refine ⟨135459422871695611564353385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 180612563828927482085804513 135459422871695611564353385)
    ·
      refine ⟨101594567153771708673265039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 135459422871695611564353385 101594567153771708673265039)
      ·
        refine ⟨152391850730657563009897559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101594567153771708673265039 152391850730657563009897559)
        ·
          refine ⟨228587776095986344514846339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 152391850730657563009897559 228587776095986344514846339)
          ·
            refine ⟨342881664143979516772269509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 228587776095986344514846339 342881664143979516772269509)
            ·
              refine ⟨64290312026996159394800533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 342881664143979516772269509 64290312026996159394800533)
              ·
                refine ⟨3013608376265444971631275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 64290312026996159394800533 3013608376265444971631275)
                ·
                  refine ⟨4520412564398167457446913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3013608376265444971631275 4520412564398167457446913)
                  ·
                    refine ⟨3390309423298625593085185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4520412564398167457446913 3390309423298625593085185)
                    ·
                      refine ⟨2542732067473969194813889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3390309423298625593085185 2542732067473969194813889)
                      ·
                        rfl

theorem cell23_4951953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 4, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 4, 6, 1, 2, 2].length) (baseStart_4951953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4951953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4951953 prefixEnd_4951953 := by exact prefixLift 4951953
  have htrace : WordTrace (prefixWord ++ tailWord_4951953) baseStart_4951953 baseEnd_4951953 := by
    simpa [prefixWord, tailWord_4951953, baseEnd_4951953] using wordTrace_append hprefix tailTrace_4951953
  have hstable : (prefixWord ++ tailWord_4951953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4951953).length < 2 ^ (prefixWord ++ tailWord_4951953).sum := by decide
  have hdescent : baseEnd_4951953 < baseStart_4951953 := by decide
  rcases family_descends (prefixWord ++ tailWord_4951953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4951970 : List Nat := [3, 3, 1, 2, 4, 1, 1, 2, 1, 1, 4]
def baseStart_4951970 : Nat := 118140960795 + 4951970 * 2 ^ 59
def prefixEnd_4951970 : Nat := 4983230072969 + 3 ^ 40 * 4951970 * 2
def baseEnd_4951970 : Nat := 2542740796645095628301311

theorem tailTrace_4951970 : CollatzResearch.WordTrace tailWord_4951970 prefixEnd_4951970 2542740796645095628301311 := by
  unfold tailWord_4951970
  simp only [CollatzResearch.WordTrace]
  refine ⟨45153295967466473497293341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 120408789246577262659448909 45153295967466473497293341)
  ·
    refine ⟨16932485987799927561485003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45153295967466473497293341 16932485987799927561485003)
    ·
      refine ⟨25398728981699891342227505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16932485987799927561485003 25398728981699891342227505)
      ·
        refine ⟨19049046736274918506670629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25398728981699891342227505 19049046736274918506670629)
        ·
          refine ⟨3571696263051547220000743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19049046736274918506670629 3571696263051547220000743)
          ·
            refine ⟨5357544394577320830001115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3571696263051547220000743 5357544394577320830001115)
            ·
              refine ⟨8036316591865981245001673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5357544394577320830001115 8036316591865981245001673)
              ·
                refine ⟨6027237443899485933751255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8036316591865981245001673 6027237443899485933751255)
                ·
                  refine ⟨9040856165849228900626883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6027237443899485933751255 9040856165849228900626883)
                  ·
                    refine ⟨13561284248773843350940325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9040856165849228900626883 13561284248773843350940325)
                    ·
                      refine ⟨2542740796645095628301311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13561284248773843350940325 2542740796645095628301311)
                      ·
                        rfl

theorem cell23_4951970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 4, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 4, 1, 1, 2, 1, 1, 4].length) (baseStart_4951970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4951970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4951970 prefixEnd_4951970 := by exact prefixLift 4951970
  have htrace : WordTrace (prefixWord ++ tailWord_4951970) baseStart_4951970 baseEnd_4951970 := by
    simpa [prefixWord, tailWord_4951970, baseEnd_4951970] using wordTrace_append hprefix tailTrace_4951970
  have hstable : (prefixWord ++ tailWord_4951970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4951970).length < 2 ^ (prefixWord ++ tailWord_4951970).sum := by decide
  have hdescent : baseEnd_4951970 < baseStart_4951970 := by decide
  rcases family_descends (prefixWord ++ tailWord_4951970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4952059 : List Nat := [1, 1, 1, 1, 1, 3, 5, 2, 2, 3, 3]
def baseStart_4952059 : Nat := 118140960795 + 4952059 * 2 ^ 59
def prefixEnd_4952059 : Nat := 4983230072969 + 3 ^ 40 * 4952059 * 2
def baseEnd_4952059 : Nat := 2542786496423345780088401

theorem tailTrace_4952059 : CollatzResearch.WordTrace tailWord_4952059 prefixEnd_4952059 2542786496423345780088401 := by
  unfold tailWord_4952059
  simp only [CollatzResearch.WordTrace]
  refine ⟨180616429966543462189163231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120410953311028974792775487 180616429966543462189163231)
  ·
    refine ⟨270924644949815193283744847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 180616429966543462189163231 270924644949815193283744847)
    ·
      refine ⟨406386967424722789925617271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 270924644949815193283744847 406386967424722789925617271)
      ·
        refine ⟨609580451137084184888425907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 406386967424722789925617271 609580451137084184888425907)
        ·
          refine ⟨914370676705626277332638861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 609580451137084184888425907 914370676705626277332638861)
          ·
            refine ⟨342889003764609853999739573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 914370676705626277332638861 342889003764609853999739573)
            ·
              refine ⟨32145844102932173812475585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 342889003764609853999739573 32145844102932173812475585)
              ·
                refine ⟨24109383077199130359356689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32145844102932173812475585 24109383077199130359356689)
                ·
                  refine ⟨18082037307899347769517517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24109383077199130359356689 18082037307899347769517517)
                  ·
                    refine ⟨6780763990462255413569069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18082037307899347769517517 6780763990462255413569069)
                    ·
                      refine ⟨2542786496423345780088401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6780763990462255413569069 2542786496423345780088401)
                      ·
                        rfl

theorem cell23_4952059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 5, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 5, 2, 2, 3, 3].length) (baseStart_4952059 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4952059 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4952059 prefixEnd_4952059 := by exact prefixLift 4952059
  have htrace : WordTrace (prefixWord ++ tailWord_4952059) baseStart_4952059 baseEnd_4952059 := by
    simpa [prefixWord, tailWord_4952059, baseEnd_4952059] using wordTrace_append hprefix tailTrace_4952059
  have hstable : (prefixWord ++ tailWord_4952059).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4952059).length < 2 ^ (prefixWord ++ tailWord_4952059).sum := by decide
  have hdescent : baseEnd_4952059 < baseStart_4952059 := by decide
  rcases family_descends (prefixWord ++ tailWord_4952059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4952099 : List Nat := [1, 1, 1, 4, 3, 1, 1, 3, 1, 3, 4]
def baseStart_4952099 : Nat := 118140960795 + 4952099 * 2 ^ 59
def prefixEnd_4952099 : Nat := 4983230072969 + 3 ^ 40 * 4952099 * 2
def baseEnd_4952099 : Nat := 2542807035649525623588217

theorem tailTrace_4952099 : CollatzResearch.WordTrace tailWord_4952099 prefixEnd_4952099 2542807035649525623588217 := by
  unfold tailWord_4952099
  simp only [CollatzResearch.WordTrace]
  refine ⟨180617888886398549020619351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120411925924265699347079567 180617888886398549020619351)
  ·
    refine ⟨270926833329597823530929027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 180617888886398549020619351 270926833329597823530929027)
    ·
      refine ⟨406390249994396735296393541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 270926833329597823530929027 406390249994396735296393541)
      ·
        refine ⟨76198171873949387868073789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 406390249994396735296393541 76198171873949387868073789)
        ·
          refine ⟨28574314452731020450527671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 76198171873949387868073789 28574314452731020450527671)
          ·
            refine ⟨42861471679096530675791507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28574314452731020450527671 42861471679096530675791507)
            ·
              refine ⟨64292207518644796013687261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42861471679096530675791507 64292207518644796013687261)
              ·
                refine ⟨24109577819491798505132723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 64292207518644796013687261 24109577819491798505132723)
                ·
                  refine ⟨36164366729237697757699085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24109577819491798505132723 36164366729237697757699085)
                  ·
                    refine ⟨13561637523464136659137157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 36164366729237697757699085 13561637523464136659137157)
                    ·
                      refine ⟨2542807035649525623588217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13561637523464136659137157 2542807035649525623588217)
                      ·
                        rfl

theorem cell23_4952099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 1, 3, 1, 3, 4].length) (baseStart_4952099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4952099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4952099 prefixEnd_4952099 := by exact prefixLift 4952099
  have htrace : WordTrace (prefixWord ++ tailWord_4952099) baseStart_4952099 baseEnd_4952099 := by
    simpa [prefixWord, tailWord_4952099, baseEnd_4952099] using wordTrace_append hprefix tailTrace_4952099
  have hstable : (prefixWord ++ tailWord_4952099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4952099).length < 2 ^ (prefixWord ++ tailWord_4952099).sum := by decide
  have hdescent : baseEnd_4952099 < baseStart_4952099 := by decide
  rcases family_descends (prefixWord ++ tailWord_4952099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4952100 : List Nat := [2, 3, 1, 4, 2, 2, 1, 3, 5]
def baseStart_4952100 : Nat := 118140960795 + 4952100 * 2 ^ 59
def prefixEnd_4952100 : Nat := 4983230072969 + 3 ^ 40 * 4952100 * 2
def baseEnd_4952100 : Nat := 282534172125575568852857

theorem tailTrace_4952100 : CollatzResearch.WordTrace tailWord_4952100 prefixEnd_4952100 282534172125575568852857 := by
  unfold tailWord_4952100
  simp only [CollatzResearch.WordTrace]
  refine ⟨90308962679697463095702877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120411950239596617460937169 90308962679697463095702877)
  ·
    refine ⟨33865861004886548660888579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 90308962679697463095702877 33865861004886548660888579)
    ·
      refine ⟨50798791507329822991332869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33865861004886548660888579 50798791507329822991332869)
      ·
        refine ⟨9524773407624341810874913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 50798791507329822991332869 9524773407624341810874913)
        ·
          refine ⟨7143580055718256358156185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9524773407624341810874913 7143580055718256358156185)
          ·
            refine ⟨5357685041788692268617139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7143580055718256358156185 5357685041788692268617139)
            ·
              refine ⟨8036527562683038402925709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5357685041788692268617139 8036527562683038402925709)
              ·
                refine ⟨3013697836006139401097141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8036527562683038402925709 3013697836006139401097141)
                ·
                  refine ⟨282534172125575568852857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3013697836006139401097141 282534172125575568852857)
                  ·
                    rfl

theorem cell23_4952100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 2, 1, 3, 5].length) (baseStart_4952100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4952100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4952100 prefixEnd_4952100 := by exact prefixLift 4952100
  have htrace : WordTrace (prefixWord ++ tailWord_4952100) baseStart_4952100 baseEnd_4952100 := by
    simpa [prefixWord, tailWord_4952100, baseEnd_4952100] using wordTrace_append hprefix tailTrace_4952100
  have hstable : (prefixWord ++ tailWord_4952100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4952100).length < 2 ^ (prefixWord ++ tailWord_4952100).sum := by decide
  have hdescent : baseEnd_4952100 < baseStart_4952100 := by decide
  rcases family_descends (prefixWord ++ tailWord_4952100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4952139 : List Nat := [1, 1, 1, 1, 3, 1, 2, 7, 6]
def baseStart_4952139 : Nat := 118140960795 + 4952139 * 2 ^ 59
def prefixEnd_4952139 : Nat := 4983230072969 + 3 ^ 40 * 4952139 * 2
def baseEnd_4952139 : Nat := 282536397208411718565337

theorem tailTrace_4952139 : CollatzResearch.WordTrace tailWord_4952139 prefixEnd_4952139 282536397208411718565337 := by
  unfold tailWord_4952139
  simp only [CollatzResearch.WordTrace]
  refine ⟨180619347806253635852075471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120412898537502423901383647 180619347806253635852075471)
  ·
    refine ⟨270929021709380453778113207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 180619347806253635852075471 270929021709380453778113207)
    ·
      refine ⟨406393532564070680667169811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 270929021709380453778113207 406393532564070680667169811)
      ·
        refine ⟨609590298846106021000754717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 406393532564070680667169811 609590298846106021000754717)
        ·
          refine ⟨228596362067289757875283019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 609590298846106021000754717 228596362067289757875283019)
          ·
            refine ⟨342894543100934636812924529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 228596362067289757875283019 342894543100934636812924529)
            ·
              refine ⟨257170907325700977609693397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 342894543100934636812924529 257170907325700977609693397)
              ·
                refine ⟨6027443140446116662727189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 257170907325700977609693397 6027443140446116662727189)
                ·
                  refine ⟨282536397208411718565337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6027443140446116662727189 282536397208411718565337)
                  ·
                    rfl

theorem cell23_4952139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 7, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 7, 6].length) (baseStart_4952139 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4952139 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4952139 prefixEnd_4952139 := by exact prefixLift 4952139
  have htrace : WordTrace (prefixWord ++ tailWord_4952139) baseStart_4952139 baseEnd_4952139 := by
    simpa [prefixWord, tailWord_4952139, baseEnd_4952139] using wordTrace_append hprefix tailTrace_4952139
  have hstable : (prefixWord ++ tailWord_4952139).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4952139).length < 2 ^ (prefixWord ++ tailWord_4952139).sum := by decide
  have hdescent : baseEnd_4952139 < baseStart_4952139 := by decide
  rcases family_descends (prefixWord ++ tailWord_4952139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4952150 : List Nat := [5, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4]
def baseStart_4952150 : Nat := 118140960795 + 4952150 * 2 ^ 59
def prefixEnd_4952150 : Nat := 4983230072969 + 3 ^ 40 * 4952150 * 2
def baseEnd_4952150 : Nat := 2542833223162904924050483

theorem tailTrace_4952150 : CollatzResearch.WordTrace tailWord_4952150 prefixEnd_4952150 2542833223162904924050483 := by
  unfold tailWord_4952150
  simp only [CollatzResearch.WordTrace]
  refine ⟨11288734313075861545670369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 120413166006142523153817269 11288734313075861545670369)
  ·
    refine ⟨8466550734806896159252777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11288734313075861545670369 8466550734806896159252777)
    ·
      refine ⟨6349913051105172119439583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8466550734806896159252777 6349913051105172119439583)
      ·
        refine ⟨9524869576657758179159375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6349913051105172119439583 9524869576657758179159375)
        ·
          refine ⟨14287304364986637268739063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9524869576657758179159375 14287304364986637268739063)
          ·
            refine ⟨21430956547479955903108595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14287304364986637268739063 21430956547479955903108595)
            ·
              refine ⟨32146434821219933854662893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21430956547479955903108595 32146434821219933854662893)
              ·
                refine ⟨12054913057957475195498585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32146434821219933854662893 12054913057957475195498585)
                ·
                  refine ⟨9041184793468106396623939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12054913057957475195498585 9041184793468106396623939)
                  ·
                    refine ⟨13561777190202159594935909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9041184793468106396623939 13561777190202159594935909)
                    ·
                      refine ⟨2542833223162904924050483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13561777190202159594935909 2542833223162904924050483)
                      ·
                        rfl

theorem cell23_4952150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4].length) (baseStart_4952150 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4952150 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4952150 prefixEnd_4952150 := by exact prefixLift 4952150
  have htrace : WordTrace (prefixWord ++ tailWord_4952150) baseStart_4952150 baseEnd_4952150 := by
    simpa [prefixWord, tailWord_4952150, baseEnd_4952150] using wordTrace_append hprefix tailTrace_4952150
  have hstable : (prefixWord ++ tailWord_4952150).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4952150).length < 2 ^ (prefixWord ++ tailWord_4952150).sum := by decide
  have hdescent : baseEnd_4952150 < baseStart_4952150 := by decide
  rcases family_descends (prefixWord ++ tailWord_4952150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4952200 : List Nat := [2, 1, 3, 4, 1, 2, 1, 2, 3, 1, 3]
def baseStart_4952200 : Nat := 118140960795 + 4952200 * 2 ^ 59
def prefixEnd_4952200 : Nat := 4983230072969 + 3 ^ 40 * 4952200 * 2
def baseEnd_4952200 : Nat := 2542858897195629728425253

theorem tailTrace_4952200 : CollatzResearch.WordTrace tailWord_4952200 prefixEnd_4952200 2542858897195629728425253 := by
  unfold tailWord_4952200
  simp only [CollatzResearch.WordTrace]
  refine ⟨90310786329516321635023027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120414381772688428846697369 90310786329516321635023027)
  ·
    refine ⟨135466179494274482452534541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90310786329516321635023027 135466179494274482452534541)
    ·
      refine ⟨50799817310352930919700453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 135466179494274482452534541 50799817310352930919700453)
      ·
        refine ⟨9524965745691174547443835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 50799817310352930919700453 9524965745691174547443835)
        ·
          refine ⟨14287448618536761821165753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9524965745691174547443835 14287448618536761821165753)
          ·
            refine ⟨10715586463902571365874315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14287448618536761821165753 10715586463902571365874315)
            ·
              refine ⟨16073379695853857048811473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10715586463902571365874315 16073379695853857048811473)
              ·
                refine ⟨12055034771890392786608605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16073379695853857048811473 12055034771890392786608605)
                ·
                  refine ⟨4520638039458897294978227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12055034771890392786608605 4520638039458897294978227)
                  ·
                    refine ⟨6780957059188345942467341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4520638039458897294978227 6780957059188345942467341)
                    ·
                      refine ⟨2542858897195629728425253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6780957059188345942467341 2542858897195629728425253)
                      ·
                        rfl

theorem cell23_4952200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 2, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 2, 1, 2, 3, 1, 3].length) (baseStart_4952200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4952200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4952200 prefixEnd_4952200 := by exact prefixLift 4952200
  have htrace : WordTrace (prefixWord ++ tailWord_4952200) baseStart_4952200 baseEnd_4952200 := by
    simpa [prefixWord, tailWord_4952200, baseEnd_4952200] using wordTrace_append hprefix tailTrace_4952200
  have hstable : (prefixWord ++ tailWord_4952200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4952200).length < 2 ^ (prefixWord ++ tailWord_4952200).sum := by decide
  have hdescent : baseEnd_4952200 < baseStart_4952200 := by decide
  rcases family_descends (prefixWord ++ tailWord_4952200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4952229 : List Nat := [1, 3, 1, 2, 1, 3, 12]
def baseStart_4952229 : Nat := 118140960795 + 4952229 * 2 ^ 59
def prefixEnd_4952229 : Nat := 4983230072969 + 3 ^ 40 * 4952229 * 2
def baseEnd_4952229 : Nat := 31393503557217408826699

theorem tailTrace_4952229 : CollatzResearch.WordTrace tailWord_4952229 prefixEnd_4952229 31393503557217408826699 := by
  unfold tailWord_4952229
  simp only [CollatzResearch.WordTrace]
  refine ⟨180622630375927581222851741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120415086917285054148567827 180622630375927581222851741)
  ·
    refine ⟨67733486390972842958569403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 180622630375927581222851741 67733486390972842958569403)
    ·
      refine ⟨101600229586459264437854105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67733486390972842958569403 101600229586459264437854105)
      ·
        refine ⟨76200172189844448328390579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 101600229586459264437854105 76200172189844448328390579)
        ·
          refine ⟨114300258284766672492585869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76200172189844448328390579 114300258284766672492585869)
          ·
            refine ⟨42862596856787502184719701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 114300258284766672492585869 42862596856787502184719701)
            ·
              refine ⟨31393503557217408826699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 42862596856787502184719701 31393503557217408826699)
              ·
                rfl

theorem cell23_4952229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 12].length) (baseStart_4952229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4952229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4952229 prefixEnd_4952229 := by exact prefixLift 4952229
  have htrace : WordTrace (prefixWord ++ tailWord_4952229) baseStart_4952229 baseEnd_4952229 := by
    simpa [prefixWord, tailWord_4952229, baseEnd_4952229] using wordTrace_append hprefix tailTrace_4952229
  have hstable : (prefixWord ++ tailWord_4952229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4952229).length < 2 ^ (prefixWord ++ tailWord_4952229).sum := by decide
  have hdescent : baseEnd_4952229 < baseStart_4952229 := by decide
  rcases family_descends (prefixWord ++ tailWord_4952229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4952239 : List Nat := [1, 1, 2, 1, 2, 3, 1, 1, 2, 2, 7]
def baseStart_4952239 : Nat := 118140960795 + 4952239 * 2 ^ 59
def prefixEnd_4952239 : Nat := 4983230072969 + 3 ^ 40 * 4952239 * 2
def baseEnd_4952239 : Nat := 2542878922941155075837573

theorem tailTrace_4952239 : CollatzResearch.WordTrace tailWord_4952239 prefixEnd_4952239 2542878922941155075837573 := by
  unfold tailWord_4952239
  simp only [CollatzResearch.WordTrace]
  refine ⟨180622995105891352930715771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120415330070594235287143847 180622995105891352930715771)
  ·
    refine ⟨270934492658837029396073657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 180622995105891352930715771 270934492658837029396073657)
    ·
      refine ⟨203200869494127772047055243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 270934492658837029396073657 203200869494127772047055243)
      ·
        refine ⟨304801304241191658070582865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 203200869494127772047055243 304801304241191658070582865)
        ·
          refine ⟨228600978180893743552937149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 304801304241191658070582865 228600978180893743552937149)
          ·
            refine ⟨85725366817835153832351431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 228600978180893743552937149 85725366817835153832351431)
            ·
              refine ⟨128588050226752730748527147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 85725366817835153832351431 128588050226752730748527147)
              ·
                refine ⟨192882075340129096122790721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 128588050226752730748527147 192882075340129096122790721)
                ·
                  refine ⟨144661556505096822092093041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 192882075340129096122790721 144661556505096822092093041)
                  ·
                    refine ⟨108496167378822616569069781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 144661556505096822092093041 108496167378822616569069781)
                    ·
                      refine ⟨2542878922941155075837573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 108496167378822616569069781 2542878922941155075837573)
                      ·
                        rfl

theorem cell23_4952239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 1, 2, 2, 7].length) (baseStart_4952239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4952239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4952239 prefixEnd_4952239 := by exact prefixLift 4952239
  have htrace : WordTrace (prefixWord ++ tailWord_4952239) baseStart_4952239 baseEnd_4952239 := by
    simpa [prefixWord, tailWord_4952239, baseEnd_4952239] using wordTrace_append hprefix tailTrace_4952239
  have hstable : (prefixWord ++ tailWord_4952239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4952239).length < 2 ^ (prefixWord ++ tailWord_4952239).sum := by decide
  have hdescent : baseEnd_4952239 < baseStart_4952239 := by decide
  rcases family_descends (prefixWord ++ tailWord_4952239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4952257 : List Nat := [1, 2, 6, 1, 2, 1, 2, 2, 1, 1, 4]
def baseStart_4952257 : Nat := 118140960795 + 4952257 * 2 ^ 59
def prefixEnd_4952257 : Nat := 4983230072969 + 3 ^ 40 * 4952257 * 2
def baseEnd_4952257 : Nat := 2542888165592936005412491

theorem tailTrace_4952257 : CollatzResearch.WordTrace tailWord_4952257 prefixEnd_4952257 2542888165592936005412491 := by
  unfold tailWord_4952257
  simp only [CollatzResearch.WordTrace]
  refine ⟨180623651619826142004871025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120415767746550761336580683 180623651619826142004871025)
  ·
    refine ⟨135467738714869606503653269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 180623651619826142004871025 135467738714869606503653269)
    ·
      refine ⟨6350050252259512804858747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 135467738714869606503653269 6350050252259512804858747)
      ·
        refine ⟨9525075378389269207288121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6350050252259512804858747 9525075378389269207288121)
        ·
          refine ⟨7143806533791951905466091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9525075378389269207288121 7143806533791951905466091)
          ·
            refine ⟨10715709800687927858199137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7143806533791951905466091 10715709800687927858199137)
            ·
              refine ⟨8036782350515945893649353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10715709800687927858199137 8036782350515945893649353)
              ·
                refine ⟨6027586762886959420237015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8036782350515945893649353 6027586762886959420237015)
                ·
                  refine ⟨9041380144330439130355523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6027586762886959420237015 9041380144330439130355523)
                  ·
                    refine ⟨13562070216495658695533285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9041380144330439130355523 13562070216495658695533285)
                    ·
                      refine ⟨2542888165592936005412491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13562070216495658695533285 2542888165592936005412491)
                      ·
                        rfl

theorem cell23_4952257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 1, 2, 2, 1, 1, 4].length) (baseStart_4952257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4952257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4952257 prefixEnd_4952257 := by exact prefixLift 4952257
  have htrace : WordTrace (prefixWord ++ tailWord_4952257) baseStart_4952257 baseEnd_4952257 := by
    simpa [prefixWord, tailWord_4952257, baseEnd_4952257] using wordTrace_append hprefix tailTrace_4952257
  have hstable : (prefixWord ++ tailWord_4952257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4952257).length < 2 ^ (prefixWord ++ tailWord_4952257).sum := by decide
  have hdescent : baseEnd_4952257 < baseStart_4952257 := by decide
  rcases family_descends (prefixWord ++ tailWord_4952257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4952259 : List Nat := [1, 1, 1, 3, 1, 1, 1, 2, 3, 9]
def baseStart_4952259 : Nat := 118140960795 + 4952259 * 2 ^ 59
def prefixEnd_4952259 : Nat := 4983230072969 + 3 ^ 40 * 4952259 * 2
def baseEnd_4952259 : Nat := 847629730851414999195827

theorem tailTrace_4952259 : CollatzResearch.WordTrace tailWord_4952259 prefixEnd_4952259 847629730851414999195827 := by
  unfold tailWord_4952259
  simp only [CollatzResearch.WordTrace]
  refine ⟨180623724565818896346443831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120415816377212597564295887 180623724565818896346443831)
  ·
    refine ⟨270935586848728344519665747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 180623724565818896346443831 270935586848728344519665747)
    ·
      refine ⟨406403380273092516779498621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 270935586848728344519665747 406403380273092516779498621)
      ·
        refine ⟨152401267602409693792311983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 406403380273092516779498621 152401267602409693792311983)
        ·
          refine ⟨228601901403614540688467975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 152401267602409693792311983 228601901403614540688467975)
          ·
            refine ⟨342902852105421811032701963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 228601901403614540688467975 342902852105421811032701963)
            ·
              refine ⟨514354278158132716549052945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 342902852105421811032701963 514354278158132716549052945)
              ·
                refine ⟨385765708618599537411789709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 514354278158132716549052945 385765708618599537411789709)
                ·
                  refine ⟨144662140731974826529421141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 385765708618599537411789709 144662140731974826529421141)
                  ·
                    refine ⟨847629730851414999195827, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 144662140731974826529421141 847629730851414999195827)
                    ·
                      rfl

theorem cell23_4952259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 2, 3, 9].length) (baseStart_4952259 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4952259 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4952259 prefixEnd_4952259 := by exact prefixLift 4952259
  have htrace : WordTrace (prefixWord ++ tailWord_4952259) baseStart_4952259 baseEnd_4952259 := by
    simpa [prefixWord, tailWord_4952259, baseEnd_4952259] using wordTrace_append hprefix tailTrace_4952259
  have hstable : (prefixWord ++ tailWord_4952259).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4952259).length < 2 ^ (prefixWord ++ tailWord_4952259).sum := by decide
  have hdescent : baseEnd_4952259 < baseStart_4952259 := by decide
  rcases family_descends (prefixWord ++ tailWord_4952259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4952260 : List Nat := [2, 3, 3, 1, 2, 1, 1, 4, 1, 2, 3]
def baseStart_4952260 : Nat := 118140960795 + 4952260 * 2 ^ 59
def prefixEnd_4952260 : Nat := 4983230072969 + 3 ^ 40 * 4952260 * 2
def baseEnd_4952260 : Nat := 2542889706034899493674977

theorem tailTrace_4952260 : CollatzResearch.WordTrace tailWord_4952260 prefixEnd_4952260 2542889706034899493674977 := by
  unfold tailWord_4952260
  simp only [CollatzResearch.WordTrace]
  refine ⟨90311880519407636758615117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120415840692543515678153489 90311880519407636758615117)
  ·
    refine ⟨33866955194777863784480669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 90311880519407636758615117 33866955194777863784480669)
    ·
      refine ⟨12700108198041698919180251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33866955194777863784480669 12700108198041698919180251)
      ·
        refine ⟨19050162297062548378770377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12700108198041698919180251 19050162297062548378770377)
        ·
          refine ⟨14287621722796911284077783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19050162297062548378770377 14287621722796911284077783)
          ·
            refine ⟨21431432584195366926116675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14287621722796911284077783 21431432584195366926116675)
            ·
              refine ⟨32147148876293050389175013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21431432584195366926116675 32147148876293050389175013)
              ·
                refine ⟨6027590414304946947970315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 32147148876293050389175013 6027590414304946947970315)
                ·
                  refine ⟨9041385621457420421955473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6027590414304946947970315 9041385621457420421955473)
                  ·
                    refine ⟨6781039216093065316466605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9041385621457420421955473 6781039216093065316466605)
                    ·
                      refine ⟨2542889706034899493674977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6781039216093065316466605 2542889706034899493674977)
                      ·
                        rfl

theorem cell23_4952260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 1, 4, 1, 2, 3].length) (baseStart_4952260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4952260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4952260 prefixEnd_4952260 := by exact prefixLift 4952260
  have htrace : WordTrace (prefixWord ++ tailWord_4952260) baseStart_4952260 baseEnd_4952260 := by
    simpa [prefixWord, tailWord_4952260, baseEnd_4952260] using wordTrace_append hprefix tailTrace_4952260
  have hstable : (prefixWord ++ tailWord_4952260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4952260).length < 2 ^ (prefixWord ++ tailWord_4952260).sum := by decide
  have hdescent : baseEnd_4952260 < baseStart_4952260 := by decide
  rcases family_descends (prefixWord ++ tailWord_4952260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4952273 : List Nat := [1, 2, 2, 1, 2, 2, 3, 2, 4, 1, 3]
def baseStart_4952273 : Nat := 118140960795 + 4952273 * 2 ^ 59
def prefixEnd_4952273 : Nat := 4983230072969 + 3 ^ 40 * 4952273 * 2
def baseEnd_4952273 : Nat := 2542896381283407942812417

theorem tailTrace_4952273 : CollatzResearch.WordTrace tailWord_4952273 prefixEnd_4952273 2542896381283407942812417 := by
  unfold tailWord_4952273
  simp only [CollatzResearch.WordTrace]
  refine ⟨180624235187768176737453473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120416156791845451158302315 180624235187768176737453473)
  ·
    refine ⟨135468176390826132553090105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 180624235187768176737453473 135468176390826132553090105)
    ·
      refine ⟨101601132293119599414817579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 135468176390826132553090105 101601132293119599414817579)
      ·
        refine ⟨152401698439679399122226369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101601132293119599414817579 152401698439679399122226369)
        ·
          refine ⟨114301273829759549341669777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 152401698439679399122226369 114301273829759549341669777)
          ·
            refine ⟨85725955372319662006252333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 114301273829759549341669777 85725955372319662006252333)
            ·
              refine ⟨32147233264619873252344625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 85725955372319662006252333 32147233264619873252344625)
              ·
                refine ⟨24110424948464904939258469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32147233264619873252344625 24110424948464904939258469)
                ·
                  refine ⟨4520704677837169676110963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24110424948464904939258469 4520704677837169676110963)
                  ·
                    refine ⟨6781057016755754514166445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4520704677837169676110963 6781057016755754514166445)
                    ·
                      refine ⟨2542896381283407942812417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6781057016755754514166445 2542896381283407942812417)
                      ·
                        rfl

theorem cell23_4952273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 3, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 3, 2, 4, 1, 3].length) (baseStart_4952273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4952273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4952273 prefixEnd_4952273 := by exact prefixLift 4952273
  have htrace : WordTrace (prefixWord ++ tailWord_4952273) baseStart_4952273 baseEnd_4952273 := by
    simpa [prefixWord, tailWord_4952273, baseEnd_4952273] using wordTrace_append hprefix tailTrace_4952273
  have hstable : (prefixWord ++ tailWord_4952273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4952273).length < 2 ^ (prefixWord ++ tailWord_4952273).sum := by decide
  have hdescent : baseEnd_4952273 < baseStart_4952273 := by decide
  rcases family_descends (prefixWord ++ tailWord_4952273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4952274 : List Nat := [3, 2, 2, 2, 1, 2, 3, 3, 1, 2, 2]
def baseStart_4952274 : Nat := 118140960795 + 4952274 * 2 ^ 59
def prefixEnd_4952274 : Nat := 4983230072969 + 3 ^ 40 * 4952274 * 2
def baseEnd_4952274 : Nat := 2542896894764062438899913

theorem tailTrace_4952274 : CollatzResearch.WordTrace tailWord_4952274 prefixEnd_4952274 2542896894764062438899913 := by
  unfold tailWord_4952274
  simp only [CollatzResearch.WordTrace]
  refine ⟨45156067915191138477059969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 120416181107176369272159917 45156067915191138477059969)
  ·
    refine ⟨33867050936393353857794977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45156067915191138477059969 33867050936393353857794977)
    ·
      refine ⟨25400288202295015393346233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33867050936393353857794977 25400288202295015393346233)
      ·
        refine ⟨19050216151721261545009675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25400288202295015393346233 19050216151721261545009675)
        ·
          refine ⟨28575324227581892317514513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19050216151721261545009675 28575324227581892317514513)
          ·
            refine ⟨21431493170686419238135885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28575324227581892317514513 21431493170686419238135885)
            ·
              refine ⟨8036809939007407214300957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21431493170686419238135885 8036809939007407214300957)
              ·
                refine ⟨3013803727127777705362859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8036809939007407214300957 3013803727127777705362859)
                ·
                  refine ⟨4520705590691666558044289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3013803727127777705362859 4520705590691666558044289)
                  ·
                    refine ⟨3390529193018749918533217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4520705590691666558044289 3390529193018749918533217)
                    ·
                      refine ⟨2542896894764062438899913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3390529193018749918533217 2542896894764062438899913)
                      ·
                        rfl

theorem cell23_4952274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 3, 3, 1, 2, 2].length) (baseStart_4952274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4952274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4952274 prefixEnd_4952274 := by exact prefixLift 4952274
  have htrace : WordTrace (prefixWord ++ tailWord_4952274) baseStart_4952274 baseEnd_4952274 := by
    simpa [prefixWord, tailWord_4952274, baseEnd_4952274] using wordTrace_append hprefix tailTrace_4952274
  have hstable : (prefixWord ++ tailWord_4952274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4952274).length < 2 ^ (prefixWord ++ tailWord_4952274).sum := by decide
  have hdescent : baseEnd_4952274 < baseStart_4952274 := by decide
  rcases family_descends (prefixWord ++ tailWord_4952274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4952291 : List Nat := [1, 1, 1, 8, 2, 1, 1, 1, 3, 2, 2]
def baseStart_4952291 : Nat := 118140960795 + 4952291 * 2 ^ 59
def prefixEnd_4952291 : Nat := 4983230072969 + 3 ^ 40 * 4952291 * 2
def baseEnd_4952291 : Nat := 2542905623935188872387335

theorem tailTrace_4952291 : CollatzResearch.WordTrace tailWord_4952291 prefixEnd_4952291 2542905623935188872387335 := by
  unfold tailWord_4952291
  simp only [CollatzResearch.WordTrace]
  refine ⟨180624891701702965811608727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120416594467801977207739151 180624891701702965811608727)
  ·
    refine ⟨270937337552554448717413091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 180624891701702965811608727 270937337552554448717413091)
    ·
      refine ⟨406406006328831673076119637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 270937337552554448717413091 406406006328831673076119637)
      ·
        refine ⟨4762570386665996168860777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 406406006328831673076119637 4762570386665996168860777)
        ·
          refine ⟨3571927789999497126645583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4762570386665996168860777 3571927789999497126645583)
          ·
            refine ⟨5357891684999245689968375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3571927789999497126645583 5357891684999245689968375)
            ·
              refine ⟨8036837527498868534952563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5357891684999245689968375 8036837527498868534952563)
              ·
                refine ⟨12055256291248302802428845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8036837527498868534952563 12055256291248302802428845)
                ·
                  refine ⟨4520721109218113550910817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12055256291248302802428845 4520721109218113550910817)
                  ·
                    refine ⟨3390540831913585163183113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4520721109218113550910817 3390540831913585163183113)
                    ·
                      refine ⟨2542905623935188872387335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3390540831913585163183113 2542905623935188872387335)
                      ·
                        rfl

theorem cell23_4952291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 2, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 2, 1, 1, 1, 3, 2, 2].length) (baseStart_4952291 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4952291 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4952291 prefixEnd_4952291 := by exact prefixLift 4952291
  have htrace : WordTrace (prefixWord ++ tailWord_4952291) baseStart_4952291 baseEnd_4952291 := by
    simpa [prefixWord, tailWord_4952291, baseEnd_4952291] using wordTrace_append hprefix tailTrace_4952291
  have hstable : (prefixWord ++ tailWord_4952291).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4952291).length < 2 ^ (prefixWord ++ tailWord_4952291).sum := by decide
  have hdescent : baseEnd_4952291 < baseStart_4952291 := by decide
  rcases family_descends (prefixWord ++ tailWord_4952291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4952330 : List Nat := [3, 1, 2, 2, 1, 1, 2, 1, 6, 2, 2]
def baseStart_4952330 : Nat := 118140960795 + 4952330 * 2 ^ 59
def prefixEnd_4952330 : Nat := 4983230072969 + 3 ^ 40 * 4952330 * 2
def baseEnd_4952330 : Nat := 2542925649680714219799655

theorem tailTrace_4952330 : CollatzResearch.WordTrace tailWord_4952330 prefixEnd_4952330 2542925649680714219799655 := by
  unfold tailWord_4952330
  simp only [CollatzResearch.WordTrace]
  refine ⟨45156578537140418868069611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 120417542765707783648185629 45156578537140418868069611)
  ·
    refine ⟨67734867805710628302104417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45156578537140418868069611 67734867805710628302104417)
    ·
      refine ⟨50801150854282971226578313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67734867805710628302104417 50801150854282971226578313)
      ·
        refine ⟨38100863140712228419933735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50801150854282971226578313 38100863140712228419933735)
        ·
          refine ⟨57151294711068342629900603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38100863140712228419933735 57151294711068342629900603)
          ·
            refine ⟨85726942066602513944850905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57151294711068342629900603 85726942066602513944850905)
            ·
              refine ⟨64295206549951885458638179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 85726942066602513944850905 64295206549951885458638179)
              ·
                refine ⟨96442809824927828187957269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 64295206549951885458638179 96442809824927828187957269)
                ·
                  refine ⟨4520756710543491946310497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 96442809824927828187957269 4520756710543491946310497)
                  ·
                    refine ⟨3390567532907618959732873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4520756710543491946310497 3390567532907618959732873)
                    ·
                      refine ⟨2542925649680714219799655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3390567532907618959732873 2542925649680714219799655)
                      ·
                        rfl

theorem cell23_4952330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 2, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 2, 1, 6, 2, 2].length) (baseStart_4952330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4952330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4952330 prefixEnd_4952330 := by exact prefixLift 4952330
  have htrace : WordTrace (prefixWord ++ tailWord_4952330) baseStart_4952330 baseEnd_4952330 := by
    simpa [prefixWord, tailWord_4952330, baseEnd_4952330] using wordTrace_append hprefix tailTrace_4952330
  have hstable : (prefixWord ++ tailWord_4952330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4952330).length < 2 ^ (prefixWord ++ tailWord_4952330).sum := by decide
  have hdescent : baseEnd_4952330 < baseStart_4952330 := by decide
  rcases family_descends (prefixWord ++ tailWord_4952330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4952360 : List Nat := [2, 1, 5, 1, 3, 1, 1, 1, 2, 2, 4]
def baseStart_4952360 : Nat := 118140960795 + 4952360 * 2 ^ 59
def prefixEnd_4952360 : Nat := 4983230072969 + 3 ^ 40 * 4952360 * 2
def baseEnd_4952360 : Nat := 2542941054100349102424517

theorem tailTrace_4952360 : CollatzResearch.WordTrace tailWord_4952360 prefixEnd_4952360 2542941054100349102424517 := by
  unfold tailWord_4952360
  simp only [CollatzResearch.WordTrace]
  refine ⟨90313704169226495297935267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120418272225635327063913689 90313704169226495297935267)
  ·
    refine ⟨135470556253839742946902901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90313704169226495297935267 135470556253839742946902901)
    ·
      refine ⟨12700364648797475901272147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 135470556253839742946902901 12700364648797475901272147)
      ·
        refine ⟨19050546973196213851908221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12700364648797475901272147 19050546973196213851908221)
        ·
          refine ⟨7143955114948580194465583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19050546973196213851908221 7143955114948580194465583)
          ·
            refine ⟨10715932672422870291698375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7143955114948580194465583 10715932672422870291698375)
            ·
              refine ⟨16073899008634305437547563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10715932672422870291698375 16073899008634305437547563)
              ·
                refine ⟨24110848512951458156321345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16073899008634305437547563 24110848512951458156321345)
                ·
                  refine ⟨18083136384713593617241009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24110848512951458156321345 18083136384713593617241009)
                  ·
                    refine ⟨13562352288535195212930757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18083136384713593617241009 13562352288535195212930757)
                    ·
                      refine ⟨2542941054100349102424517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13562352288535195212930757 2542941054100349102424517)
                      ·
                        rfl

theorem cell23_4952360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 1, 1, 1, 2, 2, 4].length) (baseStart_4952360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4952360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4952360 prefixEnd_4952360 := by exact prefixLift 4952360
  have htrace : WordTrace (prefixWord ++ tailWord_4952360) baseStart_4952360 baseEnd_4952360 := by
    simpa [prefixWord, tailWord_4952360, baseEnd_4952360] using wordTrace_append hprefix tailTrace_4952360
  have hstable : (prefixWord ++ tailWord_4952360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4952360).length < 2 ^ (prefixWord ++ tailWord_4952360).sum := by decide
  have hdescent : baseEnd_4952360 < baseStart_4952360 := by decide
  rcases family_descends (prefixWord ++ tailWord_4952360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4952376 : List Nat := [2, 1, 2, 1, 3, 1, 2, 2, 1, 1, 7]
def baseStart_4952376 : Nat := 118140960795 + 4952376 * 2 ^ 59
def prefixEnd_4952376 : Nat := 4983230072969 + 3 ^ 40 * 4952376 * 2
def baseEnd_4952376 : Nat := 2542949269790821039824443

theorem tailTrace_4952376 : CollatzResearch.WordTrace tailWord_4952376 prefixEnd_4952376 2542949269790821039824443 := by
  unfold tailWord_4952376
  simp only [CollatzResearch.WordTrace]
  refine ⟨90313995953197512664226491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120418661270930016885635321 90313995953197512664226491)
  ·
    refine ⟨135470993929796268996339737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90313995953197512664226491 135470993929796268996339737)
    ·
      refine ⟨101603245447347201747254803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 135470993929796268996339737 101603245447347201747254803)
      ·
        refine ⟨152404868171020802620882205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101603245447347201747254803 152404868171020802620882205)
        ·
          refine ⟨57151825564132800982830827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 152404868171020802620882205 57151825564132800982830827)
          ·
            refine ⟨85727738346199201474246241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57151825564132800982830827 85727738346199201474246241)
            ·
              refine ⟨64295803759649401105684681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 85727738346199201474246241 64295803759649401105684681)
              ·
                refine ⟨48221852819737050829263511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 64295803759649401105684681 48221852819737050829263511)
                ·
                  refine ⟨72332779229605576243895267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 48221852819737050829263511 72332779229605576243895267)
                  ·
                    refine ⟨108499168844408364365842901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 72332779229605576243895267 108499168844408364365842901)
                    ·
                      refine ⟨2542949269790821039824443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 108499168844408364365842901 2542949269790821039824443)
                      ·
                        rfl

theorem cell23_4952376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 2, 2, 1, 1, 7].length) (baseStart_4952376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4952376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4952376 prefixEnd_4952376 := by exact prefixLift 4952376
  have htrace : WordTrace (prefixWord ++ tailWord_4952376) baseStart_4952376 baseEnd_4952376 := by
    simpa [prefixWord, tailWord_4952376, baseEnd_4952376] using wordTrace_append hprefix tailTrace_4952376
  have hstable : (prefixWord ++ tailWord_4952376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4952376).length < 2 ^ (prefixWord ++ tailWord_4952376).sum := by decide
  have hdescent : baseEnd_4952376 < baseStart_4952376 := by decide
  rcases family_descends (prefixWord ++ tailWord_4952376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4952420 : List Nat := [2, 3, 1, 1, 3, 1, 1, 3, 2, 4, 2]
def baseStart_4952420 : Nat := 118140960795 + 4952420 * 2 ^ 59
def prefixEnd_4952420 : Nat := 4983230072969 + 3 ^ 40 * 4952420 * 2
def baseEnd_4952420 : Nat := 2542971862939618867674241

theorem tailTrace_4952420 : CollatzResearch.WordTrace tailWord_4952420 prefixEnd_4952420 2542971862939618867674241 := by
  unfold tailWord_4952420
  simp only [CollatzResearch.WordTrace]
  refine ⟨90314798359117810421527357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120419731145490413895369809 90314798359117810421527357)
  ·
    refine ⟨33868049384669178908072759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 90314798359117810421527357 33868049384669178908072759)
    ·
      refine ⟨50802074077003768362109139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33868049384669178908072759 50802074077003768362109139)
      ·
        refine ⟨76203111115505652543163709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50802074077003768362109139 76203111115505652543163709)
        ·
          refine ⟨28576166668314619703686391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 76203111115505652543163709 28576166668314619703686391)
          ·
            refine ⟨42864250002471929555529587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28576166668314619703686391 42864250002471929555529587)
            ·
              refine ⟨64296375003707894333294381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42864250002471929555529587 64296375003707894333294381)
              ·
                refine ⟨24111140626390460374985393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 64296375003707894333294381 24111140626390460374985393)
                ·
                  refine ⟨18083355469792845281239045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24111140626390460374985393 18083355469792845281239045)
                  ·
                    refine ⟨3390629150586158490232321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18083355469792845281239045 3390629150586158490232321)
                    ·
                      refine ⟨2542971862939618867674241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3390629150586158490232321 2542971862939618867674241)
                      ·
                        rfl

theorem cell23_4952420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 1, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 1, 3, 2, 4, 2].length) (baseStart_4952420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4952420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4952420 prefixEnd_4952420 := by exact prefixLift 4952420
  have htrace : WordTrace (prefixWord ++ tailWord_4952420) baseStart_4952420 baseEnd_4952420 := by
    simpa [prefixWord, tailWord_4952420, baseEnd_4952420] using wordTrace_append hprefix tailTrace_4952420
  have hstable : (prefixWord ++ tailWord_4952420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4952420).length < 2 ^ (prefixWord ++ tailWord_4952420).sum := by decide
  have hdescent : baseEnd_4952420 < baseStart_4952420 := by decide
  rcases family_descends (prefixWord ++ tailWord_4952420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4952473 : List Nat := [1, 2, 1, 2, 1, 4, 2, 2, 3, 5]
def baseStart_4952473 : Nat := 118140960795 + 4952473 * 2 ^ 59
def prefixEnd_4952473 : Nat := 4983230072969 + 3 ^ 40 * 4952473 * 2
def baseEnd_4952473 : Nat := 847666359138102386770499

theorem tailTrace_4952473 : CollatzResearch.WordTrace tailWord_4952473 prefixEnd_4952473 847666359138102386770499 := by
  unfold tailWord_4952473
  simp only [CollatzResearch.WordTrace]
  refine ⟨180631529787043610894734073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120421019858029073929822715 180631529787043610894734073)
  ·
    refine ⟨135473647340282708171050555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 180631529787043610894734073 135473647340282708171050555)
    ·
      refine ⟨203210471010424062256575833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 135473647340282708171050555 203210471010424062256575833)
      ·
        refine ⟨152407853257818046692431875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 203210471010424062256575833 152407853257818046692431875)
        ·
          refine ⟨228611779886727070038647813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 152407853257818046692431875 228611779886727070038647813)
          ·
            refine ⟨42864708728761325632246465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 228611779886727070038647813 42864708728761325632246465)
            ·
              refine ⟨32148531546570994224184849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42864708728761325632246465 32148531546570994224184849)
              ·
                refine ⟨24111398659928245668138637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32148531546570994224184849 24111398659928245668138637)
                ·
                  refine ⟨9041774497473092125551989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24111398659928245668138637 9041774497473092125551989)
                  ·
                    refine ⟨847666359138102386770499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9041774497473092125551989 847666359138102386770499)
                    ·
                      rfl

theorem cell23_4952473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 2, 2, 3, 5].length) (baseStart_4952473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4952473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4952473 prefixEnd_4952473 := by exact prefixLift 4952473
  have htrace : WordTrace (prefixWord ++ tailWord_4952473) baseStart_4952473 baseEnd_4952473 := by
    simpa [prefixWord, tailWord_4952473, baseEnd_4952473] using wordTrace_append hprefix tailTrace_4952473
  have hstable : (prefixWord ++ tailWord_4952473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4952473).length < 2 ^ (prefixWord ++ tailWord_4952473).sum := by decide
  have hdescent : baseEnd_4952473 < baseStart_4952473 := by decide
  rcases family_descends (prefixWord ++ tailWord_4952473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4952497 : List Nat := [1, 2, 2, 4, 1, 2, 1, 3, 2, 3, 2]
def baseStart_4952497 : Nat := 118140960795 + 4952497 * 2 ^ 59
def prefixEnd_4952497 : Nat := 4983230072969 + 3 ^ 40 * 4952497 * 2
def baseEnd_4952497 : Nat := 2543011400950015066411387

theorem tailTrace_4952497 : CollatzResearch.WordTrace tailWord_4952497 prefixEnd_4952497 2543011400950015066411387 := by
  unfold tailWord_4952497
  simp only [CollatzResearch.WordTrace]
  refine ⟨180632405138956662993607745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120421603425971108662405163 180632405138956662993607745)
  ·
    refine ⟨135474303854217497245205809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 180632405138956662993607745 135474303854217497245205809)
    ·
      refine ⟨101605727890663122933904357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 135474303854217497245205809 101605727890663122933904357)
      ·
        refine ⟨19051073979499335550107067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 101605727890663122933904357 19051073979499335550107067)
        ·
          refine ⟨28576610969249003325160601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19051073979499335550107067 28576610969249003325160601)
          ·
            refine ⟨21432458226936752493870451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28576610969249003325160601 21432458226936752493870451)
            ·
              refine ⟨32148687340405128740805677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21432458226936752493870451 32148687340405128740805677)
              ·
                refine ⟨12055757752651923277802129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32148687340405128740805677 12055757752651923277802129)
                ·
                  refine ⟨9041818314488942458351597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12055757752651923277802129 9041818314488942458351597)
                  ·
                    refine ⟨3390681867933353421881849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9041818314488942458351597 3390681867933353421881849)
                    ·
                      refine ⟨2543011400950015066411387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3390681867933353421881849 2543011400950015066411387)
                      ·
                        rfl

theorem cell23_4952497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 1, 3, 2, 3, 2].length) (baseStart_4952497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4952497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4952497 prefixEnd_4952497 := by exact prefixLift 4952497
  have htrace : WordTrace (prefixWord ++ tailWord_4952497) baseStart_4952497 baseEnd_4952497 := by
    simpa [prefixWord, tailWord_4952497, baseEnd_4952497] using wordTrace_append hprefix tailTrace_4952497
  have hstable : (prefixWord ++ tailWord_4952497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4952497).length < 2 ^ (prefixWord ++ tailWord_4952497).sum := by decide
  have hdescent : baseEnd_4952497 < baseStart_4952497 := by decide
  rcases family_descends (prefixWord ++ tailWord_4952497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4952503 : List Nat := [1, 1, 3, 1, 3, 3, 1, 1, 3, 6]
def baseStart_4952503 : Nat := 118140960795 + 4952503 * 2 ^ 59
def prefixEnd_4952503 : Nat := 4983230072969 + 3 ^ 40 * 4952503 * 2
def baseEnd_4952503 : Nat := 847671493944647347645453

theorem tailTrace_4952503 : CollatzResearch.WordTrace tailWord_4952503 prefixEnd_4952503 847671493944647347645453 := by
  unfold tailWord_4952503
  simp only [CollatzResearch.WordTrace]
  refine ⟨180632623976934926018326163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120421749317956617345550775 180632623976934926018326163)
  ·
    refine ⟨270948935965402389027489245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 180632623976934926018326163 270948935965402389027489245)
    ·
      refine ⟨101605850987025895885308467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 270948935965402389027489245 101605850987025895885308467)
      ·
        refine ⟨152408776480538843827962701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101605850987025895885308467 152408776480538843827962701)
        ·
          refine ⟨57153291180202066435486013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 152408776480538843827962701 57153291180202066435486013)
          ·
            refine ⟨21432484192575774913307255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 57153291180202066435486013 21432484192575774913307255)
            ·
              refine ⟨32148726288863662369960883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21432484192575774913307255 32148726288863662369960883)
              ·
                refine ⟨48223089433295493554941325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32148726288863662369960883 48223089433295493554941325)
                ·
                  refine ⟨18083658537485810083102997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 48223089433295493554941325 18083658537485810083102997)
                  ·
                    refine ⟨847671493944647347645453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18083658537485810083102997 847671493944647347645453)
                    ·
                      rfl

theorem cell23_4952503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 1, 1, 3, 6].length) (baseStart_4952503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4952503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4952503 prefixEnd_4952503 := by exact prefixLift 4952503
  have htrace : WordTrace (prefixWord ++ tailWord_4952503) baseStart_4952503 baseEnd_4952503 := by
    simpa [prefixWord, tailWord_4952503, baseEnd_4952503] using wordTrace_append hprefix tailTrace_4952503
  have hstable : (prefixWord ++ tailWord_4952503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4952503).length < 2 ^ (prefixWord ++ tailWord_4952503).sum := by decide
  have hdescent : baseEnd_4952503 < baseStart_4952503 := by decide
  rcases family_descends (prefixWord ++ tailWord_4952503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4952523 : List Nat := [1, 1, 1, 1, 3, 3, 1, 1, 5, 2, 4]
def baseStart_4952523 : Nat := 118140960795 + 4952523 * 2 ^ 59
def prefixEnd_4952523 : Nat := 4983230072969 + 3 ^ 40 * 4952523 * 2
def baseEnd_4952523 : Nat := 2543024751447031964686267

theorem tailTrace_4952523 : CollatzResearch.WordTrace tailWord_4952523 prefixEnd_4952523 2543024751447031964686267 := by
  unfold tailWord_4952523
  simp only [CollatzResearch.WordTrace]
  refine ⟨180633353436862469434054223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120422235624574979622702815 180633353436862469434054223)
  ·
    refine ⟨270950030155293704151081335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 180633353436862469434054223 270950030155293704151081335)
    ·
      refine ⟨406425045232940556226622003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 270950030155293704151081335 406425045232940556226622003)
      ·
        refine ⟨609637567849410834339933005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 406425045232940556226622003 609637567849410834339933005)
        ·
          refine ⟨228614087943529062877474877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 609637567849410834339933005 228614087943529062877474877)
          ·
            refine ⟨85730282978823398579053079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 228614087943529062877474877 85730282978823398579053079)
            ·
              refine ⟨128595424468235097868579619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 85730282978823398579053079 128595424468235097868579619)
              ·
                refine ⟨192893136702352646802869429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 128595424468235097868579619 192893136702352646802869429)
                ·
                  refine ⟨18083731565845560637769009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 192893136702352646802869429 18083731565845560637769009)
                  ·
                    refine ⟨13562798674384170478326757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18083731565845560637769009 13562798674384170478326757)
                    ·
                      refine ⟨2543024751447031964686267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13562798674384170478326757 2543024751447031964686267)
                      ·
                        rfl

theorem cell23_4952523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 1, 5, 2, 4].length) (baseStart_4952523 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4952523 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4952523 prefixEnd_4952523 := by exact prefixLift 4952523
  have htrace : WordTrace (prefixWord ++ tailWord_4952523) baseStart_4952523 baseEnd_4952523 := by
    simpa [prefixWord, tailWord_4952523, baseEnd_4952523] using wordTrace_append hprefix tailTrace_4952523
  have hstable : (prefixWord ++ tailWord_4952523).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4952523).length < 2 ^ (prefixWord ++ tailWord_4952523).sum := by decide
  have hdescent : baseEnd_4952523 < baseStart_4952523 := by decide
  rcases family_descends (prefixWord ++ tailWord_4952523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4952527 : List Nat := [1, 1, 2, 1, 1, 4, 1, 5, 3, 2, 2]
def baseStart_4952527 : Nat := 118140960795 + 4952527 * 2 ^ 59
def prefixEnd_4952527 : Nat := 4983230072969 + 3 ^ 40 * 4952527 * 2
def baseEnd_4952527 : Nat := 2543026805369649949036249

theorem tailTrace_4952527 : CollatzResearch.WordTrace tailWord_4952527 prefixEnd_4952527 2543026805369649949036249 := by
  unfold tailWord_4952527
  simp only [CollatzResearch.WordTrace]
  refine ⟨180633499328847978117199835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120422332885898652078133223 180633499328847978117199835)
  ·
    refine ⟨270950248993271967175799753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 180633499328847978117199835 270950248993271967175799753)
    ·
      refine ⟨203212686744953975381849815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 270950248993271967175799753 203212686744953975381849815)
      ·
        refine ⟨304819030117430963072774723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 203212686744953975381849815 304819030117430963072774723)
        ·
          refine ⟨457228545176146444609162085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 304819030117430963072774723 457228545176146444609162085)
          ·
            refine ⟨85730352220527458364217891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 457228545176146444609162085 85730352220527458364217891)
            ·
              refine ⟨128595528330791187546326837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 85730352220527458364217891 128595528330791187546326837)
              ·
                refine ⟨12055830781011673832468141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 128595528330791187546326837 12055830781011673832468141)
                ·
                  refine ⟨4520936542879377687175553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12055830781011673832468141 4520936542879377687175553)
                  ·
                    refine ⟨3390702407159533265381665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4520936542879377687175553 3390702407159533265381665)
                    ·
                      refine ⟨2543026805369649949036249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3390702407159533265381665 2543026805369649949036249)
                      ·
                        rfl

theorem cell23_4952527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 5, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 5, 3, 2, 2].length) (baseStart_4952527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4952527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4952527 prefixEnd_4952527 := by exact prefixLift 4952527
  have htrace : WordTrace (prefixWord ++ tailWord_4952527) baseStart_4952527 baseEnd_4952527 := by
    simpa [prefixWord, tailWord_4952527, baseEnd_4952527] using wordTrace_append hprefix tailTrace_4952527
  have hstable : (prefixWord ++ tailWord_4952527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4952527).length < 2 ^ (prefixWord ++ tailWord_4952527).sum := by decide
  have hdescent : baseEnd_4952527 < baseStart_4952527 := by decide
  rcases family_descends (prefixWord ++ tailWord_4952527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4952557 : List Nat := [1, 5, 1, 3, 1, 1, 2, 2, 1, 2, 4]
def baseStart_4952557 : Nat := 118140960795 + 4952557 * 2 ^ 59
def prefixEnd_4952557 : Nat := 4983230072969 + 3 ^ 40 * 4952557 * 2
def baseEnd_4952557 : Nat := 2543042209789284831661111

theorem tailTrace_4952557 : CollatzResearch.WordTrace tailWord_4952557 prefixEnd_4952557 2543042209789284831661111 := by
  unfold tailWord_4952557
  simp only [CollatzResearch.WordTrace]
  refine ⟨180634593518739293240791925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120423062345826195493861283 180634593518739293240791925)
  ·
    refine ⟨16934493142381808741324243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 180634593518739293240791925 16934493142381808741324243)
    ·
      refine ⟨25401739713572713111986365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16934493142381808741324243 25401739713572713111986365)
      ·
        refine ⟨9525652392589767416994887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25401739713572713111986365 9525652392589767416994887)
        ·
          refine ⟨14288478588884651125492331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9525652392589767416994887 14288478588884651125492331)
          ·
            refine ⟨21432717883326976688238497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14288478588884651125492331 21432717883326976688238497)
            ·
              refine ⟨16074538412495232516178873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21432717883326976688238497 16074538412495232516178873)
              ·
                refine ⟨12055903809371424387134155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16074538412495232516178873 12055903809371424387134155)
                ·
                  refine ⟨18083855714057136580701233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12055903809371424387134155 18083855714057136580701233)
                  ·
                    refine ⟨13562891785542852435525925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18083855714057136580701233 13562891785542852435525925)
                    ·
                      refine ⟨2543042209789284831661111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13562891785542852435525925 2543042209789284831661111)
                      ·
                        rfl

theorem cell23_4952557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 2, 2, 1, 2, 4].length) (baseStart_4952557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4952557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4952557 prefixEnd_4952557 := by exact prefixLift 4952557
  have htrace : WordTrace (prefixWord ++ tailWord_4952557) baseStart_4952557 baseEnd_4952557 := by
    simpa [prefixWord, tailWord_4952557, baseEnd_4952557] using wordTrace_append hprefix tailTrace_4952557
  have hstable : (prefixWord ++ tailWord_4952557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4952557).length < 2 ^ (prefixWord ++ tailWord_4952557).sum := by decide
  have hdescent : baseEnd_4952557 < baseStart_4952557 := by decide
  rcases family_descends (prefixWord ++ tailWord_4952557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4952560 : List Nat := [2, 1, 1, 1, 3, 3, 1, 4, 1, 3, 3]
def baseStart_4952560 : Nat := 118140960795 + 4952560 * 2 ^ 59
def prefixEnd_4952560 : Nat := 4983230072969 + 3 ^ 40 * 4952560 * 2
def baseEnd_4952560 : Nat := 2543043750231248319923597

theorem tailTrace_4952560 : CollatzResearch.WordTrace tailWord_4952560 prefixEnd_4952560 2543043750231248319923597 := by
  unfold tailWord_4952560
  simp only [CollatzResearch.WordTrace]
  refine ⟨90317351468864212376575567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120423135291818949835434089 90317351468864212376575567)
  ·
    refine ⟨135476027203296318564863351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90317351468864212376575567 135476027203296318564863351)
    ·
      refine ⟨203214040804944477847295027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 135476027203296318564863351 203214040804944477847295027)
      ·
        refine ⟨304821061207416716770942541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 203214040804944477847295027 304821061207416716770942541)
        ·
          refine ⟨114307897952781268789103453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 304821061207416716770942541 114307897952781268789103453)
          ·
            refine ⟨42865461732292975795913795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 114307897952781268789103453 42865461732292975795913795)
            ·
              refine ⟨64298192598439463693870693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42865461732292975795913795 64298192598439463693870693)
              ·
                refine ⟨12055911112207399442600755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 64298192598439463693870693 12055911112207399442600755)
                ·
                  refine ⟨18083866668311099163901133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12055911112207399442600755 18083866668311099163901133)
                  ·
                    refine ⟨6781450000616662186462925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18083866668311099163901133 6781450000616662186462925)
                    ·
                      refine ⟨2543043750231248319923597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6781450000616662186462925 2543043750231248319923597)
                      ·
                        rfl

theorem cell23_4952560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 1, 4, 1, 3, 3].length) (baseStart_4952560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4952560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4952560 prefixEnd_4952560 := by exact prefixLift 4952560
  have htrace : WordTrace (prefixWord ++ tailWord_4952560) baseStart_4952560 baseEnd_4952560 := by
    simpa [prefixWord, tailWord_4952560, baseEnd_4952560] using wordTrace_append hprefix tailTrace_4952560
  have hstable : (prefixWord ++ tailWord_4952560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4952560).length < 2 ^ (prefixWord ++ tailWord_4952560).sum := by decide
  have hdescent : baseEnd_4952560 < baseStart_4952560 := by decide
  rcases family_descends (prefixWord ++ tailWord_4952560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4952561 : List Nat := [1, 2, 2, 2, 3, 1, 4, 3, 1, 2, 2]
def baseStart_4952561 : Nat := 118140960795 + 4952561 * 2 ^ 59
def prefixEnd_4952561 : Nat := 4983230072969 + 3 ^ 40 * 4952561 * 2
def baseEnd_4952561 : Nat := 2543044263711902816011093

theorem tailTrace_4952561 : CollatzResearch.WordTrace tailWord_4952561 prefixEnd_4952561 2543044263711902816011093 := by
  unfold tailWord_4952561
  simp only [CollatzResearch.WordTrace]
  refine ⟨180634739410724801923937537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120423159607149867949291691 180634739410724801923937537)
  ·
    refine ⟨135476054558043601442953153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 180634739410724801923937537 135476054558043601442953153)
    ·
      refine ⟨101607040918532701082214865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 135476054558043601442953153 101607040918532701082214865)
      ·
        refine ⟨76205280688899525811661149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 101607040918532701082214865 76205280688899525811661149)
        ·
          refine ⟨28576980258337322179372931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 76205280688899525811661149 28576980258337322179372931)
          ·
            refine ⟨42865470387505983269059397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28576980258337322179372931 42865470387505983269059397)
            ·
              refine ⟨8037275697657371862948637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 42865470387505983269059397 8037275697657371862948637)
              ·
                refine ⟨3013978386621514448605739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8037275697657371862948637 3013978386621514448605739)
                ·
                  refine ⟨4520967579932271672908609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3013978386621514448605739 4520967579932271672908609)
                  ·
                    refine ⟨3390725684949203754681457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4520967579932271672908609 3390725684949203754681457)
                    ·
                      refine ⟨2543044263711902816011093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3390725684949203754681457 2543044263711902816011093)
                      ·
                        rfl

theorem cell23_4952561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 4, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 4, 3, 1, 2, 2].length) (baseStart_4952561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4952561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4952561 prefixEnd_4952561 := by exact prefixLift 4952561
  have htrace : WordTrace (prefixWord ++ tailWord_4952561) baseStart_4952561 baseEnd_4952561 := by
    simpa [prefixWord, tailWord_4952561, baseEnd_4952561] using wordTrace_append hprefix tailTrace_4952561
  have hstable : (prefixWord ++ tailWord_4952561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4952561).length < 2 ^ (prefixWord ++ tailWord_4952561).sum := by decide
  have hdescent : baseEnd_4952561 < baseStart_4952561 := by decide
  rcases family_descends (prefixWord ++ tailWord_4952561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4952578 : List Nat := [3, 4, 1, 2, 2, 1, 2, 1, 3, 2, 2]
def baseStart_4952578 : Nat := 118140960795 + 4952578 * 2 ^ 59
def prefixEnd_4952578 : Nat := 4983230072969 + 3 ^ 40 * 4952578 * 2
def baseEnd_4952578 : Nat := 2543052992883029249498515

theorem tailTrace_4952578 : CollatzResearch.WordTrace tailWord_4952578 prefixEnd_4952578 2543052992883029249498515 := by
  unfold tailWord_4952578
  simp only [CollatzResearch.WordTrace]
  refine ⟨45158839862915803456826597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 120423572967775475884870925 45158839862915803456826597)
  ·
    refine ⟨8467282474296713148154987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 45158839862915803456826597 8467282474296713148154987)
    ·
      refine ⟨12700923711445069722232481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8467282474296713148154987 12700923711445069722232481)
      ·
        refine ⟨9525692783583802291674361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12700923711445069722232481 9525692783583802291674361)
        ·
          refine ⟨7144269587687851718755771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9525692783583802291674361 7144269587687851718755771)
          ·
            refine ⟨10716404381531777578133657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7144269587687851718755771 10716404381531777578133657)
            ·
              refine ⟨8037303286148833183600243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10716404381531777578133657 8037303286148833183600243)
              ·
                refine ⟨12055954929223249775400365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8037303286148833183600243 12055954929223249775400365)
                ·
                  refine ⟨4520983098458718665775137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12055954929223249775400365 4520983098458718665775137)
                  ·
                    refine ⟨3390737323844038999331353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4520983098458718665775137 3390737323844038999331353)
                    ·
                      refine ⟨2543052992883029249498515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3390737323844038999331353 2543052992883029249498515)
                      ·
                        rfl

theorem cell23_4952578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 1, 2, 1, 3, 2, 2].length) (baseStart_4952578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4952578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4952578 prefixEnd_4952578 := by exact prefixLift 4952578
  have htrace : WordTrace (prefixWord ++ tailWord_4952578) baseStart_4952578 baseEnd_4952578 := by
    simpa [prefixWord, tailWord_4952578, baseEnd_4952578] using wordTrace_append hprefix tailTrace_4952578
  have hstable : (prefixWord ++ tailWord_4952578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4952578).length < 2 ^ (prefixWord ++ tailWord_4952578).sum := by decide
  have hdescent : baseEnd_4952578 < baseStart_4952578 := by decide
  rcases family_descends (prefixWord ++ tailWord_4952578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4952593 : List Nat := [1, 2, 2, 1, 1, 2, 2, 3, 1, 8]
def baseStart_4952593 : Nat := 118140960795 + 4952593 * 2 ^ 59
def prefixEnd_4952593 : Nat := 4983230072969 + 3 ^ 40 * 4952593 * 2
def baseEnd_4952593 : Nat := 847686898364282230270315

theorem tailTrace_4952593 : CollatzResearch.WordTrace tailWord_4952593 prefixEnd_4952593 847686898364282230270315 := by
  unfold tailWord_4952593
  simp only [CollatzResearch.WordTrace]
  refine ⟨180635906546608871389102433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120423937697739247592734955 180635906546608871389102433)
  ·
    refine ⟨135476929909956653541826825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 180635906546608871389102433 135476929909956653541826825)
    ·
      refine ⟨101607697432467490156370119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 135476929909956653541826825 101607697432467490156370119)
      ·
        refine ⟨152411546148701235234555179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101607697432467490156370119 152411546148701235234555179)
        ·
          refine ⟨228617319223051852851832769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 152411546148701235234555179 228617319223051852851832769)
          ·
            refine ⟨171462989417288889638874577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 228617319223051852851832769 171462989417288889638874577)
            ·
              refine ⟨128597242062966667229155933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 171462989417288889638874577 128597242062966667229155933)
              ·
                refine ⟨48223965773612500210933475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 128597242062966667229155933 48223965773612500210933475)
                ·
                  refine ⟨72335948660418750316400213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 48223965773612500210933475 72335948660418750316400213)
                  ·
                    refine ⟨847686898364282230270315, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 72335948660418750316400213 847686898364282230270315)
                    ·
                      rfl

theorem cell23_4952593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 8].length) (baseStart_4952593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4952593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4952593 prefixEnd_4952593 := by exact prefixLift 4952593
  have htrace : WordTrace (prefixWord ++ tailWord_4952593) baseStart_4952593 baseEnd_4952593 := by
    simpa [prefixWord, tailWord_4952593, baseEnd_4952593] using wordTrace_append hprefix tailTrace_4952593
  have hstable : (prefixWord ++ tailWord_4952593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4952593).length < 2 ^ (prefixWord ++ tailWord_4952593).sum := by decide
  have hdescent : baseEnd_4952593 < baseStart_4952593 := by decide
  rcases family_descends (prefixWord ++ tailWord_4952593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4952603 : List Nat := [1, 1, 1, 1, 1, 1, 3, 1, 5, 3, 5]
def baseStart_4952603 : Nat := 118140960795 + 4952603 * 2 ^ 59
def prefixEnd_4952603 : Nat := 4983230072969 + 3 ^ 40 * 4952603 * 2
def baseEnd_4952603 : Nat := 2543065829899391651685899

theorem tailTrace_4952603 : CollatzResearch.WordTrace tailWord_4952603 prefixEnd_4952603 2543065829899391651685899 := by
  unfold tailWord_4952603
  simp only [CollatzResearch.WordTrace]
  refine ⟨180636271276572643096966463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120424180851048428731310975 180636271276572643096966463)
  ·
    refine ⟨270954406914858964645449695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 180636271276572643096966463 270954406914858964645449695)
    ·
      refine ⟨406431610372288446968174543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 270954406914858964645449695 406431610372288446968174543)
      ·
        refine ⟨609647415558432670452261815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 406431610372288446968174543 609647415558432670452261815)
        ·
          refine ⟨914471123337649005678392723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 609647415558432670452261815 914471123337649005678392723)
          ·
            refine ⟨1371706685006473508517589085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 914471123337649005678392723 1371706685006473508517589085)
            ·
              refine ⟨514390006877427565694095907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1371706685006473508517589085 514390006877427565694095907)
              ·
                refine ⟨771585010316141348541143861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 514390006877427565694095907 771585010316141348541143861)
                ·
                  refine ⟨72336094717138251425732237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 771585010316141348541143861 72336094717138251425732237)
                  ·
                    refine ⟨27126035518926844284649589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 72336094717138251425732237 27126035518926844284649589)
                    ·
                      refine ⟨2543065829899391651685899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27126035518926844284649589 2543065829899391651685899)
                      ·
                        rfl

theorem cell23_4952603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 5, 3, 5].length) (baseStart_4952603 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4952603 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4952603 prefixEnd_4952603 := by exact prefixLift 4952603
  have htrace : WordTrace (prefixWord ++ tailWord_4952603) baseStart_4952603 baseEnd_4952603 := by
    simpa [prefixWord, tailWord_4952603, baseEnd_4952603] using wordTrace_append hprefix tailTrace_4952603
  have hstable : (prefixWord ++ tailWord_4952603).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4952603).length < 2 ^ (prefixWord ++ tailWord_4952603).sum := by decide
  have hdescent : baseEnd_4952603 < baseStart_4952603 := by decide
  rcases family_descends (prefixWord ++ tailWord_4952603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4952604 : List Nat := [2, 2, 3, 1, 2, 2, 1, 4, 1, 3, 2]
def baseStart_4952604 : Nat := 118140960795 + 4952604 * 2 ^ 59
def prefixEnd_4952604 : Nat := 4983230072969 + 3 ^ 40 * 4952604 * 2
def baseEnd_4952604 : Nat := 2543066343380046147773395

theorem tailTrace_4952604 : CollatzResearch.WordTrace tailWord_4952604 prefixEnd_4952604 2543066343380046147773395 := by
  unfold tailWord_4952604
  simp only [CollatzResearch.WordTrace]
  refine ⟨90318153874784510133876433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120424205166379346845168577 90318153874784510133876433)
  ·
    refine ⟨67738615406088382600407325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90318153874784510133876433 67738615406088382600407325)
    ·
      refine ⟨25401980777283143475152747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 67738615406088382600407325 25401980777283143475152747)
      ·
        refine ⟨38102971165924715212729121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25401980777283143475152747 38102971165924715212729121)
        ·
          refine ⟨28577228374443536409546841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38102971165924715212729121 28577228374443536409546841)
          ·
            refine ⟨21432921280832652307160131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28577228374443536409546841 21432921280832652307160131)
            ·
              refine ⟨32149381921248978460740197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21432921280832652307160131 32149381921248978460740197)
              ·
                refine ⟨6028009110234183461388787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 32149381921248978460740197 6028009110234183461388787)
                ·
                  refine ⟨9042013665351275192083181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6028009110234183461388787 9042013665351275192083181)
                  ·
                    refine ⟨3390755124506728197031193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9042013665351275192083181 3390755124506728197031193)
                    ·
                      refine ⟨2543066343380046147773395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3390755124506728197031193 2543066343380046147773395)
                      ·
                        rfl

theorem cell23_4952604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 1, 4, 1, 3, 2].length) (baseStart_4952604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4952604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4952604 prefixEnd_4952604 := by exact prefixLift 4952604
  have htrace : WordTrace (prefixWord ++ tailWord_4952604) baseStart_4952604 baseEnd_4952604 := by
    simpa [prefixWord, tailWord_4952604, baseEnd_4952604] using wordTrace_append hprefix tailTrace_4952604
  have hstable : (prefixWord ++ tailWord_4952604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4952604).length < 2 ^ (prefixWord ++ tailWord_4952604).sum := by decide
  have hdescent : baseEnd_4952604 < baseStart_4952604 := by decide
  rcases family_descends (prefixWord ++ tailWord_4952604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4952612 : List Nat := [2, 3, 1, 5, 2, 1, 1, 3, 1, 2, 2]
def baseStart_4952612 : Nat := 118140960795 + 4952612 * 2 ^ 59
def prefixEnd_4952612 : Nat := 4983230072969 + 3 ^ 40 * 4952612 * 2
def baseEnd_4952612 : Nat := 2543070451225282116473359

theorem tailTrace_4952612 : CollatzResearch.WordTrace tailWord_4952612 prefixEnd_4952612 2543070451225282116473359 := by
  unfold tailWord_4952612
  simp only [CollatzResearch.WordTrace]
  refine ⟨90318299766770018817022045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120424399689026691756029393 90318299766770018817022045)
  ·
    refine ⟨33869362412538757056383267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 90318299766770018817022045 33869362412538757056383267)
    ·
      refine ⟨50804043618808135584574901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33869362412538757056383267 50804043618808135584574901)
      ·
        refine ⟨4762879089263262711053897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 50804043618808135584574901 4762879089263262711053897)
        ·
          refine ⟨3572159316947447033290423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4762879089263262711053897 3572159316947447033290423)
          ·
            refine ⟨5358238975421170549935635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3572159316947447033290423 5358238975421170549935635)
            ·
              refine ⟨8037358463131755824903453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5358238975421170549935635 8037358463131755824903453)
              ·
                refine ⟨3014009423674408434338795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8037358463131755824903453 3014009423674408434338795)
                ·
                  refine ⟨4521014135511612651508193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3014009423674408434338795 4521014135511612651508193)
                  ·
                    refine ⟨3390760601633709488631145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4521014135511612651508193 3390760601633709488631145)
                    ·
                      refine ⟨2543070451225282116473359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3390760601633709488631145 2543070451225282116473359)
                      ·
                        rfl

theorem cell23_4952612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 2, 1, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 2, 1, 1, 3, 1, 2, 2].length) (baseStart_4952612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4952612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4952612 prefixEnd_4952612 := by exact prefixLift 4952612
  have htrace : WordTrace (prefixWord ++ tailWord_4952612) baseStart_4952612 baseEnd_4952612 := by
    simpa [prefixWord, tailWord_4952612, baseEnd_4952612] using wordTrace_append hprefix tailTrace_4952612
  have hstable : (prefixWord ++ tailWord_4952612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4952612).length < 2 ^ (prefixWord ++ tailWord_4952612).sum := by decide
  have hdescent : baseEnd_4952612 < baseStart_4952612 := by decide
  rcases family_descends (prefixWord ++ tailWord_4952612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4952634 : List Nat := [3, 1, 1, 1, 3, 3, 2, 1, 4, 2, 2]
def baseStart_4952634 : Nat := 118140960795 + 4952634 * 2 ^ 59
def prefixEnd_4952634 : Nat := 4983230072969 + 3 ^ 40 * 4952634 * 2
def baseEnd_4952634 : Nat := 2543081747799681030398257

theorem tailTrace_4952634 : CollatzResearch.WordTrace tailWord_4952634 prefixEnd_4952634 2543081747799681030398257 := by
  unfold tailWord_4952634
  simp only [CollatzResearch.WordTrace]
  refine ⟨45159350484865083847836239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 120424934626306890260896637 45159350484865083847836239)
  ·
    refine ⟨67739025727297625771754359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45159350484865083847836239 67739025727297625771754359)
    ·
      refine ⟨101608538590946438657631539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67739025727297625771754359 101608538590946438657631539)
      ·
        refine ⟨152412807886419657986447309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101608538590946438657631539 152412807886419657986447309)
        ·
          refine ⟨57154802957407371744917741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 152412807886419657986447309 57154802957407371744917741)
          ·
            refine ⟨21433051109027764404344153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 57154802957407371744917741 21433051109027764404344153)
            ·
              refine ⟨16074788331770823303258115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21433051109027764404344153 16074788331770823303258115)
              ·
                refine ⟨24112182497656234954887173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16074788331770823303258115 24112182497656234954887173)
                ·
                  refine ⟨4521034218310544054041345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24112182497656234954887173 4521034218310544054041345)
                  ·
                    refine ⟨3390775663732908040531009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4521034218310544054041345 3390775663732908040531009)
                    ·
                      refine ⟨2543081747799681030398257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3390775663732908040531009 2543081747799681030398257)
                      ·
                        rfl

theorem cell23_4952634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 2, 1, 4, 2, 2].length) (baseStart_4952634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4952634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4952634 prefixEnd_4952634 := by exact prefixLift 4952634
  have htrace : WordTrace (prefixWord ++ tailWord_4952634) baseStart_4952634 baseEnd_4952634 := by
    simpa [prefixWord, tailWord_4952634, baseEnd_4952634] using wordTrace_append hprefix tailTrace_4952634
  have hstable : (prefixWord ++ tailWord_4952634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4952634).length < 2 ^ (prefixWord ++ tailWord_4952634).sum := by decide
  have hdescent : baseEnd_4952634 < baseStart_4952634 := by decide
  rcases family_descends (prefixWord ++ tailWord_4952634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4952640 : List Nat := [2, 1, 1, 2, 2, 2, 5, 1, 7]
def baseStart_4952640 : Nat := 118140960795 + 4952640 * 2 ^ 59
def prefixEnd_4952640 : Nat := 4983230072969 + 3 ^ 40 * 4952640 * 2
def baseEnd_4952640 : Nat := 282564980964845334102581

theorem tailTrace_4952640 : CollatzResearch.WordTrace tailWord_4952640 prefixEnd_4952640 282564980964845334102581 := by
  unfold tailWord_4952640
  simp only [CollatzResearch.WordTrace]
  refine ⟨90318810388719299208031687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120425080518292398944042249 90318810388719299208031687)
  ·
    refine ⟨135478215583078948812047531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90318810388719299208031687 135478215583078948812047531)
    ·
      refine ⟨203217323374618423218071297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 135478215583078948812047531 203217323374618423218071297)
      ·
        refine ⟨152412992530963817413553473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 203217323374618423218071297 152412992530963817413553473)
        ·
          refine ⟨114309744398222863060165105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 152412992530963817413553473 114309744398222863060165105)
          ·
            refine ⟨85732308298667147295123829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 114309744398222863060165105 85732308298667147295123829)
            ·
              refine ⟨8037403903000045058917859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 85732308298667147295123829 8037403903000045058917859)
              ·
                refine ⟨12056105854500067588376789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8037403903000045058917859 12056105854500067588376789)
                ·
                  refine ⟨282564980964845334102581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12056105854500067588376789 282564980964845334102581)
                  ·
                    rfl

theorem cell23_4952640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 5, 1, 7].length) (baseStart_4952640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4952640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4952640 prefixEnd_4952640 := by exact prefixLift 4952640
  have htrace : WordTrace (prefixWord ++ tailWord_4952640) baseStart_4952640 baseEnd_4952640 := by
    simpa [prefixWord, tailWord_4952640, baseEnd_4952640] using wordTrace_append hprefix tailTrace_4952640
  have hstable : (prefixWord ++ tailWord_4952640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4952640).length < 2 ^ (prefixWord ++ tailWord_4952640).sum := by decide
  have hdescent : baseEnd_4952640 < baseStart_4952640 := by decide
  rcases family_descends (prefixWord ++ tailWord_4952640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4952651 : List Nat := [1, 1, 1, 1, 3, 1, 8, 1, 2, 2, 2]
def baseStart_4952651 : Nat := 118140960795 + 4952651 * 2 ^ 59
def prefixEnd_4952651 : Nat := 4983230072969 + 3 ^ 40 * 4952651 * 2
def baseEnd_4952651 : Nat := 2543090476970807463885679

theorem tailTrace_4952651 : CollatzResearch.WordTrace tailWord_4952651 prefixEnd_4952651 2543090476970807463885679 := by
  unfold tailWord_4952651
  simp only [CollatzResearch.WordTrace]
  refine ⟨180638021980398747294713807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120425347986932498196475871 180638021980398747294713807)
  ·
    refine ⟨270957032970598120942070711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 180638021980398747294713807 270957032970598120942070711)
    ·
      refine ⟨406435549455897181413106067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 270957032970598120942070711 406435549455897181413106067)
      ·
        refine ⟨609653324183845772119659101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 406435549455897181413106067 609653324183845772119659101)
        ·
          refine ⟨228619996568942164544872163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 609653324183845772119659101 228619996568942164544872163)
          ·
            refine ⟨342929994853413246817308245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 228619996568942164544872163 342929994853413246817308245)
            ·
              refine ⟨4018710877188436486140331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 342929994853413246817308245 4018710877188436486140331)
              ·
                refine ⟨6028066315782654729210497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4018710877188436486140331 6028066315782654729210497)
                ·
                  refine ⟨4521049736836991046907873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6028066315782654729210497 4521049736836991046907873)
                  ·
                    refine ⟨3390787302627743285180905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4521049736836991046907873 3390787302627743285180905)
                    ·
                      refine ⟨2543090476970807463885679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3390787302627743285180905 2543090476970807463885679)
                      ·
                        rfl

theorem cell23_4952651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 8, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 8, 1, 2, 2, 2].length) (baseStart_4952651 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4952651 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4952651 prefixEnd_4952651 := by exact prefixLift 4952651
  have htrace : WordTrace (prefixWord ++ tailWord_4952651) baseStart_4952651 baseEnd_4952651 := by
    simpa [prefixWord, tailWord_4952651, baseEnd_4952651] using wordTrace_append hprefix tailTrace_4952651
  have hstable : (prefixWord ++ tailWord_4952651).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4952651).length < 2 ^ (prefixWord ++ tailWord_4952651).sum := by decide
  have hdescent : baseEnd_4952651 < baseStart_4952651 := by decide
  rcases family_descends (prefixWord ++ tailWord_4952651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4952707 : List Nat := [1, 1, 1, 3, 3, 1, 3, 1, 1, 6, 2]
def baseStart_4952707 : Nat := 118140960795 + 4952707 * 2 ^ 59
def prefixEnd_4952707 : Nat := 4983230072969 + 3 ^ 40 * 4952707 * 2
def baseEnd_4952707 : Nat := 2543119231887459244785421

theorem tailTrace_4952707 : CollatzResearch.WordTrace tailWord_4952707 prefixEnd_4952707 2543119231887459244785421 := by
  unfold tailWord_4952707
  simp only [CollatzResearch.WordTrace]
  refine ⟨180640064468195868858752375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120426709645463912572501583 180640064468195868858752375)
  ·
    refine ⟨270960096702293803288128563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 180640064468195868858752375 270960096702293803288128563)
    ·
      refine ⟨406440145053440704932192845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 270960096702293803288128563 406440145053440704932192845)
      ·
        refine ⟨152415054395040264349572317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 406440145053440704932192845 152415054395040264349572317)
        ·
          refine ⟨57155645398140099131089619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 152415054395040264349572317 57155645398140099131089619)
          ·
            refine ⟨85733468097210148696634429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57155645398140099131089619 85733468097210148696634429)
            ·
              refine ⟨32150050536453805761237911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 85733468097210148696634429 32150050536453805761237911)
              ·
                refine ⟨48225075804680708641856867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32150050536453805761237911 48225075804680708641856867)
                ·
                  refine ⟨72337613707021062962785301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 48225075804680708641856867 72337613707021062962785301)
                  ·
                    refine ⟨3390825642516612326380561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 72337613707021062962785301 3390825642516612326380561)
                    ·
                      refine ⟨2543119231887459244785421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3390825642516612326380561 2543119231887459244785421)
                      ·
                        rfl

theorem cell23_4952707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 3, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 3, 1, 1, 6, 2].length) (baseStart_4952707 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4952707 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4952707 prefixEnd_4952707 := by exact prefixLift 4952707
  have htrace : WordTrace (prefixWord ++ tailWord_4952707) baseStart_4952707 baseEnd_4952707 := by
    simpa [prefixWord, tailWord_4952707, baseEnd_4952707] using wordTrace_append hprefix tailTrace_4952707
  have hstable : (prefixWord ++ tailWord_4952707).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4952707).length < 2 ^ (prefixWord ++ tailWord_4952707).sum := by decide
  have hdescent : baseEnd_4952707 < baseStart_4952707 := by decide
  rcases family_descends (prefixWord ++ tailWord_4952707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4952724 : List Nat := [2, 4, 2, 2, 1, 2, 1, 1, 1, 3, 4]
def baseStart_4952724 : Nat := 118140960795 + 4952724 * 2 ^ 59
def prefixEnd_4952724 : Nat := 4983230072969 + 3 ^ 40 * 4952724 * 2
def baseEnd_4952724 : Nat := 2543127961058585678272843

theorem tailTrace_4952724 : CollatzResearch.WordTrace tailWord_4952724 prefixEnd_4952724 2543127961058585678272843 := by
  unfold tailWord_4952724
  simp only [CollatzResearch.WordTrace]
  refine ⟨90320342254567140381060613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120427123006089520508080817 90320342254567140381060613)
  ·
    refine ⟨16935064172731338821448865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 90320342254567140381060613 16935064172731338821448865)
    ·
      refine ⟨12701298129548504116086649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16935064172731338821448865 12701298129548504116086649)
      ·
        refine ⟨9525973597161378087064987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12701298129548504116086649 9525973597161378087064987)
        ·
          refine ⟨14288960395742067130597481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9525973597161378087064987 14288960395742067130597481)
          ·
            refine ⟨10716720296806550347948111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14288960395742067130597481 10716720296806550347948111)
            ·
              refine ⟨16075080445209825521922167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10716720296806550347948111 16075080445209825521922167)
              ·
                refine ⟨24112620667814738282883251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16075080445209825521922167 24112620667814738282883251)
                ·
                  refine ⟨36168931001722107424324877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24112620667814738282883251 36168931001722107424324877)
                  ·
                    refine ⟨13563349125645790284121829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 36168931001722107424324877 13563349125645790284121829)
                    ·
                      refine ⟨2543127961058585678272843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13563349125645790284121829 2543127961058585678272843)
                      ·
                        rfl

theorem cell23_4952724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 2, 1, 1, 1, 3, 4].length) (baseStart_4952724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4952724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4952724 prefixEnd_4952724 := by exact prefixLift 4952724
  have htrace : WordTrace (prefixWord ++ tailWord_4952724) baseStart_4952724 baseEnd_4952724 := by
    simpa [prefixWord, tailWord_4952724, baseEnd_4952724] using wordTrace_append hprefix tailTrace_4952724
  have hstable : (prefixWord ++ tailWord_4952724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4952724).length < 2 ^ (prefixWord ++ tailWord_4952724).sum := by decide
  have hdescent : baseEnd_4952724 < baseStart_4952724 := by decide
  rcases family_descends (prefixWord ++ tailWord_4952724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4952727 : List Nat := [1, 1, 3, 3, 2, 1, 3, 1, 1, 4, 3]
def baseStart_4952727 : Nat := 118140960795 + 4952727 * 2 ^ 59
def prefixEnd_4952727 : Nat := 4983230072969 + 3 ^ 40 * 4952727 * 2
def baseEnd_4952727 : Nat := 2543129501500549166535329

theorem tailTrace_4952727 : CollatzResearch.WordTrace tailWord_4952727 prefixEnd_4952727 2543129501500549166535329 := by
  unfold tailWord_4952727
  simp only [CollatzResearch.WordTrace]
  refine ⟨180640793928123412274480435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120427195952082274849653623 180640793928123412274480435)
  ·
    refine ⟨270961190892185118411720653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 180640793928123412274480435 270961190892185118411720653)
    ·
      refine ⟨101610446584569419404395245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 270961190892185118411720653 101610446584569419404395245)
      ·
        refine ⟨38103917469213532276648217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 101610446584569419404395245 38103917469213532276648217)
        ·
          refine ⟨28577938101910149207486163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38103917469213532276648217 28577938101910149207486163)
          ·
            refine ⟨42866907152865223811229245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28577938101910149207486163 42866907152865223811229245)
            ·
              refine ⟨16075090182324458929210967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 42866907152865223811229245 16075090182324458929210967)
              ·
                refine ⟨24112635273486688393816451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16075090182324458929210967 24112635273486688393816451)
                ·
                  refine ⟨36168952910230032590724677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24112635273486688393816451 36168952910230032590724677)
                  ·
                    refine ⟨6781678670668131110760877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 36168952910230032590724677 6781678670668131110760877)
                    ·
                      refine ⟨2543129501500549166535329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6781678670668131110760877 2543129501500549166535329)
                      ·
                        rfl

theorem cell23_4952727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 3, 1, 1, 4, 3].length) (baseStart_4952727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4952727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4952727 prefixEnd_4952727 := by exact prefixLift 4952727
  have htrace : WordTrace (prefixWord ++ tailWord_4952727) baseStart_4952727 baseEnd_4952727 := by
    simpa [prefixWord, tailWord_4952727, baseEnd_4952727] using wordTrace_append hprefix tailTrace_4952727
  have hstable : (prefixWord ++ tailWord_4952727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4952727).length < 2 ^ (prefixWord ++ tailWord_4952727).sum := by decide
  have hdescent : baseEnd_4952727 < baseStart_4952727 := by decide
  rcases family_descends (prefixWord ++ tailWord_4952727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4952734 : List Nat := [4, 3, 1, 1, 1, 1, 1, 2, 5, 4]
def baseStart_4952734 : Nat := 118140960795 + 4952734 * 2 ^ 59
def prefixEnd_4952734 : Nat := 4983230072969 + 3 ^ 40 * 4952734 * 2
def baseEnd_4952734 : Nat := 847711031955043546382599

theorem tailTrace_4952734 : CollatzResearch.WordTrace tailWord_4952734 prefixEnd_4952734 847711031955043546382599 := by
  unfold tailWord_4952734
  simp only [CollatzResearch.WordTrace]
  refine ⟨22580131154887256558748157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 120427366159398701646656837 22580131154887256558748157)
  ·
    refine ⟨8467549183082721209530559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22580131154887256558748157 8467549183082721209530559)
    ·
      refine ⟨12701323774624081814295839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8467549183082721209530559 12701323774624081814295839)
      ·
        refine ⟨19051985661936122721443759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12701323774624081814295839 19051985661936122721443759)
        ·
          refine ⟨28577978492904184082165639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19051985661936122721443759 28577978492904184082165639)
          ·
            refine ⟨42866967739356276123248459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28577978492904184082165639 42866967739356276123248459)
            ·
              refine ⟨64300451609034414184872689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42866967739356276123248459 64300451609034414184872689)
              ·
                refine ⟨48225338706775810638654517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 64300451609034414184872689 48225338706775810638654517)
                ·
                  refine ⟨4521125503760232247373861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 48225338706775810638654517 4521125503760232247373861)
                  ·
                    refine ⟨847711031955043546382599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4521125503760232247373861 847711031955043546382599)
                    ·
                      rfl

theorem cell23_4952734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 1, 2, 5, 4].length) (baseStart_4952734 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4952734 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4952734 prefixEnd_4952734 := by exact prefixLift 4952734
  have htrace : WordTrace (prefixWord ++ tailWord_4952734) baseStart_4952734 baseEnd_4952734 := by
    simpa [prefixWord, tailWord_4952734, baseEnd_4952734] using wordTrace_append hprefix tailTrace_4952734
  have hstable : (prefixWord ++ tailWord_4952734).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4952734).length < 2 ^ (prefixWord ++ tailWord_4952734).sum := by decide
  have hdescent : baseEnd_4952734 < baseStart_4952734 := by decide
  rcases family_descends (prefixWord ++ tailWord_4952734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4952764 : List Nat := [2, 2, 2, 3, 1, 1, 5, 1, 6]
def baseStart_4952764 : Nat := 118140960795 + 4952764 * 2 ^ 59
def prefixEnd_4952764 : Nat := 4983230072969 + 3 ^ 40 * 4952764 * 2
def baseEnd_4952764 : Nat := 282572055587196169085851

theorem tailTrace_4952764 : CollatzResearch.WordTrace tailWord_4952764 prefixEnd_4952764 282572055587196169085851 := by
  unfold tailWord_4952764
  simp only [CollatzResearch.WordTrace]
  refine ⟨90321071714494683796788673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120428095619326245062384897 90321071714494683796788673)
  ·
    refine ⟨67740803785871012847591505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90321071714494683796788673 67740803785871012847591505)
    ·
      refine ⟨50805602839403259635693629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67740803785871012847591505 50805602839403259635693629)
      ·
        refine ⟨19052101064776222363385111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 50805602839403259635693629 19052101064776222363385111)
        ·
          refine ⟨28578151597164333545077667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19052101064776222363385111 28578151597164333545077667)
          ·
            refine ⟨42867227395746500317616501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28578151597164333545077667 42867227395746500317616501)
            ·
              refine ⟨4018802568351234404776547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 42867227395746500317616501 4018802568351234404776547)
              ·
                refine ⟨6028203852526851607164821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4018802568351234404776547 6028203852526851607164821)
                ·
                  refine ⟨282572055587196169085851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6028203852526851607164821 282572055587196169085851)
                  ·
                    rfl

theorem cell23_4952764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 5, 1, 6].length) (baseStart_4952764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4952764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4952764 prefixEnd_4952764 := by exact prefixLift 4952764
  have htrace : WordTrace (prefixWord ++ tailWord_4952764) baseStart_4952764 baseEnd_4952764 := by
    simpa [prefixWord, tailWord_4952764, baseEnd_4952764] using wordTrace_append hprefix tailTrace_4952764
  have hstable : (prefixWord ++ tailWord_4952764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4952764).length < 2 ^ (prefixWord ++ tailWord_4952764).sum := by decide
  have hdescent : baseEnd_4952764 < baseStart_4952764 := by decide
  rcases family_descends (prefixWord ++ tailWord_4952764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4952801 : List Nat := [1, 2, 3, 1, 4, 2, 1, 2, 2, 3, 2]
def baseStart_4952801 : Nat := 118140960795 + 4952801 * 2 ^ 59
def prefixEnd_4952801 : Nat := 4983230072969 + 3 ^ 40 * 4952801 * 2
def baseEnd_4952801 : Nat := 2543167499068981877009989

theorem tailTrace_4952801 : CollatzResearch.WordTrace tailWord_4952801 prefixEnd_4952801 2543167499068981877009989 := by
  unfold tailWord_4952801
  simp only [CollatzResearch.WordTrace]
  refine ⟨180643492929855322912674257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120428995286570215275116171 180643492929855322912674257)
  ·
    refine ⟨135482619697391492184505693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 180643492929855322912674257 135482619697391492184505693)
    ·
      refine ⟨50805982386521809569189635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 135482619697391492184505693 50805982386521809569189635)
      ·
        refine ⟨76208973579782714353784453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50805982386521809569189635 76208973579782714353784453)
        ·
          refine ⟨14289182546209258941334585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 76208973579782714353784453 14289182546209258941334585)
          ·
            refine ⟨10716886909656944206000939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14289182546209258941334585 10716886909656944206000939)
            ·
              refine ⟨16075330364485416309001409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10716886909656944206000939 16075330364485416309001409)
              ·
                refine ⟨12056497773364062231751057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16075330364485416309001409 12056497773364062231751057)
                ·
                  refine ⟨9042373330023046673813293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12056497773364062231751057 9042373330023046673813293)
                  ·
                    refine ⟨3390889998758642502679985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9042373330023046673813293 3390889998758642502679985)
                    ·
                      refine ⟨2543167499068981877009989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3390889998758642502679985 2543167499068981877009989)
                      ·
                        rfl

theorem cell23_4952801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 2, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 2, 1, 2, 2, 3, 2].length) (baseStart_4952801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4952801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4952801 prefixEnd_4952801 := by exact prefixLift 4952801
  have htrace : WordTrace (prefixWord ++ tailWord_4952801) baseStart_4952801 baseEnd_4952801 := by
    simpa [prefixWord, tailWord_4952801, baseEnd_4952801] using wordTrace_append hprefix tailTrace_4952801
  have hstable : (prefixWord ++ tailWord_4952801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4952801).length < 2 ^ (prefixWord ++ tailWord_4952801).sum := by decide
  have hdescent : baseEnd_4952801 < baseStart_4952801 := by decide
  rcases family_descends (prefixWord ++ tailWord_4952801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4952808 : List Nat := [2, 1, 4, 1, 4, 2, 1, 1, 3, 1, 3]
def baseStart_4952808 : Nat := 118140960795 + 4952808 * 2 ^ 59
def prefixEnd_4952808 : Nat := 4983230072969 + 3 ^ 40 * 4952808 * 2
def baseEnd_4952808 : Nat := 2543171093433563349622457

theorem tailTrace_4952808 : CollatzResearch.WordTrace tailWord_4952808 prefixEnd_4952808 2543171093433563349622457 := by
  unfold tailWord_4952808
  simp only [CollatzResearch.WordTrace]
  refine ⟨90321874120414981554089539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120429165493886642072119385 90321874120414981554089539)
  ·
    refine ⟨135482811180622472331134309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90321874120414981554089539 135482811180622472331134309)
    ·
      refine ⟨25403027096366713562087683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 135482811180622472331134309 25403027096366713562087683)
      ·
        refine ⟨38104540644550070343131525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25403027096366713562087683 38104540644550070343131525)
        ·
          refine ⟨7144601370853138189337161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 38104540644550070343131525 7144601370853138189337161)
          ·
            refine ⟨5358451028139853642002871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7144601370853138189337161 5358451028139853642002871)
            ·
              refine ⟨8037676542209780463004307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5358451028139853642002871 8037676542209780463004307)
              ·
                refine ⟨12056514813314670694506461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8037676542209780463004307 12056514813314670694506461)
                ·
                  refine ⟨4521193054993001510439923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12056514813314670694506461 4521193054993001510439923)
                  ·
                    refine ⟨6781789582489502265659885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4521193054993001510439923 6781789582489502265659885)
                    ·
                      refine ⟨2543171093433563349622457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6781789582489502265659885 2543171093433563349622457)
                      ·
                        rfl

theorem cell23_4952808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 2, 1, 1, 3, 1, 3].length) (baseStart_4952808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4952808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4952808 prefixEnd_4952808 := by exact prefixLift 4952808
  have htrace : WordTrace (prefixWord ++ tailWord_4952808) baseStart_4952808 baseEnd_4952808 := by
    simpa [prefixWord, tailWord_4952808, baseEnd_4952808] using wordTrace_append hprefix tailTrace_4952808
  have hstable : (prefixWord ++ tailWord_4952808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4952808).length < 2 ^ (prefixWord ++ tailWord_4952808).sum := by decide
  have hdescent : baseEnd_4952808 < baseStart_4952808 := by decide
  rcases family_descends (prefixWord ++ tailWord_4952808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4952817 : List Nat := [1, 2, 2, 2, 2, 2, 1, 4, 1, 1, 5]
def baseStart_4952817 : Nat := 118140960795 + 4952817 * 2 ^ 59
def prefixEnd_4952817 : Nat := 4983230072969 + 3 ^ 40 * 4952817 * 2
def baseEnd_4952817 : Nat := 2543175714759453814409915

theorem tailTrace_4952817 : CollatzResearch.WordTrace tailWord_4952817 prefixEnd_4952817 2543175714759453814409915 := by
  unfold tailWord_4952817
  simp only [CollatzResearch.WordTrace]
  refine ⟨180644076497797357645256705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120429384331864905096837803 180644076497797357645256705)
  ·
    refine ⟨135483057373348018233942529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 180644076497797357645256705 135483057373348018233942529)
    ·
      refine ⟨101612293030011013675456897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 135483057373348018233942529 101612293030011013675456897)
      ·
        refine ⟨76209219772508260256592673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 101612293030011013675456897 76209219772508260256592673)
        ·
          refine ⟨57156914829381195192444505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 76209219772508260256592673 57156914829381195192444505)
          ·
            refine ⟨42867686122035896394333379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57156914829381195192444505 42867686122035896394333379)
            ·
              refine ⟨64301529183053844591500069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42867686122035896394333379 64301529183053844591500069)
              ·
                refine ⟨12056536721822595860906263, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 64301529183053844591500069 12056536721822595860906263)
                ·
                  refine ⟨18084805082733893791359395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12056536721822595860906263 18084805082733893791359395)
                  ·
                    refine ⟨27127207624100840687039093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18084805082733893791359395 27127207624100840687039093)
                    ·
                      refine ⟨2543175714759453814409915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27127207624100840687039093 2543175714759453814409915)
                      ·
                        rfl

theorem cell23_4952817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 1, 4, 1, 1, 5].length) (baseStart_4952817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4952817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4952817 prefixEnd_4952817 := by exact prefixLift 4952817
  have htrace : WordTrace (prefixWord ++ tailWord_4952817) baseStart_4952817 baseEnd_4952817 := by
    simpa [prefixWord, tailWord_4952817, baseEnd_4952817] using wordTrace_append hprefix tailTrace_4952817
  have hstable : (prefixWord ++ tailWord_4952817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4952817).length < 2 ^ (prefixWord ++ tailWord_4952817).sum := by decide
  have hdescent : baseEnd_4952817 < baseStart_4952817 := by decide
  rcases family_descends (prefixWord ++ tailWord_4952817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4952824 : List Nat := [2, 1, 2, 1, 1, 2, 5, 3, 2, 4]
def baseStart_4952824 : Nat := 118140960795 + 4952824 * 2 ^ 59
def prefixEnd_4952824 : Nat := 4983230072969 + 3 ^ 40 * 4952824 * 2
def baseEnd_4952824 : Nat := 847726436374678429007461

theorem tailTrace_4952824 : CollatzResearch.WordTrace tailWord_4952824 prefixEnd_4952824 847726436374678429007461 := by
  unfold tailWord_4952824
  simp only [CollatzResearch.WordTrace]
  refine ⟨90322165904385998920380763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120429554539181331893841017 90322165904385998920380763)
  ·
    refine ⟨135483248856578998380571145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90322165904385998920380763 135483248856578998380571145)
    ·
      refine ⟨101612436642434248785428359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 135483248856578998380571145 101612436642434248785428359)
      ·
        refine ⟨152418654963651373178142539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101612436642434248785428359 152418654963651373178142539)
        ·
          refine ⟨228627982445477059767213809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 152418654963651373178142539 228627982445477059767213809)
          ·
            refine ⟨171470986834107794825410357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 228627982445477059767213809 171470986834107794825410357)
            ·
              refine ⟨16075405015697605764882221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 171470986834107794825410357 16075405015697605764882221)
              ·
                refine ⟨6028276880886602161830833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16075405015697605764882221 6028276880886602161830833)
                ·
                  refine ⟨4521207660664951621373125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6028276880886602161830833 4521207660664951621373125)
                  ·
                    refine ⟨847726436374678429007461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4521207660664951621373125 847726436374678429007461)
                    ·
                      rfl

theorem cell23_4952824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 5, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 5, 3, 2, 4].length) (baseStart_4952824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4952824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4952824 prefixEnd_4952824 := by exact prefixLift 4952824
  have htrace : WordTrace (prefixWord ++ tailWord_4952824) baseStart_4952824 baseEnd_4952824 := by
    simpa [prefixWord, tailWord_4952824, baseEnd_4952824] using wordTrace_append hprefix tailTrace_4952824
  have hstable : (prefixWord ++ tailWord_4952824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4952824).length < 2 ^ (prefixWord ++ tailWord_4952824).sum := by decide
  have hdescent : baseEnd_4952824 < baseStart_4952824 := by decide
  rcases family_descends (prefixWord ++ tailWord_4952824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4952851 : List Nat := [1, 1, 1, 2, 1, 3, 7, 1, 1, 2, 3]
def baseStart_4952851 : Nat := 118140960795 + 4952851 * 2 ^ 59
def prefixEnd_4952851 : Nat := 4983230072969 + 3 ^ 40 * 4952851 * 2
def baseEnd_4952851 : Nat := 2543193173101706681384759

theorem tailTrace_4952851 : CollatzResearch.WordTrace tailWord_4952851 prefixEnd_4952851 2543193173101706681384759 := by
  unfold tailWord_4952851
  simp only [CollatzResearch.WordTrace]
  refine ⟨180645316579674181451994407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120430211053116120967996271 180645316579674181451994407)
  ·
    refine ⟨270967974869511272177991611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 180645316579674181451994407 270967974869511272177991611)
    ·
      refine ⟨406451962304266908266987417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 270967974869511272177991611 406451962304266908266987417)
      ·
        refine ⟨304838971728200181200240563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 406451962304266908266987417 304838971728200181200240563)
        ·
          refine ⟨457258457592300271800360845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 304838971728200181200240563 457258457592300271800360845)
          ·
            refine ⟨171471921597112601925135317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 457258457592300271800360845 171471921597112601925135317)
            ·
              refine ⟨4018873162432326607620359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 171471921597112601925135317 4018873162432326607620359)
              ·
                refine ⟨6028309743648489911430539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4018873162432326607620359 6028309743648489911430539)
                ·
                  refine ⟨9042464615472734867145809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6028309743648489911430539 9042464615472734867145809)
                  ·
                    refine ⟨6781848461604551150359357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9042464615472734867145809 6781848461604551150359357)
                    ·
                      refine ⟨2543193173101706681384759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6781848461604551150359357 2543193173101706681384759)
                      ·
                        rfl

theorem cell23_4952851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 7, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 7, 1, 1, 2, 3].length) (baseStart_4952851 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4952851 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4952851 prefixEnd_4952851 := by exact prefixLift 4952851
  have htrace : WordTrace (prefixWord ++ tailWord_4952851) baseStart_4952851 baseEnd_4952851 := by
    simpa [prefixWord, tailWord_4952851, baseEnd_4952851] using wordTrace_append hprefix tailTrace_4952851
  have hstable : (prefixWord ++ tailWord_4952851).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4952851).length < 2 ^ (prefixWord ++ tailWord_4952851).sum := by decide
  have hdescent : baseEnd_4952851 < baseStart_4952851 := by decide
  rcases family_descends (prefixWord ++ tailWord_4952851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4952881 : List Nat := [1, 2, 2, 3, 2, 1, 1, 5, 2, 1, 3]
def baseStart_4952881 : Nat := 118140960795 + 4952881 * 2 ^ 59
def prefixEnd_4952881 : Nat := 4983230072969 + 3 ^ 40 * 4952881 * 2
def baseEnd_4952881 : Nat := 2543208577521341564009621

theorem tailTrace_4952881 : CollatzResearch.WordTrace tailWord_4952881 prefixEnd_4952881 2543208577521341564009621 := by
  unfold tailWord_4952881
  simp only [CollatzResearch.WordTrace]
  refine ⟨180646410769565496575586497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120430940513043664383724331 180646410769565496575586497)
  ·
    refine ⟨135484808077174122431689873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 180646410769565496575586497 135484808077174122431689873)
    ·
      refine ⟨101613606057880591823767405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 135484808077174122431689873 101613606057880591823767405)
      ·
        refine ⟨38105102271705221933912777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 101613606057880591823767405 38105102271705221933912777)
        ·
          refine ⟨28578826703778916450434583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38105102271705221933912777 28578826703778916450434583)
          ·
            refine ⟨42868240055668374675651875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28578826703778916450434583 42868240055668374675651875)
            ·
              refine ⟨64302360083502562013477813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42868240055668374675651875 64302360083502562013477813)
              ·
                refine ⟨6028346257828365188763545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 64302360083502562013477813 6028346257828365188763545)
                ·
                  refine ⟨4521259693371273891572659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6028346257828365188763545 4521259693371273891572659)
                  ·
                    refine ⟨6781889540056910837358989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4521259693371273891572659 6781889540056910837358989)
                    ·
                      refine ⟨2543208577521341564009621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6781889540056910837358989 2543208577521341564009621)
                      ·
                        rfl

theorem cell23_4952881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 1, 5, 2, 1, 3].length) (baseStart_4952881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4952881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4952881 prefixEnd_4952881 := by exact prefixLift 4952881
  have htrace : WordTrace (prefixWord ++ tailWord_4952881) baseStart_4952881 baseEnd_4952881 := by
    simpa [prefixWord, tailWord_4952881, baseEnd_4952881] using wordTrace_append hprefix tailTrace_4952881
  have hstable : (prefixWord ++ tailWord_4952881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4952881).length < 2 ^ (prefixWord ++ tailWord_4952881).sum := by decide
  have hdescent : baseEnd_4952881 < baseStart_4952881 := by decide
  rcases family_descends (prefixWord ++ tailWord_4952881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4952887 : List Nat := [1, 1, 3, 1, 2, 1, 3, 2, 2, 3, 4]
def baseStart_4952887 : Nat := 118140960795 + 4952887 * 2 ^ 59
def prefixEnd_4952887 : Nat := 4983230072969 + 3 ^ 40 * 4952887 * 2
def baseEnd_4952887 : Nat := 2543211658405268540534593

theorem tailTrace_4952887 : CollatzResearch.WordTrace tailWord_4952887 prefixEnd_4952887 2543211658405268540534593 := by
  unfold tailWord_4952887
  simp only [CollatzResearch.WordTrace]
  refine ⟨180646629607543759600304915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120431086405029173066869943 180646629607543759600304915)
  ·
    refine ⟨270969944411315639400457373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 180646629607543759600304915 270969944411315639400457373)
    ·
      refine ⟨101613729154243364775171515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 270969944411315639400457373 101613729154243364775171515)
      ·
        refine ⟨152420593731365047162757273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101613729154243364775171515 152420593731365047162757273)
        ·
          refine ⟨114315445298523785372067955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 152420593731365047162757273 114315445298523785372067955)
          ·
            refine ⟨171473167947785678058101933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 114315445298523785372067955 171473167947785678058101933)
            ·
              refine ⟨64302437980419629271788225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 171473167947785678058101933 64302437980419629271788225)
              ·
                refine ⟨48226828485314721953841169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 64302437980419629271788225 48226828485314721953841169)
                ·
                  refine ⟨36170121363986041465380877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 48226828485314721953841169 36170121363986041465380877)
                  ·
                    refine ⟨13563795511494765549517829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 36170121363986041465380877 13563795511494765549517829)
                    ·
                      refine ⟨2543211658405268540534593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13563795511494765549517829 2543211658405268540534593)
                      ·
                        rfl

theorem cell23_4952887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 3, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 3, 2, 2, 3, 4].length) (baseStart_4952887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4952887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4952887 prefixEnd_4952887 := by exact prefixLift 4952887
  have htrace : WordTrace (prefixWord ++ tailWord_4952887) baseStart_4952887 baseEnd_4952887 := by
    simpa [prefixWord, tailWord_4952887, baseEnd_4952887] using wordTrace_append hprefix tailTrace_4952887
  have hstable : (prefixWord ++ tailWord_4952887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4952887).length < 2 ^ (prefixWord ++ tailWord_4952887).sum := by decide
  have hdescent : baseEnd_4952887 < baseStart_4952887 := by decide
  rcases family_descends (prefixWord ++ tailWord_4952887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4952908 : List Nat := [2, 2, 1, 3, 3, 2, 1, 3, 1, 3, 2]
def baseStart_4952908 : Nat := 118140960795 + 4952908 * 2 ^ 59
def prefixEnd_4952908 : Nat := 4983230072969 + 3 ^ 40 * 4952908 * 2
def baseEnd_4952908 : Nat := 2543222441499012958371997

theorem tailTrace_4952908 : CollatzResearch.WordTrace tailWord_4952908 prefixEnd_4952908 2543222441499012958371997 := by
  unfold tailWord_4952908
  simp only [CollatzResearch.WordTrace]
  refine ⟨90323697770233840093409689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120431597026978453457879585 90323697770233840093409689)
  ·
    refine ⟨67742773327675380070057267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90323697770233840093409689 67742773327675380070057267)
    ·
      refine ⟨101614159991513070105085901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67742773327675380070057267 101614159991513070105085901)
      ·
        refine ⟨38105309996817401289407213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 101614159991513070105085901 38105309996817401289407213)
        ·
          refine ⟨14289491248806525483527705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38105309996817401289407213 14289491248806525483527705)
          ·
            refine ⟨10717118436604894112645779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14289491248806525483527705 10717118436604894112645779)
            ·
              refine ⟨16075677654907341168968669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10717118436604894112645779 16075677654907341168968669)
              ·
                refine ⟨6028379120590252938363251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16075677654907341168968669 6028379120590252938363251)
                ·
                  refine ⟨9042568680885379407544877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6028379120590252938363251 9042568680885379407544877)
                  ·
                    refine ⟨3390963255332017277829329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9042568680885379407544877 3390963255332017277829329)
                    ·
                      refine ⟨2543222441499012958371997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3390963255332017277829329 2543222441499012958371997)
                      ·
                        rfl

theorem cell23_4952908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 2, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 2, 1, 3, 1, 3, 2].length) (baseStart_4952908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4952908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4952908 prefixEnd_4952908 := by exact prefixLift 4952908
  have htrace : WordTrace (prefixWord ++ tailWord_4952908) baseStart_4952908 baseEnd_4952908 := by
    simpa [prefixWord, tailWord_4952908, baseEnd_4952908] using wordTrace_append hprefix tailTrace_4952908
  have hstable : (prefixWord ++ tailWord_4952908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4952908).length < 2 ^ (prefixWord ++ tailWord_4952908).sum := by decide
  have hdescent : baseEnd_4952908 < baseStart_4952908 := by decide
  rcases family_descends (prefixWord ++ tailWord_4952908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4952958 : List Nat := [4, 2, 3, 1, 2, 1, 1, 1, 2, 1, 5]
def baseStart_4952958 : Nat := 118140960795 + 4952958 * 2 ^ 59
def prefixEnd_4952958 : Nat := 4983230072969 + 3 ^ 40 * 4952958 * 2
def baseEnd_4952958 : Nat := 2543248115531737762746767

theorem tailTrace_4952958 : CollatzResearch.WordTrace tailWord_4952958 prefixEnd_4952958 2543248115531737762746767 := by
  unfold tailWord_4952958
  simp only [CollatzResearch.WordTrace]
  refine ⟨22581152398785817340767441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 120432812793524359150759685 22581152398785817340767441)
  ·
    refine ⟨16935864299089363005575581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22581152398785817340767441 16935864299089363005575581)
    ·
      refine ⟨6350949112158511127090843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16935864299089363005575581 6350949112158511127090843)
      ·
        refine ⟨9526423668237766690636265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6350949112158511127090843 9526423668237766690636265)
        ·
          refine ⟨7144817751178325017977199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9526423668237766690636265 7144817751178325017977199)
          ·
            refine ⟨10717226626767487526965799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7144817751178325017977199 10717226626767487526965799)
            ·
              refine ⟨16075839940151231290448699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10717226626767487526965799 16075839940151231290448699)
              ·
                refine ⟨24113759910226846935673049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16075839940151231290448699 24113759910226846935673049)
                ·
                  refine ⟨18085319932670135201754787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24113759910226846935673049 18085319932670135201754787)
                  ·
                    refine ⟨27127979899005202802632181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18085319932670135201754787 27127979899005202802632181)
                    ·
                      refine ⟨2543248115531737762746767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27127979899005202802632181 2543248115531737762746767)
                      ·
                        rfl

theorem cell23_4952958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 1, 1, 1, 2, 1, 5].length) (baseStart_4952958 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4952958 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4952958 prefixEnd_4952958 := by exact prefixLift 4952958
  have htrace : WordTrace (prefixWord ++ tailWord_4952958) baseStart_4952958 baseEnd_4952958 := by
    simpa [prefixWord, tailWord_4952958, baseEnd_4952958] using wordTrace_append hprefix tailTrace_4952958
  have hstable : (prefixWord ++ tailWord_4952958).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4952958).length < 2 ^ (prefixWord ++ tailWord_4952958).sum := by decide
  have hdescent : baseEnd_4952958 < baseStart_4952958 := by decide
  rcases family_descends (prefixWord ++ tailWord_4952958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4952978 : List Nat := [3, 2, 3, 2, 2, 2, 1, 1, 7]
def baseStart_4952978 : Nat := 118140960795 + 4952978 * 2 ^ 59
def prefixEnd_4952978 : Nat := 4983230072969 + 3 ^ 40 * 4952978 * 2
def baseEnd_4952978 : Nat := 282584265016091964944075

theorem tailTrace_4952978 : CollatzResearch.WordTrace tailWord_4952978 prefixEnd_4952978 282584265016091964944075 := by
  unfold tailWord_4952978
  simp only [CollatzResearch.WordTrace]
  refine ⟨45162487162553520535466897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 120433299100142721427911725 45162487162553520535466897)
  ·
    refine ⟨33871865371915140401600173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45162487162553520535466897 33871865371915140401600173)
    ·
      refine ⟨12701949514468177650600065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33871865371915140401600173 12701949514468177650600065)
      ·
        refine ⟨9526462135851133237950049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12701949514468177650600065 9526462135851133237950049)
        ·
          refine ⟨7144846601888349928462537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9526462135851133237950049 7144846601888349928462537)
          ·
            refine ⟨5358634951416262446346903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7144846601888349928462537 5358634951416262446346903)
            ·
              refine ⟨8037952427124393669520355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5358634951416262446346903 8037952427124393669520355)
              ·
                refine ⟨12056928640686590504280533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8037952427124393669520355 12056928640686590504280533)
                ·
                  refine ⟨282584265016091964944075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12056928640686590504280533 282584265016091964944075)
                  ·
                    rfl

theorem cell23_4952978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 2, 1, 1, 7].length) (baseStart_4952978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4952978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4952978 prefixEnd_4952978 := by exact prefixLift 4952978
  have htrace : WordTrace (prefixWord ++ tailWord_4952978) baseStart_4952978 baseEnd_4952978 := by
    simpa [prefixWord, tailWord_4952978, baseEnd_4952978] using wordTrace_append hprefix tailTrace_4952978
  have hstable : (prefixWord ++ tailWord_4952978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4952978).length < 2 ^ (prefixWord ++ tailWord_4952978).sum := by decide
  have hdescent : baseEnd_4952978 < baseStart_4952978 := by decide
  rcases family_descends (prefixWord ++ tailWord_4952978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4953031 : List Nat := [1, 1, 4, 1, 1, 2, 4, 2, 2, 2, 3]
def baseStart_4953031 : Nat := 118140960795 + 4953031 * 2 ^ 59
def prefixEnd_4953031 : Nat := 4983230072969 + 3 ^ 40 * 4953031 * 2
def baseEnd_4953031 : Nat := 2543285599619515977133931

theorem tailTrace_4953031 : CollatzResearch.WordTrace tailWord_4953031 prefixEnd_4953031 2543285599619515977133931 := by
  unfold tailWord_4953031
  simp only [CollatzResearch.WordTrace]
  refine ⟨180651881719022072193546947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120434587812681381462364631 180651881719022072193546947)
  ·
    refine ⟨270977822578533108290320421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 180651881719022072193546947 270977822578533108290320421)
    ·
      refine ⟨50808341733474957804435079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 270977822578533108290320421 50808341733474957804435079)
      ·
        refine ⟨76212512600212436706652619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50808341733474957804435079 76212512600212436706652619)
        ·
          refine ⟨114318768900318655059978929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76212512600212436706652619 114318768900318655059978929)
          ·
            refine ⟨85739076675238991294984197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 114318768900318655059978929 85739076675238991294984197)
            ·
              refine ⟨16076076876607310867809537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 85739076675238991294984197 16076076876607310867809537)
              ·
                refine ⟨12057057657455483150857153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16076076876607310867809537 12057057657455483150857153)
                ·
                  refine ⟨9042793243091612363142865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12057057657455483150857153 9042793243091612363142865)
                  ·
                    refine ⟨6782094932318709272357149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9042793243091612363142865 6782094932318709272357149)
                    ·
                      refine ⟨2543285599619515977133931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6782094932318709272357149 2543285599619515977133931)
                      ·
                        rfl

theorem cell23_4953031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 4, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 4, 2, 2, 2, 3].length) (baseStart_4953031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4953031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4953031 prefixEnd_4953031 := by exact prefixLift 4953031
  have htrace : WordTrace (prefixWord ++ tailWord_4953031) baseStart_4953031 baseEnd_4953031 := by
    simpa [prefixWord, tailWord_4953031, baseEnd_4953031] using wordTrace_append hprefix tailTrace_4953031
  have hstable : (prefixWord ++ tailWord_4953031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4953031).length < 2 ^ (prefixWord ++ tailWord_4953031).sum := by decide
  have hdescent : baseEnd_4953031 < baseStart_4953031 := by decide
  rcases family_descends (prefixWord ++ tailWord_4953031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4953081 : List Nat := [1, 2, 1, 3, 1, 3, 3, 3, 1, 5]
def baseStart_4953081 : Nat := 118140960795 + 4953081 * 2 ^ 59
def prefixEnd_4953081 : Nat := 4983230072969 + 3 ^ 40 * 4953081 * 2
def baseEnd_4953081 : Nat := 847770424550746927169567

theorem tailTrace_4953081 : CollatzResearch.WordTrace tailWord_4953081 prefixEnd_4953081 847770424550746927169567 := by
  unfold tailWord_4953081
  simp only [CollatzResearch.WordTrace]
  refine ⟨180653705368840930732867097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120435803579227287155244731 180653705368840930732867097)
  ·
    refine ⟨135490279026630698049650323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 180653705368840930732867097 135490279026630698049650323)
    ·
      refine ⟨203235418539946047074475485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 135490279026630698049650323 203235418539946047074475485)
      ·
        refine ⟨76213281952479767652928307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 203235418539946047074475485 76213281952479767652928307)
        ·
          refine ⟨114319922928719651479392461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76213281952479767652928307 114319922928719651479392461)
          ·
            refine ⟨42869971098269869304772173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 114319922928719651479392461 42869971098269869304772173)
            ·
              refine ⟨16076239161851200989289565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 42869971098269869304772173 16076239161851200989289565)
              ·
                refine ⟨6028589685694200370983587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16076239161851200989289565 6028589685694200370983587)
                ·
                  refine ⟨9042884528541300556475381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6028589685694200370983587 9042884528541300556475381)
                  ·
                    refine ⟨847770424550746927169567, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9042884528541300556475381 847770424550746927169567)
                    ·
                      rfl

theorem cell23_4953081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 3, 3, 1, 5].length) (baseStart_4953081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4953081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4953081 prefixEnd_4953081 := by exact prefixLift 4953081
  have htrace : WordTrace (prefixWord ++ tailWord_4953081) baseStart_4953081 baseEnd_4953081 := by
    simpa [prefixWord, tailWord_4953081, baseEnd_4953081] using wordTrace_append hprefix tailTrace_4953081
  have hstable : (prefixWord ++ tailWord_4953081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4953081).length < 2 ^ (prefixWord ++ tailWord_4953081).sum := by decide
  have hdescent : baseEnd_4953081 < baseStart_4953081 := by decide
  rcases family_descends (prefixWord ++ tailWord_4953081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4953095 : List Nat := [1, 1, 4, 3, 1, 1, 1, 6, 1, 1, 3]
def baseStart_4953095 : Nat := 118140960795 + 4953095 * 2 ^ 59
def prefixEnd_4953095 : Nat := 4983230072969 + 3 ^ 40 * 4953095 * 2
def baseEnd_4953095 : Nat := 2543318462381403726733637

theorem tailTrace_4953095 : CollatzResearch.WordTrace tailWord_4953095 prefixEnd_4953095 2543318462381403726733637 := by
  unfold tailWord_4953095
  simp only [CollatzResearch.WordTrace]
  refine ⟨180654215990790211123876739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120436143993860140749251159 180654215990790211123876739)
  ·
    refine ⟨270981323986185316685815109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 180654215990790211123876739 270981323986185316685815109)
    ·
      refine ⟨50808998247409746878590333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 270981323986185316685815109 50808998247409746878590333)
      ·
        refine ⟨19053374342778655079471375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 50808998247409746878590333 19053374342778655079471375)
        ·
          refine ⟨28580061514167982619207063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19053374342778655079471375 28580061514167982619207063)
          ·
            refine ⟨42870092271251973928810595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28580061514167982619207063 42870092271251973928810595)
            ·
              refine ⟨64305138406877960893215893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42870092271251973928810595 64305138406877960893215893)
              ·
                refine ⟨3014303362822404416869495, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 64305138406877960893215893 3014303362822404416869495)
                ·
                  refine ⟨4521455044233606625304243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3014303362822404416869495 4521455044233606625304243)
                  ·
                    refine ⟨6782182566350409937956365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4521455044233606625304243 6782182566350409937956365)
                    ·
                      refine ⟨2543318462381403726733637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6782182566350409937956365 2543318462381403726733637)
                      ·
                        rfl

theorem cell23_4953095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 1, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 1, 6, 1, 1, 3].length) (baseStart_4953095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4953095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4953095 prefixEnd_4953095 := by exact prefixLift 4953095
  have htrace : WordTrace (prefixWord ++ tailWord_4953095) baseStart_4953095 baseEnd_4953095 := by
    simpa [prefixWord, tailWord_4953095, baseEnd_4953095] using wordTrace_append hprefix tailTrace_4953095
  have hstable : (prefixWord ++ tailWord_4953095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4953095).length < 2 ^ (prefixWord ++ tailWord_4953095).sum := by decide
  have hdescent : baseEnd_4953095 < baseStart_4953095 := by decide
  rcases family_descends (prefixWord ++ tailWord_4953095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4953138 : List Nat := [3, 2, 1, 1, 2, 2, 1, 5, 1, 2, 3]
def baseStart_4953138 : Nat := 118140960795 + 4953138 * 2 ^ 59
def prefixEnd_4953138 : Nat := 4983230072969 + 3 ^ 40 * 4953138 * 2
def baseEnd_4953138 : Nat := 2543340542049547058495939

theorem tailTrace_4953138 : CollatzResearch.WordTrace tailWord_4953138 prefixEnd_4953138 2543340542049547058495939 := by
  unfold tailWord_4953138
  simp only [CollatzResearch.WordTrace]
  refine ⟨45163946082408607366923017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 120437189553089619645128045 45163946082408607366923017)
  ·
    refine ⟨33872959561806455525192263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45163946082408607366923017 33872959561806455525192263)
    ·
      refine ⟨50809439342709683287788395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33872959561806455525192263 50809439342709683287788395)
      ·
        refine ⟨76214159014064524931682593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50809439342709683287788395 76214159014064524931682593)
        ·
          refine ⟨57160619260548393698761945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 76214159014064524931682593 57160619260548393698761945)
          ·
            refine ⟨42870464445411295274071459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57160619260548393698761945 42870464445411295274071459)
            ·
              refine ⟨64305696668116942911107189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42870464445411295274071459 64305696668116942911107189)
              ·
                refine ⟨6028659062635963397916299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 64305696668116942911107189 6028659062635963397916299)
                ·
                  refine ⟨9042988593953945096874449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6028659062635963397916299 9042988593953945096874449)
                  ·
                    refine ⟨6782241445465458822655837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9042988593953945096874449 6782241445465458822655837)
                    ·
                      refine ⟨2543340542049547058495939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6782241445465458822655837 2543340542049547058495939)
                      ·
                        rfl

theorem cell23_4953138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 1, 5, 1, 2, 3].length) (baseStart_4953138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4953138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4953138 prefixEnd_4953138 := by exact prefixLift 4953138
  have htrace : WordTrace (prefixWord ++ tailWord_4953138) baseStart_4953138 baseEnd_4953138 := by
    simpa [prefixWord, tailWord_4953138, baseEnd_4953138] using wordTrace_append hprefix tailTrace_4953138
  have hstable : (prefixWord ++ tailWord_4953138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4953138).length < 2 ^ (prefixWord ++ tailWord_4953138).sum := by decide
  have hdescent : baseEnd_4953138 < baseStart_4953138 := by decide
  rcases family_descends (prefixWord ++ tailWord_4953138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4953158 : List Nat := [6, 1, 1, 1, 1, 2, 1, 10]
def baseStart_4953158 : Nat := 118140960795 + 4953158 * 2 ^ 59
def prefixEnd_4953158 : Nat := 4983230072969 + 3 ^ 40 * 4953158 * 2
def baseEnd_4953158 : Nat := 94198178209727295564661

theorem tailTrace_4953158 : CollatzResearch.WordTrace tailWord_4953158 prefixEnd_4953158 94198178209727295564661 := by
  unfold tailWord_4953158
  simp only [CollatzResearch.WordTrace]
  refine ⟨5645516055923811652606879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 120437675859707981922280085 5645516055923811652606879)
  ·
    refine ⟨8468274083885717478910319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5645516055923811652606879 8468274083885717478910319)
    ·
      refine ⟨12702411125828576218365479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8468274083885717478910319 12702411125828576218365479)
      ·
        refine ⟨19053616688742864327548219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12702411125828576218365479 19053616688742864327548219)
        ·
          refine ⟨28580425033114296491322329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19053616688742864327548219 28580425033114296491322329)
          ·
            refine ⟨21435318774835722368491747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28580425033114296491322329 21435318774835722368491747)
            ·
              refine ⟨32152978162253583552737621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21435318774835722368491747 32152978162253583552737621)
              ·
                refine ⟨94198178209727295564661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 32152978162253583552737621 94198178209727295564661)
                ·
                  rfl

theorem cell23_4953158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 1, 10].length) (baseStart_4953158 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4953158 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4953158 prefixEnd_4953158 := by exact prefixLift 4953158
  have htrace : WordTrace (prefixWord ++ tailWord_4953158) baseStart_4953158 baseEnd_4953158 := by
    simpa [prefixWord, tailWord_4953158, baseEnd_4953158] using wordTrace_append hprefix tailTrace_4953158
  have hstable : (prefixWord ++ tailWord_4953158).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4953158).length < 2 ^ (prefixWord ++ tailWord_4953158).sum := by decide
  have hdescent : baseEnd_4953158 < baseStart_4953158 := by decide
  rcases family_descends (prefixWord ++ tailWord_4953158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4953182 : List Nat := [4, 4, 1, 1, 1, 2, 1, 2, 1, 2, 4]
def baseStart_4953182 : Nat := 118140960795 + 4953182 * 2 ^ 59
def prefixEnd_4953182 : Nat := 4983230072969 + 3 ^ 40 * 4953182 * 2
def baseEnd_4953182 : Nat := 2543363135198344886345737

theorem tailTrace_4953182 : CollatzResearch.WordTrace tailWord_4953182 prefixEnd_4953182 2543363135198344886345737 := by
  unfold tailWord_4953182
  simp only [CollatzResearch.WordTrace]
  refine ⟨22582173642684378122786725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 120438259427650016654862533 22582173642684378122786725)
  ·
    refine ⟨4234157558003320898022511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 22582173642684378122786725 4234157558003320898022511)
    ·
      refine ⟨6351236337004981347033767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4234157558003320898022511 6351236337004981347033767)
      ·
        refine ⟨9526854505507472020550651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6351236337004981347033767 9526854505507472020550651)
        ·
          refine ⟨14290281758261208030825977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9526854505507472020550651 14290281758261208030825977)
          ·
            refine ⟨10717711318695906023119483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14290281758261208030825977 10717711318695906023119483)
            ·
              refine ⟨16076566978043859034679225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10717711318695906023119483 16076566978043859034679225)
              ·
                refine ⟨12057425233532894276009419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16076566978043859034679225 12057425233532894276009419)
                ·
                  refine ⟨18086137850299341414014129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12057425233532894276009419 18086137850299341414014129)
                  ·
                    refine ⟨13564603387724506060510597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18086137850299341414014129 13564603387724506060510597)
                    ·
                      refine ⟨2543363135198344886345737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13564603387724506060510597 2543363135198344886345737)
                      ·
                        rfl

theorem cell23_4953182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 2, 1, 2, 1, 2, 4].length) (baseStart_4953182 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4953182 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4953182 prefixEnd_4953182 := by exact prefixLift 4953182
  have htrace : WordTrace (prefixWord ++ tailWord_4953182) baseStart_4953182 baseEnd_4953182 := by
    simpa [prefixWord, tailWord_4953182, baseEnd_4953182] using wordTrace_append hprefix tailTrace_4953182
  have hstable : (prefixWord ++ tailWord_4953182).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4953182).length < 2 ^ (prefixWord ++ tailWord_4953182).sum := by decide
  have hdescent : baseEnd_4953182 < baseStart_4953182 := by decide
  rcases family_descends (prefixWord ++ tailWord_4953182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4953225 : List Nat := [1, 2, 1, 1, 4, 4, 2, 1, 1, 4, 2]
def baseStart_4953225 : Nat := 118140960795 + 4953225 * 2 ^ 59
def prefixEnd_4953225 : Nat := 4983230072969 + 3 ^ 40 * 4953225 * 2
def baseEnd_4953225 : Nat := 2543385214866488218108039

theorem tailTrace_4953225 : CollatzResearch.WordTrace tailWord_4953225 prefixEnd_4953225 2543385214866488218108039 := by
  unfold tailWord_4953225
  simp only [CollatzResearch.WordTrace]
  refine ⟨180658957480319243326109129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120439304986879495550739419 180658957480319243326109129)
  ·
    refine ⟨135494218110239432494581847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 180658957480319243326109129 135494218110239432494581847)
    ·
      refine ⟨203241327165359148741872771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 135494218110239432494581847 203241327165359148741872771)
      ·
        refine ⟨304861990748038723112809157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 203241327165359148741872771 304861990748038723112809157)
        ·
          refine ⟨57161623265257260583651717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 304861990748038723112809157 57161623265257260583651717)
          ·
            refine ⟨10717804362235736359434697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 57161623265257260583651717 10717804362235736359434697)
            ·
              refine ⟨8038353271676802269576023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10717804362235736359434697 8038353271676802269576023)
              ·
                refine ⟨12057529907515203404364035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8038353271676802269576023 12057529907515203404364035)
                ·
                  refine ⟨18086294861272805106546053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12057529907515203404364035 18086294861272805106546053)
                  ·
                    refine ⟨3391180286488650957477385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18086294861272805106546053 3391180286488650957477385)
                    ·
                      refine ⟨2543385214866488218108039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3391180286488650957477385 2543385214866488218108039)
                      ·
                        rfl

theorem cell23_4953225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 4, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 4, 2, 1, 1, 4, 2].length) (baseStart_4953225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4953225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4953225 prefixEnd_4953225 := by exact prefixLift 4953225
  have htrace : WordTrace (prefixWord ++ tailWord_4953225) baseStart_4953225 baseEnd_4953225 := by
    simpa [prefixWord, tailWord_4953225, baseEnd_4953225] using wordTrace_append hprefix tailTrace_4953225
  have hstable : (prefixWord ++ tailWord_4953225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4953225).length < 2 ^ (prefixWord ++ tailWord_4953225).sum := by decide
  have hdescent : baseEnd_4953225 < baseStart_4953225 := by decide
  rcases family_descends (prefixWord ++ tailWord_4953225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4953246 : List Nat := [4, 3, 1, 1, 2, 3, 2, 1, 1, 3, 2]
def baseStart_4953246 : Nat := 118140960795 + 4953246 * 2 ^ 59
def prefixEnd_4953246 : Nat := 4983230072969 + 3 ^ 40 * 4953246 * 2
def baseEnd_4953246 : Nat := 2543395997960232635945443

theorem tailTrace_4953246 : CollatzResearch.WordTrace tailWord_4953246 prefixEnd_4953246 2543395997960232635945443 := by
  unfold tailWord_4953246
  simp only [CollatzResearch.WordTrace]
  refine ⟨22582465426655395489077949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 120439815608828775941749061 22582465426655395489077949)
  ·
    refine ⟨8468424534995773308404231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22582465426655395489077949 8468424534995773308404231)
    ·
      refine ⟨12702636802493659962606347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8468424534995773308404231 12702636802493659962606347)
      ·
        refine ⟨19053955203740489943909521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12702636802493659962606347 19053955203740489943909521)
        ·
          refine ⟨14290466402805367457932141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19053955203740489943909521 14290466402805367457932141)
          ·
            refine ⟨5358924901052012796724553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14290466402805367457932141 5358924901052012796724553)
            ·
              refine ⟨4019193675789009597543415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5358924901052012796724553 4019193675789009597543415)
              ·
                refine ⟨6028790513683514396315123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4019193675789009597543415 6028790513683514396315123)
                ·
                  refine ⟨9043185770525271594472685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6028790513683514396315123 9043185770525271594472685)
                  ·
                    refine ⟨3391194663946976847927257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9043185770525271594472685 3391194663946976847927257)
                    ·
                      refine ⟨2543395997960232635945443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3391194663946976847927257 2543395997960232635945443)
                      ·
                        rfl

theorem cell23_4953246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 3, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 3, 2, 1, 1, 3, 2].length) (baseStart_4953246 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4953246 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4953246 prefixEnd_4953246 := by exact prefixLift 4953246
  have htrace : WordTrace (prefixWord ++ tailWord_4953246) baseStart_4953246 baseEnd_4953246 := by
    simpa [prefixWord, tailWord_4953246, baseEnd_4953246] using wordTrace_append hprefix tailTrace_4953246
  have hstable : (prefixWord ++ tailWord_4953246).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4953246).length < 2 ^ (prefixWord ++ tailWord_4953246).sum := by decide
  have hdescent : baseEnd_4953246 < baseStart_4953246 := by decide
  rcases family_descends (prefixWord ++ tailWord_4953246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4953265 : List Nat := [1, 2, 2, 5, 1, 1, 2, 4, 5]
def baseStart_4953265 : Nat := 118140960795 + 4953265 * 2 ^ 59
def prefixEnd_4953265 : Nat := 4983230072969 + 3 ^ 40 * 4953265 * 2
def baseEnd_4953265 : Nat := 282600639343629784623095

theorem tailTrace_4953265 : CollatzResearch.WordTrace tailWord_4953265 prefixEnd_4953265 282600639343629784623095 := by
  unfold tailWord_4953265
  simp only [CollatzResearch.WordTrace]
  refine ⟨180660416400174330157565249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120440277600116220105043499 180660416400174330157565249)
  ·
    refine ⟨135495312300130747618173937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 180660416400174330157565249 135495312300130747618173937)
    ·
      refine ⟨101621484225098060713630453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 135495312300130747618173937 101621484225098060713630453)
      ·
        refine ⟨9527014146102943191902855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 101621484225098060713630453 9527014146102943191902855)
        ·
          refine ⟨14290521219154414787854283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9527014146102943191902855 14290521219154414787854283)
          ·
            refine ⟨21435781828731622181781425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14290521219154414787854283 21435781828731622181781425)
            ·
              refine ⟨16076836371548716636336069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21435781828731622181781425 16076836371548716636336069)
              ·
                refine ⟨3014406819665384369313013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16076836371548716636336069 3014406819665384369313013)
                ·
                  refine ⟨282600639343629784623095, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3014406819665384369313013 282600639343629784623095)
                  ·
                    rfl

theorem cell23_4953265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 2, 4, 5].length) (baseStart_4953265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4953265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4953265 prefixEnd_4953265 := by exact prefixLift 4953265
  have htrace : WordTrace (prefixWord ++ tailWord_4953265) baseStart_4953265 baseEnd_4953265 := by
    simpa [prefixWord, tailWord_4953265, baseEnd_4953265] using wordTrace_append hprefix tailTrace_4953265
  have hstable : (prefixWord ++ tailWord_4953265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4953265).length < 2 ^ (prefixWord ++ tailWord_4953265).sum := by decide
  have hdescent : baseEnd_4953265 < baseStart_4953265 := by decide
  rcases family_descends (prefixWord ++ tailWord_4953265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4953271 : List Nat := [1, 1, 3, 1, 4, 1, 2, 1, 1, 1, 7]
def baseStart_4953271 : Nat := 118140960795 + 4953271 * 2 ^ 59
def prefixEnd_4953271 : Nat := 4983230072969 + 3 ^ 40 * 4953271 * 2
def baseEnd_4953271 : Nat := 2543408834976595038132827

theorem tailTrace_4953271 : CollatzResearch.WordTrace tailWord_4953271 prefixEnd_4953271 2543408834976595038132827 := by
  unfold tailWord_4953271
  simp only [CollatzResearch.WordTrace]
  refine ⟨180660635238152593182283667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120440423492101728788189111 180660635238152593182283667)
  ·
    refine ⟨270990952857228889773425501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 180660635238152593182283667 270990952857228889773425501)
    ·
      refine ⟨101621607321460833665034563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 270990952857228889773425501 101621607321460833665034563)
      ·
        refine ⟨152432410982191250497551845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101621607321460833665034563 152432410982191250497551845)
        ·
          refine ⟨28581077059160859468290971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 152432410982191250497551845 28581077059160859468290971)
          ·
            refine ⟨42871615588741289202436457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28581077059160859468290971 42871615588741289202436457)
            ·
              refine ⟨32153711691555966901827343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42871615588741289202436457 32153711691555966901827343)
              ·
                refine ⟨48230567537333950352741015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32153711691555966901827343 48230567537333950352741015)
                ·
                  refine ⟨72345851306000925529111523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 48230567537333950352741015 72345851306000925529111523)
                  ·
                    refine ⟨108518776959001388293667285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 72345851306000925529111523 108518776959001388293667285)
                    ·
                      refine ⟨2543408834976595038132827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 108518776959001388293667285 2543408834976595038132827)
                      ·
                        rfl

theorem cell23_4953271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 2, 1, 1, 1, 7].length) (baseStart_4953271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4953271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4953271 prefixEnd_4953271 := by exact prefixLift 4953271
  have htrace : WordTrace (prefixWord ++ tailWord_4953271) baseStart_4953271 baseEnd_4953271 := by
    simpa [prefixWord, tailWord_4953271, baseEnd_4953271] using wordTrace_append hprefix tailTrace_4953271
  have hstable : (prefixWord ++ tailWord_4953271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4953271).length < 2 ^ (prefixWord ++ tailWord_4953271).sum := by decide
  have hdescent : baseEnd_4953271 < baseStart_4953271 := by decide
  rcases family_descends (prefixWord ++ tailWord_4953271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4953278 : List Nat := [4, 2, 1, 1, 3, 1, 1, 2, 1, 7]
def baseStart_4953278 : Nat := 118140960795 + 4953278 * 2 ^ 59
def prefixEnd_4953278 : Nat := 4983230072969 + 3 ^ 40 * 4953278 * 2
def baseEnd_4953278 : Nat := 847804143113725503581765

theorem tailTrace_4953278 : CollatzResearch.WordTrace tailWord_4953278 prefixEnd_4953278 847804143113725503581765 := by
  unfold tailWord_4953278
  simp only [CollatzResearch.WordTrace]
  refine ⟨22582611318640904172223561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 120440593699418155585192325 22582611318640904172223561)
  ·
    refine ⟨16936958488980678129167671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22582611318640904172223561 16936958488980678129167671)
    ·
      refine ⟨25405437733471017193751507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16936958488980678129167671 25405437733471017193751507)
      ·
        refine ⟨38108156600206525790627261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25405437733471017193751507 38108156600206525790627261)
        ·
          refine ⟨14290558725077447171485223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38108156600206525790627261 14290558725077447171485223)
          ·
            refine ⟨21435838087616170757227835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14290558725077447171485223 21435838087616170757227835)
            ·
              refine ⟨32153757131424256135841753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21435838087616170757227835 32153757131424256135841753)
              ·
                refine ⟨24115317848568192101881315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32153757131424256135841753 24115317848568192101881315)
                ·
                  refine ⟨36172976772852288152821973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24115317848568192101881315 36172976772852288152821973)
                  ·
                    refine ⟨847804143113725503581765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 36172976772852288152821973 847804143113725503581765)
                    ·
                      rfl

theorem cell23_4953278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 1, 2, 1, 7].length) (baseStart_4953278 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4953278 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4953278 prefixEnd_4953278 := by exact prefixLift 4953278
  have htrace : WordTrace (prefixWord ++ tailWord_4953278) baseStart_4953278 baseEnd_4953278 := by
    simpa [prefixWord, tailWord_4953278, baseEnd_4953278] using wordTrace_append hprefix tailTrace_4953278
  have hstable : (prefixWord ++ tailWord_4953278).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4953278).length < 2 ^ (prefixWord ++ tailWord_4953278).sum := by decide
  have hdescent : baseEnd_4953278 < baseStart_4953278 := by decide
  rcases family_descends (prefixWord ++ tailWord_4953278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4953298 : List Nat := [3, 2, 2, 2, 1, 1, 1, 3, 1, 3, 4]
def baseStart_4953298 : Nat := 118140960795 + 4953298 * 2 ^ 59
def prefixEnd_4953298 : Nat := 4983230072969 + 3 ^ 40 * 4953298 * 2
def baseEnd_4953298 : Nat := 2543422698954266432495203

theorem tailTrace_4953298 : CollatzResearch.WordTrace tailWord_4953298 prefixEnd_4953298 2543422698954266432495203 := by
  unfold tailWord_4953298
  simp only [CollatzResearch.WordTrace]
  refine ⟨45165405002263694198379137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 120441080006036517862344365 45165405002263694198379137)
  ·
    refine ⟨33874053751697770648784353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45165405002263694198379137 33874053751697770648784353)
    ·
      refine ⟨25405540313773327986588265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33874053751697770648784353 25405540313773327986588265)
      ·
        refine ⟨19054155235329995989941199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25405540313773327986588265 19054155235329995989941199)
        ·
          refine ⟨28581232852994993984911799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19054155235329995989941199 28581232852994993984911799)
          ·
            refine ⟨42871849279492490977367699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28581232852994993984911799 42871849279492490977367699)
            ·
              refine ⟨64307773919238736466051549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42871849279492490977367699 64307773919238736466051549)
              ·
                refine ⟨24115415219714526174769331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 64307773919238736466051549 24115415219714526174769331)
                ·
                  refine ⟨36173122829571789262153997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24115415219714526174769331 36173122829571789262153997)
                  ·
                    refine ⟨13564921061089420973307749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 36173122829571789262153997 13564921061089420973307749)
                    ·
                      refine ⟨2543422698954266432495203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13564921061089420973307749 2543422698954266432495203)
                      ·
                        rfl

theorem cell23_4953298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 1, 3, 1, 3, 4].length) (baseStart_4953298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4953298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4953298 prefixEnd_4953298 := by exact prefixLift 4953298
  have htrace : WordTrace (prefixWord ++ tailWord_4953298) baseStart_4953298 baseEnd_4953298 := by
    simpa [prefixWord, tailWord_4953298, baseEnd_4953298] using wordTrace_append hprefix tailTrace_4953298
  have hstable : (prefixWord ++ tailWord_4953298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4953298).length < 2 ^ (prefixWord ++ tailWord_4953298).sum := by decide
  have hdescent : baseEnd_4953298 < baseStart_4953298 := by decide
  rcases family_descends (prefixWord ++ tailWord_4953298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4953311 : List Nat := [1, 1, 2, 3, 2, 1, 2, 1, 1, 3, 6]
def baseStart_4953311 : Nat := 118140960795 + 4953311 * 2 ^ 59
def prefixEnd_4953311 : Nat := 4983230072969 + 3 ^ 40 * 4953311 * 2
def baseEnd_4953311 : Nat := 2543429374202774881632643

theorem tailTrace_4953311 : CollatzResearch.WordTrace tailWord_4953311 prefixEnd_4953311 2543429374202774881632643 := by
  unfold tailWord_4953311
  simp only [CollatzResearch.WordTrace]
  refine ⟨180662094158007680013739787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120441396105338453342493191 180662094158007680013739787)
  ·
    refine ⟨270993141237011520020609681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 180662094158007680013739787 270993141237011520020609681)
    ·
      refine ⟨203244855927758640015457261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 270993141237011520020609681 203244855927758640015457261)
      ·
        refine ⟨76216820972909490005796473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 203244855927758640015457261 76216820972909490005796473)
        ·
          refine ⟨57162615729682117504347355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 76216820972909490005796473 57162615729682117504347355)
          ·
            refine ⟨85743923594523176256521033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57162615729682117504347355 85743923594523176256521033)
            ·
              refine ⟨64307942695892382192390775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 85743923594523176256521033 64307942695892382192390775)
              ·
                refine ⟨96461914043838573288586163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 64307942695892382192390775 96461914043838573288586163)
                ·
                  refine ⟨144692871065757859932879245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 96461914043838573288586163 144692871065757859932879245)
                  ·
                    refine ⟨54259826649659197474829717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 144692871065757859932879245 54259826649659197474829717)
                    ·
                      refine ⟨2543429374202774881632643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 54259826649659197474829717 2543429374202774881632643)
                      ·
                        rfl

theorem cell23_4953311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 2, 1, 1, 3, 6].length) (baseStart_4953311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4953311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4953311 prefixEnd_4953311 := by exact prefixLift 4953311
  have htrace : WordTrace (prefixWord ++ tailWord_4953311) baseStart_4953311 baseEnd_4953311 := by
    simpa [prefixWord, tailWord_4953311, baseEnd_4953311] using wordTrace_append hprefix tailTrace_4953311
  have hstable : (prefixWord ++ tailWord_4953311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4953311).length < 2 ^ (prefixWord ++ tailWord_4953311).sum := by decide
  have hdescent : baseEnd_4953311 < baseStart_4953311 := by decide
  rcases family_descends (prefixWord ++ tailWord_4953311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4953338 : List Nat := [3, 1, 1, 1, 1, 4, 3, 3, 6]
def baseStart_4953338 : Nat := 118140960795 + 4953338 * 2 ^ 59
def prefixEnd_4953338 : Nat := 4983230072969 + 3 ^ 40 * 4953338 * 2
def baseEnd_4953338 : Nat := 282604804242271808443891

theorem tailTrace_4953338 : CollatzResearch.WordTrace tailWord_4953338 prefixEnd_4953338 282604804242271808443891 := by
  unfold tailWord_4953338
  simp only [CollatzResearch.WordTrace]
  refine ⟨45165769732227465906243167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 120442052619273242416648445 45165769732227465906243167)
  ·
    refine ⟨67748654598341198859364751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45165769732227465906243167 67748654598341198859364751)
    ·
      refine ⟨101622981897511798289047127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67748654598341198859364751 101622981897511798289047127)
      ·
        refine ⟨152434472846267697433570691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101622981897511798289047127 152434472846267697433570691)
        ·
          refine ⟨228651709269401546150356037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 152434472846267697433570691 228651709269401546150356037)
          ·
            refine ⟨42872195488012789903191757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 228651709269401546150356037 42872195488012789903191757)
            ·
              refine ⟨16077073308004796213696909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 42872195488012789903191757 16077073308004796213696909)
              ·
                refine ⟨6028902490501798580136341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16077073308004796213696909 6028902490501798580136341)
                ·
                  refine ⟨282604804242271808443891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6028902490501798580136341 282604804242271808443891)
                  ·
                    rfl

theorem cell23_4953338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 3, 3, 6].length) (baseStart_4953338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4953338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4953338 prefixEnd_4953338 := by exact prefixLift 4953338
  have htrace : WordTrace (prefixWord ++ tailWord_4953338) baseStart_4953338 baseEnd_4953338 := by
    simpa [prefixWord, tailWord_4953338, baseEnd_4953338] using wordTrace_append hprefix tailTrace_4953338
  have hstable : (prefixWord ++ tailWord_4953338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4953338).length < 2 ^ (prefixWord ++ tailWord_4953338).sum := by decide
  have hdescent : baseEnd_4953338 < baseStart_4953338 := by decide
  rcases family_descends (prefixWord ++ tailWord_4953338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4953352 : List Nat := [2, 1, 3, 2, 4, 1, 2, 1, 2, 2, 3]
def baseStart_4953352 : Nat := 118140960795 + 4953352 * 2 ^ 59
def prefixEnd_4953352 : Nat := 4983230072969 + 3 ^ 40 * 4953352 * 2
def baseEnd_4953352 : Nat := 2543450426909609221219955

theorem tailTrace_4953352 : CollatzResearch.WordTrace tailWord_4953352 prefixEnd_4953352 2543450426909609221219955 := by
  unfold tailWord_4953352
  simp only [CollatzResearch.WordTrace]
  refine ⟨90331794775429572007991155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120442393033906096010654873 90331794775429572007991155)
  ·
    refine ⟨135497692163144358011986733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90331794775429572007991155 135497692163144358011986733)
    ·
      refine ⟨50811634561179134254495025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 135497692163144358011986733 50811634561179134254495025)
      ·
        refine ⟨38108725920884350690871269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50811634561179134254495025 38108725920884350690871269)
        ·
          refine ⟨7145386110165815754538363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 38108725920884350690871269 7145386110165815754538363)
          ·
            refine ⟨10718079165248723631807545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7145386110165815754538363 10718079165248723631807545)
            ·
              refine ⟨8038559373936542723855659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10718079165248723631807545 8038559373936542723855659)
              ·
                refine ⟨12057839060904814085783489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8038559373936542723855659 12057839060904814085783489)
                ·
                  refine ⟨9043379295678610564337617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12057839060904814085783489 9043379295678610564337617)
                  ·
                    refine ⟨6782534471758957923253213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9043379295678610564337617 6782534471758957923253213)
                    ·
                      refine ⟨2543450426909609221219955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6782534471758957923253213 2543450426909609221219955)
                      ·
                        rfl

theorem cell23_4953352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 1, 2, 1, 2, 2, 3].length) (baseStart_4953352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4953352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4953352 prefixEnd_4953352 := by exact prefixLift 4953352
  have htrace : WordTrace (prefixWord ++ tailWord_4953352) baseStart_4953352 baseEnd_4953352 := by
    simpa [prefixWord, tailWord_4953352, baseEnd_4953352] using wordTrace_append hprefix tailTrace_4953352
  have hstable : (prefixWord ++ tailWord_4953352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4953352).length < 2 ^ (prefixWord ++ tailWord_4953352).sum := by decide
  have hdescent : baseEnd_4953352 < baseStart_4953352 := by decide
  rcases family_descends (prefixWord ++ tailWord_4953352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4953376 : List Nat := [2, 1, 1, 5, 3, 2, 2, 2, 1, 4]
def baseStart_4953376 : Nat := 118140960795 + 4953376 * 2 ^ 59
def prefixEnd_4953376 : Nat := 4983230072969 + 3 ^ 40 * 4953376 * 2
def baseEnd_4953376 : Nat := 847820916815105709106615

theorem tailTrace_4953376 : CollatzResearch.WordTrace tailWord_4953376 prefixEnd_4953376 847820916815105709106615 := by
  unfold tailWord_4953376
  simp only [CollatzResearch.WordTrace]
  refine ⟨90332232451386098057427991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120442976601848130743237321 90332232451386098057427991)
  ·
    refine ⟨135498348677079147086141987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90332232451386098057427991 135498348677079147086141987)
    ·
      refine ⟨203247523015618720629212981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 135498348677079147086141987 203247523015618720629212981)
      ·
        refine ⟨19054455282714255058988717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 203247523015618720629212981 19054455282714255058988717)
        ·
          refine ⟨7145420731017845647120769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19054455282714255058988717 7145420731017845647120769)
          ·
            refine ⟨5359065548263384235340577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7145420731017845647120769 5359065548263384235340577)
            ·
              refine ⟨4019299161197538176505433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5359065548263384235340577 4019299161197538176505433)
              ·
                refine ⟨3014474370898153632379075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4019299161197538176505433 3014474370898153632379075)
                ·
                  refine ⟨4521711556347230448568613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3014474370898153632379075 4521711556347230448568613)
                  ·
                    refine ⟨847820916815105709106615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4521711556347230448568613 847820916815105709106615)
                    ·
                      rfl

theorem cell23_4953376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 2, 2, 2, 1, 4].length) (baseStart_4953376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4953376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4953376 prefixEnd_4953376 := by exact prefixLift 4953376
  have htrace : WordTrace (prefixWord ++ tailWord_4953376) baseStart_4953376 baseEnd_4953376 := by
    simpa [prefixWord, tailWord_4953376, baseEnd_4953376] using wordTrace_append hprefix tailTrace_4953376
  have hstable : (prefixWord ++ tailWord_4953376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4953376).length < 2 ^ (prefixWord ++ tailWord_4953376).sum := by decide
  have hdescent : baseEnd_4953376 < baseStart_4953376 := by decide
  rcases family_descends (prefixWord ++ tailWord_4953376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
