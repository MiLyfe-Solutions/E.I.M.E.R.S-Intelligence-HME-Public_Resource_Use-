import V185TrunkScan22Chunk055

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_502870 : List Nat := [5, 2, 2, 1, 3, 1, 1, 1, 6]
def baseStart_502870 : Nat := 118140960795 + 502870 * 2 ^ 59
def prefixEnd_502870 : Nat := 4983230072969 + 3 ^ 40 * 502870 * 2
def baseEnd_502870 : Nat := 57380892605900611669411

theorem tailTrace_502870 : CollatzResearch.WordTrace tailWord_502870 prefixEnd_502870 57380892605900611669411 := by
  unfold tailWord_502870
  simp only [CollatzResearch.WordTrace]
  refine ⟨1146323480512209262724129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 12227450458796898802390709 1146323480512209262724129)
  ·
    refine ⟨859742610384156947043097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1146323480512209262724129 859742610384156947043097)
    ·
      refine ⟨644806957788117710282323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 859742610384156947043097 644806957788117710282323)
      ·
        refine ⟨967210436682176565423485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 644806957788117710282323 967210436682176565423485)
        ·
          refine ⟨362703913755816212033807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 967210436682176565423485 362703913755816212033807)
          ·
            refine ⟨544055870633724318050711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 362703913755816212033807 544055870633724318050711)
            ·
              refine ⟨816083805950586477076067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 544055870633724318050711 816083805950586477076067)
              ·
                refine ⟨1224125708925879715614101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 816083805950586477076067 1224125708925879715614101)
                ·
                  refine ⟨57380892605900611669411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1224125708925879715614101 57380892605900611669411)
                  ·
                    rfl

theorem cell22_502870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 3, 1, 1, 1, 6].length) (baseStart_502870 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_502870 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_502870 prefixEnd_502870 := by exact prefixLift 502870
  have htrace : WordTrace (prefixWord ++ tailWord_502870) baseStart_502870 baseEnd_502870 := by
    simpa [prefixWord, tailWord_502870, baseEnd_502870] using wordTrace_append hprefix tailTrace_502870
  have hstable : (prefixWord ++ tailWord_502870).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_502870).length < 2 ^ (prefixWord ++ tailWord_502870).sum := by decide
  have hdescent : baseEnd_502870 < baseStart_502870 := by decide
  rcases family_descends (prefixWord ++ tailWord_502870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_502926 : List Nat := [4, 1, 1, 3, 2, 2, 2, 2, 5]
def baseStart_502926 : Nat := 118140960795 + 502926 * 2 ^ 59
def prefixEnd_502926 : Nat := 4983230072969 + 3 ^ 40 * 502926 * 2
def baseEnd_502926 : Nat := 57387282587378785202687

theorem tailTrace_502926 : CollatzResearch.WordTrace tailWord_502926 prefixEnd_502926 57387282587378785202687 := by
  unfold tailWord_502926
  simp only [CollatzResearch.WordTrace]
  refine ⟨2292902271999058720953079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12228812117328313178416421 2292902271999058720953079)
  ·
    refine ⟨3439353407998588081429619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2292902271999058720953079 3439353407998588081429619)
    ·
      refine ⟨5159030111997882122144429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3439353407998588081429619 5159030111997882122144429)
      ·
        refine ⟨1934636291999205795804161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5159030111997882122144429 1934636291999205795804161)
        ·
          refine ⟨1450977218999404346853121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1934636291999205795804161 1450977218999404346853121)
          ·
            refine ⟨1088232914249553260139841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1450977218999404346853121 1088232914249553260139841)
            ·
              refine ⟨816174685687164945104881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1088232914249553260139841 816174685687164945104881)
              ·
                refine ⟨612131014265373708828661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 816174685687164945104881 612131014265373708828661)
                ·
                  refine ⟨57387282587378785202687, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 612131014265373708828661 57387282587378785202687)
                  ·
                    rfl

theorem cell22_502926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 2, 2, 2, 5].length) (baseStart_502926 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_502926 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_502926 prefixEnd_502926 := by exact prefixLift 502926
  have htrace : WordTrace (prefixWord ++ tailWord_502926) baseStart_502926 baseEnd_502926 := by
    simpa [prefixWord, tailWord_502926, baseEnd_502926] using wordTrace_append hprefix tailTrace_502926
  have hstable : (prefixWord ++ tailWord_502926).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_502926).length < 2 ^ (prefixWord ++ tailWord_502926).sum := by decide
  have hdescent : baseEnd_502926 < baseStart_502926 := by decide
  rcases family_descends (prefixWord ++ tailWord_502926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_502930 : List Nat := [3, 2, 3, 1, 1, 2, 4, 2, 1, 3]
def baseStart_502930 : Nat := 118140960795 + 502930 * 2 ^ 59
def prefixEnd_502930 : Nat := 4983230072969 + 3 ^ 40 * 502930 * 2
def baseEnd_502930 : Nat := 172163217043881678508049

theorem tailTrace_502930 : CollatzResearch.WordTrace tailWord_502930 prefixEnd_502930 172163217043881678508049 := by
  unfold tailWord_502930
  simp only [CollatzResearch.WordTrace]
  refine ⟨4585841016994494612692561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12228909378651985633846829 4585841016994494612692561)
  ·
    refine ⟨3439380762745870959519421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4585841016994494612692561 3439380762745870959519421)
    ·
      refine ⟨1289767786029701609819783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3439380762745870959519421 1289767786029701609819783)
      ·
        refine ⟨1934651679044552414729675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1289767786029701609819783 1934651679044552414729675)
        ·
          refine ⟨2901977518566828622094513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1934651679044552414729675 2901977518566828622094513)
          ·
            refine ⟨2176483138925121466570885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2901977518566828622094513 2176483138925121466570885)
            ·
              refine ⟨408090588548460274982041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2176483138925121466570885 408090588548460274982041)
              ·
                refine ⟨306067941411345206236531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 408090588548460274982041 306067941411345206236531)
                ·
                  refine ⟨459101912117017809354797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 306067941411345206236531 459101912117017809354797)
                  ·
                    refine ⟨172163217043881678508049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 459101912117017809354797 172163217043881678508049)
                    ·
                      rfl

theorem cell22_502930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 4, 2, 1, 3].length) (baseStart_502930 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_502930 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_502930 prefixEnd_502930 := by exact prefixLift 502930
  have htrace : WordTrace (prefixWord ++ tailWord_502930) baseStart_502930 baseEnd_502930 := by
    simpa [prefixWord, tailWord_502930, baseEnd_502930] using wordTrace_append hprefix tailTrace_502930
  have hstable : (prefixWord ++ tailWord_502930).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_502930).length < 2 ^ (prefixWord ++ tailWord_502930).sum := by decide
  have hdescent : baseEnd_502930 < baseStart_502930 := by decide
  rcases family_descends (prefixWord ++ tailWord_502930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_502969 : List Nat := [1, 2, 1, 4, 1, 3, 2, 2, 1, 5]
def baseStart_502969 : Nat := 118140960795 + 502969 * 2 ^ 59
def prefixEnd_502969 : Nat := 4983230072969 + 3 ^ 40 * 502969 * 2
def baseEnd_502969 : Nat := 172176567540898576782929

theorem tailTrace_502969 : CollatzResearch.WordTrace tailWord_502969 prefixEnd_502969 172176567540898576782929 := by
  unfold tailWord_502969
  simp only [CollatzResearch.WordTrace]
  refine ⟨18344786514836688111439961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12229857676557792074293307 18344786514836688111439961)
  ·
    refine ⟨13758589886127516083579971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18344786514836688111439961 13758589886127516083579971)
    ·
      refine ⟨20637884829191274125369957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13758589886127516083579971 20637884829191274125369957)
      ·
        refine ⟨3869603405473363898506867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20637884829191274125369957 3869603405473363898506867)
        ·
          refine ⟨5804405108210045847760301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3869603405473363898506867 5804405108210045847760301)
          ·
            refine ⟨2176651915578767192910113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5804405108210045847760301 2176651915578767192910113)
            ·
              refine ⟨1632488936684075394682585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2176651915578767192910113 1632488936684075394682585)
              ·
                refine ⟨1224366702513056546011939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1632488936684075394682585 1224366702513056546011939)
                ·
                  refine ⟨1836550053769584819017909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1224366702513056546011939 1836550053769584819017909)
                  ·
                    refine ⟨172176567540898576782929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1836550053769584819017909 172176567540898576782929)
                    ·
                      rfl

theorem cell22_502969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 2, 2, 1, 5].length) (baseStart_502969 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_502969 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_502969 prefixEnd_502969 := by exact prefixLift 502969
  have htrace : WordTrace (prefixWord ++ tailWord_502969) baseStart_502969 baseEnd_502969 := by
    simpa [prefixWord, tailWord_502969, baseEnd_502969] using wordTrace_append hprefix tailTrace_502969
  have hstable : (prefixWord ++ tailWord_502969).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_502969).length < 2 ^ (prefixWord ++ tailWord_502969).sum := by decide
  have hdescent : baseEnd_502969 < baseStart_502969 := by decide
  rcases family_descends (prefixWord ++ tailWord_502969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_502984 : List Nat := [2, 1, 3, 1, 2, 1, 2, 4, 2, 4]
def baseStart_502984 : Nat := 118140960795 + 502984 * 2 ^ 59
def prefixEnd_502984 : Nat := 4983230072969 + 3 ^ 40 * 502984 * 2
def baseEnd_502984 : Nat := 172181702347443537657883

theorem tailTrace_502984 : CollatzResearch.WordTrace tailWord_502984 prefixEnd_502984 172181702347443537657883 := by
  unfold tailWord_502984
  simp only [CollatzResearch.WordTrace]
  refine ⟨9172666804891172836618003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12230222406521563782157337 9172666804891172836618003)
  ·
    refine ⟨13759000207336759254927005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9172666804891172836618003 13759000207336759254927005)
    ·
      refine ⟨5159625077751284720597627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13759000207336759254927005 5159625077751284720597627)
      ·
        refine ⟨7739437616626927080896441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5159625077751284720597627 7739437616626927080896441)
        ·
          refine ⟨5804578212470195310672331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7739437616626927080896441 5804578212470195310672331)
          ·
            refine ⟨8706867318705292966008497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5804578212470195310672331 8706867318705292966008497)
            ·
              refine ⟨6530150489028969724506373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8706867318705292966008497 6530150489028969724506373)
              ·
                refine ⟨1224403216692931823344945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6530150489028969724506373 1224403216692931823344945)
                ·
                  refine ⟨918302412519698867508709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1224403216692931823344945 918302412519698867508709)
                  ·
                    refine ⟨172181702347443537657883, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 918302412519698867508709 172181702347443537657883)
                    ·
                      rfl

theorem cell22_502984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 2, 4, 2, 4].length) (baseStart_502984 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_502984 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_502984 prefixEnd_502984 := by exact prefixLift 502984
  have htrace : WordTrace (prefixWord ++ tailWord_502984) baseStart_502984 baseEnd_502984 := by
    simpa [prefixWord, tailWord_502984, baseEnd_502984] using wordTrace_append hprefix tailTrace_502984
  have hstable : (prefixWord ++ tailWord_502984).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_502984).length < 2 ^ (prefixWord ++ tailWord_502984).sum := by decide
  have hdescent : baseEnd_502984 < baseStart_502984 := by decide
  rcases family_descends (prefixWord ++ tailWord_502984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_502986 : List Nat := [3, 1, 2, 1, 3, 3, 1, 1, 4, 3]
def baseStart_502986 : Nat := 118140960795 + 502986 * 2 ^ 59
def prefixEnd_502986 : Nat := 4983230072969 + 3 ^ 40 * 502986 * 2
def baseEnd_502986 : Nat := 172182386988316199107877

theorem tailTrace_502986 : CollatzResearch.WordTrace tailWord_502986 prefixEnd_502986 172182386988316199107877 := by
  unfold tailWord_502986
  simp only [CollatzResearch.WordTrace]
  refine ⟨4586351638943775003702203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12230271037183400009872541 4586351638943775003702203)
  ·
    refine ⟨6879527458415662505553305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4586351638943775003702203 6879527458415662505553305)
    ·
      refine ⟨5159645593811746879164979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6879527458415662505553305 5159645593811746879164979)
      ·
        refine ⟨7739468390717620318747469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5159645593811746879164979 7739468390717620318747469)
        ·
          refine ⟨2902300646519107619530301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7739468390717620318747469 2902300646519107619530301)
          ·
            refine ⟨1088362742444665357323863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2902300646519107619530301 1088362742444665357323863)
            ·
              refine ⟨1632544113666998035985795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1088362742444665357323863 1632544113666998035985795)
              ·
                refine ⟨2448816170500497053978693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1632544113666998035985795 2448816170500497053978693)
                ·
                  refine ⟨459153031968843197621005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2448816170500497053978693 459153031968843197621005)
                  ·
                    refine ⟨172182386988316199107877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 459153031968843197621005 172182386988316199107877)
                    ·
                      rfl

theorem cell22_502986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 3, 1, 1, 4, 3].length) (baseStart_502986 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_502986 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_502986 prefixEnd_502986 := by exact prefixLift 502986
  have htrace : WordTrace (prefixWord ++ tailWord_502986) baseStart_502986 baseEnd_502986 := by
    simpa [prefixWord, tailWord_502986, baseEnd_502986] using wordTrace_append hprefix tailTrace_502986
  have hstable : (prefixWord ++ tailWord_502986).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_502986).length < 2 ^ (prefixWord ++ tailWord_502986).sum := by decide
  have hdescent : baseEnd_502986 < baseStart_502986 := by decide
  rcases family_descends (prefixWord ++ tailWord_502986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_503104 : List Nat := [2, 1, 1, 2, 2, 1, 3, 2, 3, 5]
def baseStart_503104 : Nat := 118140960795 + 503104 * 2 ^ 59
def prefixEnd_503104 : Nat := 4983230072969 + 3 ^ 40 * 503104 * 2
def baseEnd_503104 : Nat := 172222780799803224657515

theorem tailTrace_503104 : CollatzResearch.WordTrace tailWord_503104 prefixEnd_503104 172222780799803224657515 := by
  unfold tailWord_503104
  simp only [CollatzResearch.WordTrace]
  refine ⟨9174855184673803083802183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12233140246231737445069577 9174855184673803083802183)
  ·
    refine ⟨13762282777010704625703275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9174855184673803083802183 13762282777010704625703275)
    ·
      refine ⟨20643424165516056938554913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13762282777010704625703275 20643424165516056938554913)
      ·
        refine ⟨15482568124137042703916185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20643424165516056938554913 15482568124137042703916185)
        ·
          refine ⟨11611926093102782027937139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15482568124137042703916185 11611926093102782027937139)
          ·
            refine ⟨17417889139654173041905709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11611926093102782027937139 17417889139654173041905709)
            ·
              refine ⟨6531708427370314890714641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17417889139654173041905709 6531708427370314890714641)
              ·
                refine ⟨4898781320527736168035981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6531708427370314890714641 4898781320527736168035981)
                ·
                  refine ⟨1837042995197901063013493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4898781320527736168035981 1837042995197901063013493)
                  ·
                    refine ⟨172222780799803224657515, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1837042995197901063013493 172222780799803224657515)
                    ·
                      rfl

theorem cell22_503104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 3, 2, 3, 5].length) (baseStart_503104 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_503104 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_503104 prefixEnd_503104 := by exact prefixLift 503104
  have htrace : WordTrace (prefixWord ++ tailWord_503104) baseStart_503104 baseEnd_503104 := by
    simpa [prefixWord, tailWord_503104, baseEnd_503104] using wordTrace_append hprefix tailTrace_503104
  have hstable : (prefixWord ++ tailWord_503104).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_503104).length < 2 ^ (prefixWord ++ tailWord_503104).sum := by decide
  have hdescent : baseEnd_503104 < baseStart_503104 := by decide
  rcases family_descends (prefixWord ++ tailWord_503104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_503108 : List Nat := [2, 3, 4, 1, 1, 1, 1, 2, 3, 4]
def baseStart_503108 : Nat := 118140960795 + 503108 * 2 ^ 59
def prefixEnd_503108 : Nat := 4983230072969 + 3 ^ 40 * 503108 * 2
def baseEnd_503108 : Nat := 172224150081548547557503

theorem tailTrace_503108 : CollatzResearch.WordTrace tailWord_503108 prefixEnd_503108 172224150081548547557503 := by
  unfold tailWord_503108
  simp only [CollatzResearch.WordTrace]
  refine ⟨9174928130666557425374989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12233237507555409900499985 9174928130666557425374989)
  ·
    refine ⟨3440598048999959034515621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9174928130666557425374989 3440598048999959034515621)
    ·
      refine ⟨645112134187492318971679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3440598048999959034515621 645112134187492318971679)
      ·
        refine ⟨967668201281238478457519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 645112134187492318971679 967668201281238478457519)
        ·
          refine ⟨1451502301921857717686279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 967668201281238478457519 1451502301921857717686279)
          ·
            refine ⟨2177253452882786576529419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1451502301921857717686279 2177253452882786576529419)
            ·
              refine ⟨3265880179324179864794129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2177253452882786576529419 3265880179324179864794129)
              ·
                refine ⟨2449410134493134898595597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3265880179324179864794129 2449410134493134898595597)
                ·
                  refine ⟨918528800434925586973349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2449410134493134898595597 918528800434925586973349)
                  ·
                    refine ⟨172224150081548547557503, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 918528800434925586973349 172224150081548547557503)
                    ·
                      rfl

theorem cell22_503108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 1, 2, 3, 4].length) (baseStart_503108 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_503108 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_503108 prefixEnd_503108 := by exact prefixLift 503108
  have htrace : WordTrace (prefixWord ++ tailWord_503108) baseStart_503108 baseEnd_503108 := by
    simpa [prefixWord, tailWord_503108, baseEnd_503108] using wordTrace_append hprefix tailTrace_503108
  have hstable : (prefixWord ++ tailWord_503108).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_503108).length < 2 ^ (prefixWord ++ tailWord_503108).sum := by decide
  have hdescent : baseEnd_503108 < baseStart_503108 := by decide
  rcases family_descends (prefixWord ++ tailWord_503108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_503121 : List Nat := [1, 2, 2, 1, 4, 1, 4, 1, 1, 5]
def baseStart_503121 : Nat := 118140960795 + 503121 * 2 ^ 59
def prefixEnd_503121 : Nat := 4983230072969 + 3 ^ 40 * 503121 * 2
def baseEnd_503121 : Nat := 172228600247220846982463

theorem tailTrace_503121 : CollatzResearch.WordTrace tailWord_503121 prefixEnd_503121 172228600247220846982463 := by
  unfold tailWord_503121
  simp only [CollatzResearch.WordTrace]
  refine ⟨18350330410286018070973217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12233553606857345380648811 18350330410286018070973217)
  ·
    refine ⟨13762747807714513553229913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18350330410286018070973217 13762747807714513553229913)
    ·
      refine ⟨10322060855785885164922435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13762747807714513553229913 10322060855785885164922435)
      ·
        refine ⟨15483091283678827747383653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10322060855785885164922435 15483091283678827747383653)
        ·
          refine ⟨2903079615689780202634435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15483091283678827747383653 2903079615689780202634435)
          ·
            refine ⟨4354619423534670303951653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2903079615689780202634435 4354619423534670303951653)
            ·
              refine ⟨816491141912750681990935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4354619423534670303951653 816491141912750681990935)
              ·
                refine ⟨1224736712869126022986403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 816491141912750681990935 1224736712869126022986403)
                ·
                  refine ⟨1837105069303689034479605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1224736712869126022986403 1837105069303689034479605)
                  ·
                    refine ⟨172228600247220846982463, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1837105069303689034479605 172228600247220846982463)
                    ·
                      rfl

theorem cell22_503121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 4, 1, 1, 5].length) (baseStart_503121 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_503121 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_503121 prefixEnd_503121 := by exact prefixLift 503121
  have htrace : WordTrace (prefixWord ++ tailWord_503121) baseStart_503121 baseEnd_503121 := by
    simpa [prefixWord, tailWord_503121, baseEnd_503121] using wordTrace_append hprefix tailTrace_503121
  have hstable : (prefixWord ++ tailWord_503121).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_503121).length < 2 ^ (prefixWord ++ tailWord_503121).sum := by decide
  have hdescent : baseEnd_503121 < baseStart_503121 := by decide
  rcases family_descends (prefixWord ++ tailWord_503121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_503136 : List Nat := [2, 1, 1, 3, 4, 2, 1, 1, 1, 6]
def baseStart_503136 : Nat := 118140960795 + 503136 * 2 ^ 59
def prefixEnd_503136 : Nat := 4983230072969 + 3 ^ 40 * 503136 * 2
def baseEnd_503136 : Nat := 172233735053765807857417

theorem tailTrace_503136 : CollatzResearch.WordTrace tailWord_503136 prefixEnd_503136 172233735053765807857417 := by
  unfold tailWord_503136
  simp only [CollatzResearch.WordTrace]
  refine ⟨9175438752615837816384631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12233918336821117088512841 9175438752615837816384631)
  ·
    refine ⟨13763158128923756724576947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9175438752615837816384631 13763158128923756724576947)
    ·
      refine ⟨20644737193385635086865421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13763158128923756724576947 20644737193385635086865421)
      ·
        refine ⟨7741776447519613157574533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20644737193385635086865421 7741776447519613157574533)
        ·
          refine ⟨1451583083909927467045225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7741776447519613157574533 1451583083909927467045225)
          ·
            refine ⟨1088687312932445600283919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1451583083909927467045225 1088687312932445600283919)
            ·
              refine ⟨1633030969398668400425879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1088687312932445600283919 1633030969398668400425879)
              ·
                refine ⟨2449546454098002600638819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1633030969398668400425879 2449546454098002600638819)
                ·
                  refine ⟨3674319681147003900958229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2449546454098002600638819 3674319681147003900958229)
                  ·
                    refine ⟨172233735053765807857417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3674319681147003900958229 172233735053765807857417)
                    ·
                      rfl

theorem cell22_503136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 2, 1, 1, 1, 6].length) (baseStart_503136 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_503136 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_503136 prefixEnd_503136 := by exact prefixLift 503136
  have htrace : WordTrace (prefixWord ++ tailWord_503136) baseStart_503136 baseEnd_503136 := by
    simpa [prefixWord, tailWord_503136, baseEnd_503136] using wordTrace_append hprefix tailTrace_503136
  have hstable : (prefixWord ++ tailWord_503136).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_503136).length < 2 ^ (prefixWord ++ tailWord_503136).sum := by decide
  have hdescent : baseEnd_503136 < baseStart_503136 := by decide
  rcases family_descends (prefixWord ++ tailWord_503136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_503138 : List Nat := [3, 3, 2, 1, 1, 1, 2, 2, 4, 3]
def baseStart_503138 : Nat := 118140960795 + 503138 * 2 ^ 59
def prefixEnd_503138 : Nat := 4983230072969 + 3 ^ 40 * 503138 * 2
def baseEnd_503138 : Nat := 172234419694638469307411

theorem tailTrace_503138 : CollatzResearch.WordTrace tailWord_503138 prefixEnd_503138 172234419694638469307411 := by
  unfold tailWord_503138
  simp only [CollatzResearch.WordTrace]
  refine ⟨4587737612806107493585517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12233966967482953316228045 4587737612806107493585517)
  ·
    refine ⟨1720401604802290310094569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4587737612806107493585517 1720401604802290310094569)
    ·
      refine ⟨1290301203601717732570927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1720401604802290310094569 1290301203601717732570927)
      ·
        refine ⟨1935451805402576598856391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1290301203601717732570927 1935451805402576598856391)
        ·
          refine ⟨2903177708103864898284587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1935451805402576598856391 2903177708103864898284587)
          ·
            refine ⟨4354766562155797347426881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2903177708103864898284587 4354766562155797347426881)
            ·
              refine ⟨3266074921616848010570161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4354766562155797347426881 3266074921616848010570161)
              ·
                refine ⟨2449556191212636007927621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3266074921616848010570161 2449556191212636007927621)
                ·
                  refine ⟨459291785852369251486429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2449556191212636007927621 459291785852369251486429)
                  ·
                    refine ⟨172234419694638469307411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 459291785852369251486429 172234419694638469307411)
                    ·
                      rfl

theorem cell22_503138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 2, 2, 4, 3].length) (baseStart_503138 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_503138 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_503138 prefixEnd_503138 := by exact prefixLift 503138
  have htrace : WordTrace (prefixWord ++ tailWord_503138) baseStart_503138 baseEnd_503138 := by
    simpa [prefixWord, tailWord_503138, baseEnd_503138] using wordTrace_append hprefix tailTrace_503138
  have hstable : (prefixWord ++ tailWord_503138).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_503138).length < 2 ^ (prefixWord ++ tailWord_503138).sum := by decide
  have hdescent : baseEnd_503138 < baseStart_503138 := by decide
  rcases family_descends (prefixWord ++ tailWord_503138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_503213 : List Nat := [1, 5, 2, 2, 1, 1, 2, 1, 7]
def baseStart_503213 : Nat := 118140960795 + 503213 * 2 ^ 59
def prefixEnd_503213 : Nat := 4983230072969 + 3 ^ 40 * 503213 * 2
def baseEnd_503213 : Nat := 57420031242454424560727

theorem tailTrace_503213 : CollatzResearch.WordTrace tailWord_503213 prefixEnd_503213 57420031242454424560727 := by
  unfold tailWord_503213
  simp only [CollatzResearch.WordTrace]
  refine ⟨18353685925952717783322293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12235790617301811855548195 18353685925952717783322293)
  ·
    refine ⟨1720658055558067292186465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 18353685925952717783322293 1720658055558067292186465)
    ·
      refine ⟨1290493541668550469139849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1720658055558067292186465 1290493541668550469139849)
      ·
        refine ⟨967870156251412851854887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1290493541668550469139849 967870156251412851854887)
        ·
          refine ⟨1451805234377119277782331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 967870156251412851854887 1451805234377119277782331)
          ·
            refine ⟨2177707851565678916673497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1451805234377119277782331 2177707851565678916673497)
            ·
              refine ⟨1633280888674259187505123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2177707851565678916673497 1633280888674259187505123)
              ·
                refine ⟨2449921333011388781257685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1633280888674259187505123 2449921333011388781257685)
                ·
                  refine ⟨57420031242454424560727, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2449921333011388781257685 57420031242454424560727)
                  ·
                    rfl

theorem cell22_503213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 2, 1, 7].length) (baseStart_503213 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_503213 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_503213 prefixEnd_503213 := by exact prefixLift 503213
  have htrace : WordTrace (prefixWord ++ tailWord_503213) baseStart_503213 baseEnd_503213 := by
    simpa [prefixWord, tailWord_503213, baseEnd_503213] using wordTrace_append hprefix tailTrace_503213
  have hstable : (prefixWord ++ tailWord_503213).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_503213).length < 2 ^ (prefixWord ++ tailWord_503213).sum := by decide
  have hdescent : baseEnd_503213 < baseStart_503213 := by decide
  rcases family_descends (prefixWord ++ tailWord_503213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_503217 : List Nat := [1, 2, 2, 4, 1, 1, 5, 2, 1, 3]
def baseStart_503217 : Nat := 118140960795 + 503217 * 2 ^ 59
def prefixEnd_503217 : Nat := 4983230072969 + 3 ^ 40 * 503217 * 2
def baseEnd_503217 : Nat := 172261463009108596582169

theorem tailTrace_503217 : CollatzResearch.WordTrace tailWord_503217 prefixEnd_503217 172261463009108596582169 := by
  unfold tailWord_503217
  simp only [CollatzResearch.WordTrace]
  refine ⟨18353831817938226466467905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12235887878625484310978603 18353831817938226466467905)
  ·
    refine ⟨13765373863453669849850929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18353831817938226466467905 13765373863453669849850929)
    ·
      refine ⟨10324030397590252387388197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13765373863453669849850929 10324030397590252387388197)
      ·
        refine ⟨1935755699548172322635287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10324030397590252387388197 1935755699548172322635287)
        ·
          refine ⟨2903633549322258483952931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1935755699548172322635287 2903633549322258483952931)
          ·
            refine ⟨4355450323983387725929397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2903633549322258483952931 4355450323983387725929397)
            ·
              refine ⟨408323467873442599305881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4355450323983387725929397 408323467873442599305881)
              ·
                refine ⟨306242600905081949479411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 408323467873442599305881 306242600905081949479411)
                ·
                  refine ⟨459363901357622924219117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 306242600905081949479411 459363901357622924219117)
                  ·
                    refine ⟨172261463009108596582169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 459363901357622924219117 172261463009108596582169)
                    ·
                      rfl

theorem cell22_503217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 5, 2, 1, 3].length) (baseStart_503217 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_503217 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_503217 prefixEnd_503217 := by exact prefixLift 503217
  have htrace : WordTrace (prefixWord ++ tailWord_503217) baseStart_503217 baseEnd_503217 := by
    simpa [prefixWord, tailWord_503217, baseEnd_503217] using wordTrace_append hprefix tailTrace_503217
  have hstable : (prefixWord ++ tailWord_503217).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_503217).length < 2 ^ (prefixWord ++ tailWord_503217).sum := by decide
  have hdescent : baseEnd_503217 < baseStart_503217 := by decide
  rcases family_descends (prefixWord ++ tailWord_503217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_503243 : List Nat := [1, 1, 1, 1, 3, 3, 5, 2, 1, 4]
def baseStart_503243 : Nat := 118140960795 + 503243 * 2 ^ 59
def prefixEnd_503243 : Nat := 4983230072969 + 3 ^ 40 * 503243 * 2
def baseEnd_503243 : Nat := 172270363340453195432089

theorem tailTrace_503243 : CollatzResearch.WordTrace tailWord_503243 prefixEnd_503243 172270363340453195432089 := by
  unfold tailWord_503243
  simp only [CollatzResearch.WordTrace]
  refine ⟨18354780115844032906914383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12236520077229355271276255 18354780115844032906914383)
  ·
    refine ⟨27532170173766049360371575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18354780115844032906914383 27532170173766049360371575)
    ·
      refine ⟨41298255260649074040557363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27532170173766049360371575 41298255260649074040557363)
      ·
        refine ⟨61947382890973611060836045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41298255260649074040557363 61947382890973611060836045)
        ·
          refine ⟨23230268584115104147813517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61947382890973611060836045 23230268584115104147813517)
          ·
            refine ⟨8711350719043164055430069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23230268584115104147813517 8711350719043164055430069)
            ·
              refine ⟨816689129910296630196569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8711350719043164055430069 816689129910296630196569)
              ·
                refine ⟨612516847432722472647427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 816689129910296630196569 612516847432722472647427)
                ·
                  refine ⟨918775271149083708971141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 612516847432722472647427 918775271149083708971141)
                  ·
                    refine ⟨172270363340453195432089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 918775271149083708971141 172270363340453195432089)
                    ·
                      rfl

theorem cell22_503243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 5, 2, 1, 4].length) (baseStart_503243 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_503243 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_503243 prefixEnd_503243 := by exact prefixLift 503243
  have htrace : WordTrace (prefixWord ++ tailWord_503243) baseStart_503243 baseEnd_503243 := by
    simpa [prefixWord, tailWord_503243, baseEnd_503243] using wordTrace_append hprefix tailTrace_503243
  have hstable : (prefixWord ++ tailWord_503243).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_503243).length < 2 ^ (prefixWord ++ tailWord_503243).sum := by decide
  have hdescent : baseEnd_503243 < baseStart_503243 := by decide
  rcases family_descends (prefixWord ++ tailWord_503243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_503256 : List Nat := [2, 1, 2, 2, 2, 1, 3, 1, 3, 5]
def baseStart_503256 : Nat := 118140960795 + 503256 * 2 ^ 59
def prefixEnd_503256 : Nat := 4983230072969 + 3 ^ 40 * 503256 * 2
def baseEnd_503256 : Nat := 172274813506125494857049

theorem tailTrace_503256 : CollatzResearch.WordTrace tailWord_503256 prefixEnd_503256 172274813506125494857049 := by
  unfold tailWord_503256
  simp only [CollatzResearch.WordTrace]
  refine ⟨9177627132398468063568811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12236836176531290751425081 9177627132398468063568811)
  ·
    refine ⟨13766440698597702095353217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9177627132398468063568811 13766440698597702095353217)
    ·
      refine ⟨10324830523948276571514913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13766440698597702095353217 10324830523948276571514913)
      ·
        refine ⟨7743622892961207428636185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10324830523948276571514913 7743622892961207428636185)
        ·
          refine ⟨5807717169720905571477139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7743622892961207428636185 5807717169720905571477139)
          ·
            refine ⟨8711575754581358357215709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5807717169720905571477139 8711575754581358357215709)
            ·
              refine ⟨3266840907968009383955891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8711575754581358357215709 3266840907968009383955891)
              ·
                refine ⟨4900261361952014075933837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3266840907968009383955891 4900261361952014075933837)
                ·
                  refine ⟨1837598010732005278475189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4900261361952014075933837 1837598010732005278475189)
                  ·
                    refine ⟨172274813506125494857049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1837598010732005278475189 172274813506125494857049)
                    ·
                      rfl

theorem cell22_503256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 3, 1, 3, 5].length) (baseStart_503256 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_503256 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_503256 prefixEnd_503256 := by exact prefixLift 503256
  have htrace : WordTrace (prefixWord ++ tailWord_503256) baseStart_503256 baseEnd_503256 := by
    simpa [prefixWord, tailWord_503256, baseEnd_503256] using wordTrace_append hprefix tailTrace_503256
  have hstable : (prefixWord ++ tailWord_503256).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_503256).length < 2 ^ (prefixWord ++ tailWord_503256).sum := by decide
  have hdescent : baseEnd_503256 < baseStart_503256 := by decide
  rcases family_descends (prefixWord ++ tailWord_503256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_503425 : List Nat := [1, 2, 4, 2, 1, 3, 1, 2, 1, 5]
def baseStart_503425 : Nat := 118140960795 + 503425 * 2 ^ 59
def prefixEnd_503425 : Nat := 4983230072969 + 3 ^ 40 * 503425 * 2
def baseEnd_503425 : Nat := 172332665659865387381531

theorem tailTrace_503425 : CollatzResearch.WordTrace tailWord_503425 prefixEnd_503425 172332665659865387381531 := by
  unfold tailWord_503425
  simp only [CollatzResearch.WordTrace]
  refine ⟨18361418201184677990039729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12240945467456451993359819 18361418201184677990039729)
  ·
    refine ⟨13771063650888508492529797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18361418201184677990039729 13771063650888508492529797)
    ·
      refine ⟨2582074434541595342349337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13771063650888508492529797 2582074434541595342349337)
      ·
        refine ⟨1936555825906196506762003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2582074434541595342349337 1936555825906196506762003)
        ·
          refine ⟨2904833738859294760143005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1936555825906196506762003 2904833738859294760143005)
          ·
            refine ⟨1089312652072235535053627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2904833738859294760143005 1089312652072235535053627)
            ·
              refine ⟨1633968978108353302580441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1089312652072235535053627 1633968978108353302580441)
              ·
                refine ⟨1225476733581264976935331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1633968978108353302580441 1225476733581264976935331)
                ·
                  refine ⟨1838215100371897465402997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1225476733581264976935331 1838215100371897465402997)
                  ·
                    refine ⟨172332665659865387381531, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1838215100371897465402997 172332665659865387381531)
                    ·
                      rfl

theorem cell22_503425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 3, 1, 2, 1, 5].length) (baseStart_503425 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_503425 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_503425 prefixEnd_503425 := by exact prefixLift 503425
  have htrace : WordTrace (prefixWord ++ tailWord_503425) baseStart_503425 baseEnd_503425 := by
    simpa [prefixWord, tailWord_503425, baseEnd_503425] using wordTrace_append hprefix tailTrace_503425
  have hstable : (prefixWord ++ tailWord_503425).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_503425).length < 2 ^ (prefixWord ++ tailWord_503425).sum := by decide
  have hdescent : baseEnd_503425 < baseStart_503425 := by decide
  rcases family_descends (prefixWord ++ tailWord_503425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_503438 : List Nat := [4, 1, 1, 3, 1, 12]
def baseStart_503438 : Nat := 118140960795 + 503438 * 2 ^ 59
def prefixEnd_503438 : Nat := 4983230072969 + 3 ^ 40 * 503438 * 2
def baseEnd_503438 : Nat := 2127618713895526997611

theorem tailTrace_503438 : CollatzResearch.WordTrace tailWord_503438 prefixEnd_503438 2127618713895526997611 := by
  unfold tailWord_503438
  simp only [CollatzResearch.WordTrace]
  refine ⟨2295236543767197651282871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12241261566758387473508645 2295236543767197651282871)
  ·
    refine ⟨3442854815650796476924307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2295236543767197651282871 3442854815650796476924307)
    ·
      refine ⟨5164282223476194715386461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3442854815650796476924307 5164282223476194715386461)
      ·
        refine ⟨1936605833803573018269923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5164282223476194715386461 1936605833803573018269923)
        ·
          refine ⟨2904908750705359527404885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1936605833803573018269923 2904908750705359527404885)
          ·
            refine ⟨2127618713895526997611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 2904908750705359527404885 2127618713895526997611)
            ·
              rfl

theorem cell22_503438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 12].length) (baseStart_503438 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_503438 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_503438 prefixEnd_503438 := by exact prefixLift 503438
  have htrace : WordTrace (prefixWord ++ tailWord_503438) baseStart_503438 baseEnd_503438 := by
    simpa [prefixWord, tailWord_503438, baseEnd_503438] using wordTrace_append hprefix tailTrace_503438
  have hstable : (prefixWord ++ tailWord_503438).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_503438).length < 2 ^ (prefixWord ++ tailWord_503438).sum := by decide
  have hdescent : baseEnd_503438 < baseStart_503438 := by decide
  rcases family_descends (prefixWord ++ tailWord_503438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_503444 : List Nat := [2, 4, 2, 2, 2, 1, 1, 4, 4]
def baseStart_503444 : Nat := 118140960795 + 503444 * 2 ^ 59
def prefixEnd_503444 : Nat := 4983230072969 + 3 ^ 40 * 503444 * 2
def baseEnd_503444 : Nat := 57446389916051890385491

theorem tailTrace_503444 : CollatzResearch.WordTrace tailWord_503444 prefixEnd_503444 57446389916051890385491 := by
  unfold tailWord_503444
  simp only [CollatzResearch.WordTrace]
  refine ⟨9181055594057922117490693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12241407458743896156654257 9181055594057922117490693)
  ·
    refine ⟨1721447923885860397029505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9181055594057922117490693 1721447923885860397029505)
    ·
      refine ⟨1291085942914395297772129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1721447923885860397029505 1291085942914395297772129)
      ·
        refine ⟨968314457185796473329097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1291085942914395297772129 968314457185796473329097)
        ·
          refine ⟨726235842889347354996823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 968314457185796473329097 726235842889347354996823)
          ·
            refine ⟨1089353764334021032495235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 726235842889347354996823 1089353764334021032495235)
            ·
              refine ⟨1634030646501031548742853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1089353764334021032495235 1634030646501031548742853)
              ·
                refine ⟨306380746218943415389285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1634030646501031548742853 306380746218943415389285)
                ·
                  refine ⟨57446389916051890385491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 306380746218943415389285 57446389916051890385491)
                  ·
                    rfl

theorem cell22_503444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 1, 1, 4, 4].length) (baseStart_503444 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_503444 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_503444 prefixEnd_503444 := by exact prefixLift 503444
  have htrace : WordTrace (prefixWord ++ tailWord_503444) baseStart_503444 baseEnd_503444 := by
    simpa [prefixWord, tailWord_503444, baseEnd_503444] using wordTrace_append hprefix tailTrace_503444
  have hstable : (prefixWord ++ tailWord_503444).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_503444).length < 2 ^ (prefixWord ++ tailWord_503444).sum := by decide
  have hdescent : baseEnd_503444 < baseStart_503444 := by decide
  rcases family_descends (prefixWord ++ tailWord_503444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_503453 : List Nat := [1, 4, 2, 1, 1, 1, 1, 2, 2, 7]
def baseStart_503453 : Nat := 118140960795 + 503453 * 2 ^ 59
def prefixEnd_503453 : Nat := 4983230072969 + 3 ^ 40 * 503453 * 2
def baseEnd_503453 : Nat := 172342250632082647681445

theorem tailTrace_503453 : CollatzResearch.WordTrace tailWord_503453 prefixEnd_503453 172342250632082647681445 := by
  unfold tailWord_503453
  simp only [CollatzResearch.WordTrace]
  refine ⟨18362439445083238772059013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12241626296722159181372675 18362439445083238772059013)
  ·
    refine ⟨3442957395953107269761065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18362439445083238772059013 3442957395953107269761065)
    ·
      refine ⟨2582218046964830452320799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3442957395953107269761065 2582218046964830452320799)
      ·
        refine ⟨3873327070447245678481199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2582218046964830452320799 3873327070447245678481199)
        ·
          refine ⟨5809990605670868517721799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3873327070447245678481199 5809990605670868517721799)
          ·
            refine ⟨8714985908506302776582699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5809990605670868517721799 8714985908506302776582699)
            ·
              refine ⟨13072478862759454164874049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8714985908506302776582699 13072478862759454164874049)
              ·
                refine ⟨9804359147069590623655537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13072478862759454164874049 9804359147069590623655537)
                ·
                  refine ⟨7353269360302192967741653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9804359147069590623655537 7353269360302192967741653)
                  ·
                    refine ⟨172342250632082647681445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 7353269360302192967741653 172342250632082647681445)
                    ·
                      rfl

theorem cell22_503453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 2, 2, 7].length) (baseStart_503453 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_503453 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_503453 prefixEnd_503453 := by exact prefixLift 503453
  have htrace : WordTrace (prefixWord ++ tailWord_503453) baseStart_503453 baseEnd_503453 := by
    simpa [prefixWord, tailWord_503453, baseEnd_503453] using wordTrace_append hprefix tailTrace_503453
  have hstable : (prefixWord ++ tailWord_503453).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_503453).length < 2 ^ (prefixWord ++ tailWord_503453).sum := by decide
  have hdescent : baseEnd_503453 < baseStart_503453 := by decide
  rcases family_descends (prefixWord ++ tailWord_503453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_503530 : List Nat := [3, 1, 3, 1, 1, 1, 2, 3, 3, 4]
def baseStart_503530 : Nat := 118140960795 + 503530 * 2 ^ 59
def prefixEnd_503530 : Nat := 4983230072969 + 3 ^ 40 * 503530 * 2
def baseEnd_503530 : Nat := 172368609305680113506209

theorem tailTrace_503530 : CollatzResearch.WordTrace tailWord_503530 prefixEnd_503530 172368609305680113506209 := by
  unfold tailWord_503530
  simp only [CollatzResearch.WordTrace]
  refine ⟨4591311966451070230653011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12243498577202853948408029 4591311966451070230653011)
  ·
    refine ⟨6886967949676605345979517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4591311966451070230653011 6886967949676605345979517)
    ·
      refine ⟨2582612981128727004742319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6886967949676605345979517 2582612981128727004742319)
      ·
        refine ⟨3873919471693090507113479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2582612981128727004742319 3873919471693090507113479)
        ·
          refine ⟨5810879207539635760670219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3873919471693090507113479 5810879207539635760670219)
          ·
            refine ⟨8716318811309453641005329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5810879207539635760670219 8716318811309453641005329)
            ·
              refine ⟨6537239108482090230753997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8716318811309453641005329 6537239108482090230753997)
              ·
                refine ⟨2451464665680783836532749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6537239108482090230753997 2451464665680783836532749)
                ·
                  refine ⟨919299249630293938699781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2451464665680783836532749 919299249630293938699781)
                  ·
                    refine ⟨172368609305680113506209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 919299249630293938699781 172368609305680113506209)
                    ·
                      rfl

theorem cell22_503530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 2, 3, 3, 4].length) (baseStart_503530 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_503530 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_503530 prefixEnd_503530 := by exact prefixLift 503530
  have htrace : WordTrace (prefixWord ++ tailWord_503530) baseStart_503530 baseEnd_503530 := by
    simpa [prefixWord, tailWord_503530, baseEnd_503530] using wordTrace_append hprefix tailTrace_503530
  have hstable : (prefixWord ++ tailWord_503530).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_503530).length < 2 ^ (prefixWord ++ tailWord_503530).sum := by decide
  have hdescent : baseEnd_503530 < baseStart_503530 := by decide
  rcases family_descends (prefixWord ++ tailWord_503530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_503562 : List Nat := [3, 1, 2, 2, 1, 5, 1, 1, 6]
def baseStart_503562 : Nat := 118140960795 + 503562 * 2 ^ 59
def prefixEnd_503562 : Nat := 4983230072969 + 3 ^ 40 * 503562 * 2
def baseEnd_503562 : Nat := 57459854519880898902037

theorem tailTrace_503562 : CollatzResearch.WordTrace tailWord_503562 prefixEnd_503562 57459854519880898902037 := by
  unfold tailWord_503562
  simp only [CollatzResearch.WordTrace]
  refine ⟨4591603750422087596944235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12244276667792233591851293 4591603750422087596944235)
  ·
    refine ⟨6887405625633131395416353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4591603750422087596944235 6887405625633131395416353)
    ·
      refine ⟨5165554219224848546562265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6887405625633131395416353 5165554219224848546562265)
      ·
        refine ⟨3874165664418636409921699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5165554219224848546562265 3874165664418636409921699)
        ·
          refine ⟨5811248496627954614882549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3874165664418636409921699 5811248496627954614882549)
          ·
            refine ⟨544804546558870745145239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 5811248496627954614882549 544804546558870745145239)
            ·
              refine ⟨817206819838306117717859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 544804546558870745145239 817206819838306117717859)
              ·
                refine ⟨1225810229757459176576789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 817206819838306117717859 1225810229757459176576789)
                ·
                  refine ⟨57459854519880898902037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1225810229757459176576789 57459854519880898902037)
                  ·
                    rfl

theorem cell22_503562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 5, 1, 1, 6].length) (baseStart_503562 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_503562 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_503562 prefixEnd_503562 := by exact prefixLift 503562
  have htrace : WordTrace (prefixWord ++ tailWord_503562) baseStart_503562 baseEnd_503562 := by
    simpa [prefixWord, tailWord_503562, baseEnd_503562] using wordTrace_append hprefix tailTrace_503562
  have hstable : (prefixWord ++ tailWord_503562).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_503562).length < 2 ^ (prefixWord ++ tailWord_503562).sum := by decide
  have hdescent : baseEnd_503562 < baseStart_503562 := by decide
  rcases family_descends (prefixWord ++ tailWord_503562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_503592 : List Nat := [2, 1, 5, 1, 1, 2, 1, 3, 2, 4]
def baseStart_503592 : Nat := 118140960795 + 503592 * 2 ^ 59
def prefixEnd_503592 : Nat := 4983230072969 + 3 ^ 40 * 503592 * 2
def baseEnd_503592 : Nat := 172389833172732618456019

theorem tailTrace_503592 : CollatzResearch.WordTrace tailWord_503592 prefixEnd_503592 172389833172732618456019 := by
  unfold tailWord_503592
  simp only [CollatzResearch.WordTrace]
  refine ⟨9183754595789832755684515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12245006127719777007579353 9183754595789832755684515)
  ·
    refine ⟨13775631893684749133526773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9183754595789832755684515 13775631893684749133526773)
    ·
      refine ⟨1291465490032945231268135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 13775631893684749133526773 1291465490032945231268135)
      ·
        refine ⟨1937198235049417846902203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1291465490032945231268135 1937198235049417846902203)
        ·
          refine ⟨2905797352574126770353305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1937198235049417846902203 2905797352574126770353305)
          ·
            refine ⟨2179348014430595077764979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2905797352574126770353305 2179348014430595077764979)
            ·
              refine ⟨3269022021645892616647469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2179348014430595077764979 3269022021645892616647469)
              ·
                refine ⟨1225883258117209731242801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3269022021645892616647469 1225883258117209731242801)
                ·
                  refine ⟨919412443587907298432101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1225883258117209731242801 919412443587907298432101)
                  ·
                    refine ⟨172389833172732618456019, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 919412443587907298432101 172389833172732618456019)
                    ·
                      rfl

theorem cell22_503592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 1, 3, 2, 4].length) (baseStart_503592 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_503592 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_503592 prefixEnd_503592 := by exact prefixLift 503592
  have htrace : WordTrace (prefixWord ++ tailWord_503592) baseStart_503592 baseEnd_503592 := by
    simpa [prefixWord, tailWord_503592, baseEnd_503592] using wordTrace_append hprefix tailTrace_503592
  have hstable : (prefixWord ++ tailWord_503592).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_503592).length < 2 ^ (prefixWord ++ tailWord_503592).sum := by decide
  have hdescent : baseEnd_503592 < baseStart_503592 := by decide
  rcases family_descends (prefixWord ++ tailWord_503592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_503639 : List Nat := [1, 1, 3, 2, 5, 1, 1, 2, 3, 3]
def baseStart_503639 : Nat := 118140960795 + 503639 * 2 ^ 59
def prefixEnd_503639 : Nat := 4983230072969 + 3 ^ 40 * 503639 * 2
def baseEnd_503639 : Nat := 172405922233240162530875

theorem tailTrace_503639 : CollatzResearch.WordTrace tailWord_503639 prefixEnd_503639 172405922233240162530875 := by
  unfold tailWord_503639
  simp only [CollatzResearch.WordTrace]
  refine ⟨18369223422409392538329971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12246148948272928358886647 18369223422409392538329971)
  ·
    refine ⟨27553835133614088807494957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18369223422409392538329971 27553835133614088807494957)
    ·
      refine ⟨10332688175105283302810609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27553835133614088807494957 10332688175105283302810609)
      ·
        refine ⟨7749516131328962477107957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10332688175105283302810609 7749516131328962477107957)
        ·
          refine ⟨726517137312090232228871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 7749516131328962477107957 726517137312090232228871)
          ·
            refine ⟨1089775705968135348343307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 726517137312090232228871 1089775705968135348343307)
            ·
              refine ⟨1634663558952203022514961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1089775705968135348343307 1634663558952203022514961)
              ·
                refine ⟨1225997669214152266886221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1634663558952203022514961 1225997669214152266886221)
                ·
                  refine ⟨459749125955307100082333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1225997669214152266886221 459749125955307100082333)
                  ·
                    refine ⟨172405922233240162530875, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 459749125955307100082333 172405922233240162530875)
                    ·
                      rfl

theorem cell22_503639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 1, 1, 2, 3, 3].length) (baseStart_503639 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_503639 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_503639 prefixEnd_503639 := by exact prefixLift 503639
  have htrace : WordTrace (prefixWord ++ tailWord_503639) baseStart_503639 baseEnd_503639 := by
    simpa [prefixWord, tailWord_503639, baseEnd_503639] using wordTrace_append hprefix tailTrace_503639
  have hstable : (prefixWord ++ tailWord_503639).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_503639).length < 2 ^ (prefixWord ++ tailWord_503639).sum := by decide
  have hdescent : baseEnd_503639 < baseStart_503639 := by decide
  rcases family_descends (prefixWord ++ tailWord_503639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_503656 : List Nat := [2, 1, 4, 2, 1, 1, 4, 3, 1, 3]
def baseStart_503656 : Nat := 118140960795 + 503656 * 2 ^ 59
def prefixEnd_503656 : Nat := 4983230072969 + 3 ^ 40 * 503656 * 2
def baseEnd_503656 : Nat := 172411741680657784855823

theorem tailTrace_503656 : CollatzResearch.WordTrace tailWord_503656 prefixEnd_503656 172411741680657784855823 := by
  unfold tailWord_503656
  simp only [CollatzResearch.WordTrace]
  refine ⟨9184921731673902220849411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12246562308898536294465881 9184921731673902220849411)
  ·
    refine ⟨13777382597510853331274117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9184921731673902220849411 13777382597510853331274117)
    ·
      refine ⟨2583259237033284999613897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13777382597510853331274117 2583259237033284999613897)
      ·
        refine ⟨1937444427774963749710423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2583259237033284999613897 1937444427774963749710423)
        ·
          refine ⟨2906166641662445624565635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1937444427774963749710423 2906166641662445624565635)
          ·
            refine ⟨4359249962493668436848453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2906166641662445624565635 4359249962493668436848453)
            ·
              refine ⟨817359367967562831909085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4359249962493668436848453 817359367967562831909085)
              ·
                refine ⟨306509762987836061965907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 817359367967562831909085 306509762987836061965907)
                ·
                  refine ⟨459764644481754092948861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 306509762987836061965907 459764644481754092948861)
                  ·
                    refine ⟨172411741680657784855823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 459764644481754092948861 172411741680657784855823)
                    ·
                      rfl

theorem cell22_503656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 4, 3, 1, 3].length) (baseStart_503656 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_503656 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_503656 prefixEnd_503656 := by exact prefixLift 503656
  have htrace : WordTrace (prefixWord ++ tailWord_503656) baseStart_503656 baseEnd_503656 := by
    simpa [prefixWord, tailWord_503656, baseEnd_503656] using wordTrace_append hprefix tailTrace_503656
  have hstable : (prefixWord ++ tailWord_503656).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_503656).length < 2 ^ (prefixWord ++ tailWord_503656).sum := by decide
  have hdescent : baseEnd_503656 < baseStart_503656 := by decide
  rcases family_descends (prefixWord ++ tailWord_503656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_503727 : List Nat := [1, 1, 2, 1, 2, 2, 5, 2, 2, 4]
def baseStart_503727 : Nat := 118140960795 + 503727 * 2 ^ 59
def prefixEnd_503727 : Nat := 4983230072969 + 3 ^ 40 * 503727 * 2
def baseEnd_503727 : Nat := 172436046431637266330605

theorem tailTrace_503727 : CollatzResearch.WordTrace tailWord_503727 prefixEnd_503727 172436046431637266330605 := by
  unfold tailWord_503727
  simp only [CollatzResearch.WordTrace]
  refine ⟨18372433046090583567533435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12248288697393722378355623 18372433046090583567533435)
  ·
    refine ⟨27558649569135875351300153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18372433046090583567533435 27558649569135875351300153)
    ·
      refine ⟨20668987176851906513475115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27558649569135875351300153 20668987176851906513475115)
      ·
        refine ⟨31003480765277859770212673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20668987176851906513475115 31003480765277859770212673)
        ·
          refine ⟨23252610573958394827659505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31003480765277859770212673 23252610573958394827659505)
          ·
            refine ⟨17439457930468796120744629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23252610573958394827659505 17439457930468796120744629)
            ·
              refine ⟨1634949180981449636319809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 17439457930468796120744629 1634949180981449636319809)
              ·
                refine ⟨1226211885736087227239857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1634949180981449636319809 1226211885736087227239857)
                ·
                  refine ⟨919658914302065420429893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1226211885736087227239857 919658914302065420429893)
                  ·
                    refine ⟨172436046431637266330605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 919658914302065420429893 172436046431637266330605)
                    ·
                      rfl

theorem cell22_503727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 5, 2, 2, 4].length) (baseStart_503727 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_503727 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_503727 prefixEnd_503727 := by exact prefixLift 503727
  have htrace : WordTrace (prefixWord ++ tailWord_503727) baseStart_503727 baseEnd_503727 := by
    simpa [prefixWord, tailWord_503727, baseEnd_503727] using wordTrace_append hprefix tailTrace_503727
  have hstable : (prefixWord ++ tailWord_503727).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_503727).length < 2 ^ (prefixWord ++ tailWord_503727).sum := by decide
  have hdescent : baseEnd_503727 < baseStart_503727 := by decide
  rcases family_descends (prefixWord ++ tailWord_503727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_503729 : List Nat := [1, 2, 2, 4, 2, 1, 2, 1, 4, 3]
def baseStart_503729 : Nat := 118140960795 + 503729 * 2 ^ 59
def prefixEnd_503729 : Nat := 4983230072969 + 3 ^ 40 * 503729 * 2
def baseEnd_503729 : Nat := 172436731072509927780599

theorem tailTrace_503729 : CollatzResearch.WordTrace tailWord_503729 prefixEnd_503729 172436731072509927780599 := by
  unfold tailWord_503729
  simp only [CollatzResearch.WordTrace]
  refine ⟨18372505992083337909106241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12248337328055558606070827 18372505992083337909106241)
  ·
    refine ⟨13779379494062503431829681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18372505992083337909106241 13779379494062503431829681)
    ·
      refine ⟨10334534620546877573872261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13779379494062503431829681 10334534620546877573872261)
      ·
        refine ⟨1937725241352539545101049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10334534620546877573872261 1937725241352539545101049)
        ·
          refine ⟨1453293931014404658825787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1937725241352539545101049 1453293931014404658825787)
          ·
            refine ⟨2179940896521606988238681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1453293931014404658825787 2179940896521606988238681)
            ·
              refine ⟨1634955672391205241179011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2179940896521606988238681 1634955672391205241179011)
              ·
                refine ⟨2452433508586807861768517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1634955672391205241179011 2452433508586807861768517)
                ·
                  refine ⟨459831282860026474081597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2452433508586807861768517 459831282860026474081597)
                  ·
                    refine ⟨172436731072509927780599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 459831282860026474081597 172436731072509927780599)
                    ·
                      rfl

theorem cell22_503729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 2, 1, 4, 3].length) (baseStart_503729 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_503729 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_503729 prefixEnd_503729 := by exact prefixLift 503729
  have htrace : WordTrace (prefixWord ++ tailWord_503729) baseStart_503729 baseEnd_503729 := by
    simpa [prefixWord, tailWord_503729, baseEnd_503729] using wordTrace_append hprefix tailTrace_503729
  have hstable : (prefixWord ++ tailWord_503729).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_503729).length < 2 ^ (prefixWord ++ tailWord_503729).sum := by decide
  have hdescent : baseEnd_503729 < baseStart_503729 := by decide
  rcases family_descends (prefixWord ++ tailWord_503729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_503742 : List Nat := [4, 2, 1, 1, 1, 3, 1, 9]
def baseStart_503742 : Nat := 118140960795 + 503742 * 2 ^ 59
def prefixEnd_503742 : Nat := 4983230072969 + 3 ^ 40 * 503742 * 2
def baseEnd_503742 : Nat := 19160131248686914133951

theorem tailTrace_503742 : CollatzResearch.WordTrace tailWord_503742 prefixEnd_503742 19160131248686914133951 := by
  unfold tailWord_503742
  simp only [CollatzResearch.WordTrace]
  refine ⟨2296622517629530141166185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12248653427357494086219653 2296622517629530141166185)
  ·
    refine ⟨1722466888222147605874639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2296622517629530141166185 1722466888222147605874639)
    ·
      refine ⟨2583700332333221408811959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1722466888222147605874639 2583700332333221408811959)
      ·
        refine ⟨3875550498499832113217939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2583700332333221408811959 3875550498499832113217939)
        ·
          refine ⟨5813325747749748169826909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3875550498499832113217939 5813325747749748169826909)
          ·
            refine ⟨2179997155406155563685091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5813325747749748169826909 2179997155406155563685091)
            ·
              refine ⟨3269995733109233345527637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2179997155406155563685091 3269995733109233345527637)
              ·
                refine ⟨19160131248686914133951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 3269995733109233345527637 19160131248686914133951)
                ·
                  rfl

theorem cell22_503742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 1, 9].length) (baseStart_503742 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_503742 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_503742 prefixEnd_503742 := by exact prefixLift 503742
  have htrace : WordTrace (prefixWord ++ tailWord_503742) baseStart_503742 baseEnd_503742 := by
    simpa [prefixWord, tailWord_503742, baseEnd_503742] using wordTrace_append hprefix tailTrace_503742
  have hstable : (prefixWord ++ tailWord_503742).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_503742).length < 2 ^ (prefixWord ++ tailWord_503742).sum := by decide
  have hdescent : baseEnd_503742 < baseStart_503742 := by decide
  rcases family_descends (prefixWord ++ tailWord_503742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_503791 : List Nat := [1, 1, 2, 1, 4, 2, 3, 4, 1, 3]
def baseStart_503791 : Nat := 118140960795 + 503791 * 2 ^ 59
def prefixEnd_503791 : Nat := 4983230072969 + 3 ^ 40 * 503791 * 2
def baseEnd_503791 : Nat := 172457954939562432730409

theorem tailTrace_503791 : CollatzResearch.WordTrace tailWord_503791 prefixEnd_503791 172457954939562432730409 := by
  unfold tailWord_503791
  simp only [CollatzResearch.WordTrace]
  refine ⟨18374767317858722497863227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12249844878572481665242151 18374767317858722497863227)
  ·
    refine ⟨27562150976788083746794841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18374767317858722497863227 27562150976788083746794841)
    ·
      refine ⟨20671613232591062810096131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27562150976788083746794841 20671613232591062810096131)
      ·
        refine ⟨31007419848886594215144197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20671613232591062810096131 31007419848886594215144197)
        ·
          refine ⟨5813891221666236415339537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31007419848886594215144197 5813891221666236415339537)
          ·
            refine ⟨4360418416249677311504653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5813891221666236415339537 4360418416249677311504653)
            ·
              refine ⟨1635156906093628991814245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4360418416249677311504653 1635156906093628991814245)
              ·
                refine ⟨306591919892555435965171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1635156906093628991814245 306591919892555435965171)
                ·
                  refine ⟨459887879838833153947757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 306591919892555435965171 459887879838833153947757)
                  ·
                    refine ⟨172457954939562432730409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 459887879838833153947757 172457954939562432730409)
                    ·
                      rfl

theorem cell22_503791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 3, 4, 1, 3].length) (baseStart_503791 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_503791 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_503791 prefixEnd_503791 := by exact prefixLift 503791
  have htrace : WordTrace (prefixWord ++ tailWord_503791) baseStart_503791 baseEnd_503791 := by
    simpa [prefixWord, tailWord_503791, baseEnd_503791] using wordTrace_append hprefix tailTrace_503791
  have hstable : (prefixWord ++ tailWord_503791).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_503791).length < 2 ^ (prefixWord ++ tailWord_503791).sum := by decide
  have hdescent : baseEnd_503791 < baseStart_503791 := by decide
  rcases family_descends (prefixWord ++ tailWord_503791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_503832 : List Nat := [2, 1, 2, 3, 2, 1, 1, 2, 8]
def baseStart_503832 : Nat := 118140960795 + 503832 * 2 ^ 59
def prefixEnd_503832 : Nat := 4983230072969 + 3 ^ 40 * 503832 * 2
def baseEnd_503832 : Nat := 57490663359150664151761

theorem tailTrace_503832 : CollatzResearch.WordTrace tailWord_503832 prefixEnd_503832 57490663359150664151761 := by
  unfold tailWord_503832
  simp only [CollatzResearch.WordTrace]
  refine ⟨9188131355355093250052875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12250841807140124333403833 9188131355355093250052875)
  ·
    refine ⟨13782197033032639875079313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9188131355355093250052875 13782197033032639875079313)
    ·
      refine ⟨10336647774774479906309485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13782197033032639875079313 10336647774774479906309485)
      ·
        refine ⟨3876242915540429964866057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10336647774774479906309485 3876242915540429964866057)
        ·
          refine ⟨2907182186655322473649543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3876242915540429964866057 2907182186655322473649543)
          ·
            refine ⟨4360773279982983710474315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2907182186655322473649543 4360773279982983710474315)
            ·
              refine ⟨6541159919974475565711473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4360773279982983710474315 6541159919974475565711473)
              ·
                refine ⟨4905869939980856674283605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6541159919974475565711473 4905869939980856674283605)
                ·
                  refine ⟨57490663359150664151761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 4905869939980856674283605 57490663359150664151761)
                  ·
                    rfl

theorem cell22_503832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 1, 2, 8].length) (baseStart_503832 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_503832 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_503832 prefixEnd_503832 := by exact prefixLift 503832
  have htrace : WordTrace (prefixWord ++ tailWord_503832) baseStart_503832 baseEnd_503832 := by
    simpa [prefixWord, tailWord_503832, baseEnd_503832] using wordTrace_append hprefix tailTrace_503832
  have hstable : (prefixWord ++ tailWord_503832).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_503832).length < 2 ^ (prefixWord ++ tailWord_503832).sum := by decide
  have hdescent : baseEnd_503832 < baseStart_503832 := by decide
  rcases family_descends (prefixWord ++ tailWord_503832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_503879 : List Nat := [1, 1, 4, 1, 3, 1, 2, 3, 2, 4]
def baseStart_503879 : Nat := 118140960795 + 503879 * 2 ^ 59
def prefixEnd_503879 : Nat := 4983230072969 + 3 ^ 40 * 503879 * 2
def baseEnd_503879 : Nat := 172488079137959536530139

theorem tailTrace_503879 : CollatzResearch.WordTrace tailWord_503879 prefixEnd_503879 172488079137959536530139 := by
  unfold tailWord_503879
  simp only [CollatzResearch.WordTrace]
  refine ⟨18377976941539913527066691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12251984627693275684711127 18377976941539913527066691)
  ·
    refine ⟨27566965412309870290600037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18377976941539913527066691 27566965412309870290600037)
    ·
      refine ⟨5168806014808100679487507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27566965412309870290600037 5168806014808100679487507)
      ·
        refine ⟨7753209022212151019231261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5168806014808100679487507 7753209022212151019231261)
        ·
          refine ⟨2907453383329556632211723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7753209022212151019231261 2907453383329556632211723)
          ·
            refine ⟨4361180074994334948317585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2907453383329556632211723 4361180074994334948317585)
            ·
              refine ⟨3270885056245751211238189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4361180074994334948317585 3270885056245751211238189)
              ·
                refine ⟨1226581896092156704214321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3270885056245751211238189 1226581896092156704214321)
                ·
                  refine ⟨919936422069117528160741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1226581896092156704214321 919936422069117528160741)
                  ·
                    refine ⟨172488079137959536530139, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 919936422069117528160741 172488079137959536530139)
                    ·
                      rfl

theorem cell22_503879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 2, 3, 2, 4].length) (baseStart_503879 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_503879 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_503879 prefixEnd_503879 := by exact prefixLift 503879
  have htrace : WordTrace (prefixWord ++ tailWord_503879) baseStart_503879 baseEnd_503879 := by
    simpa [prefixWord, tailWord_503879, baseEnd_503879] using wordTrace_append hprefix tailTrace_503879
  have hstable : (prefixWord ++ tailWord_503879).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_503879).length < 2 ^ (prefixWord ++ tailWord_503879).sum := by decide
  have hdescent : baseEnd_503879 < baseStart_503879 := by decide
  rcases family_descends (prefixWord ++ tailWord_503879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_503960 : List Nat := [2, 1, 2, 4, 3, 1, 1, 4, 1, 3]
def baseStart_503960 : Nat := 118140960795 + 503960 * 2 ^ 59
def prefixEnd_503960 : Nat := 4983230072969 + 3 ^ 40 * 503960 * 2
def baseEnd_503960 : Nat := 172515807093302325254891

theorem tailTrace_503960 : CollatzResearch.WordTrace tailWord_503960 prefixEnd_503960 172515807093302325254891 := by
  unfold tailWord_503960
  simp only [CollatzResearch.WordTrace]
  refine ⟨9190465627123232180382667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12253954169497642907176889 9190465627123232180382667)
  ·
    refine ⟨13785698440684848270574001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9190465627123232180382667 13785698440684848270574001)
    ·
      refine ⟨10339273830513636202930501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13785698440684848270574001 10339273830513636202930501)
      ·
        refine ⟨1938613843221306788049469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10339273830513636202930501 1938613843221306788049469)
        ·
          refine ⟨726980191207990045518551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1938613843221306788049469 726980191207990045518551)
          ·
            refine ⟨1090470286811985068277827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 726980191207990045518551 1090470286811985068277827)
            ·
              refine ⟨1635705430217977602416741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1090470286811985068277827 1635705430217977602416741)
              ·
                refine ⟨306694768165870800453139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1635705430217977602416741 306694768165870800453139)
                ·
                  refine ⟨460042152248806200679709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 306694768165870800453139 460042152248806200679709)
                  ·
                    refine ⟨172515807093302325254891, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 460042152248806200679709 172515807093302325254891)
                    ·
                      rfl

theorem cell22_503960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 1, 1, 4, 1, 3].length) (baseStart_503960 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_503960 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_503960 prefixEnd_503960 := by exact prefixLift 503960
  have htrace : WordTrace (prefixWord ++ tailWord_503960) baseStart_503960 baseEnd_503960 := by
    simpa [prefixWord, tailWord_503960, baseEnd_503960] using wordTrace_append hprefix tailTrace_503960
  have hstable : (prefixWord ++ tailWord_503960).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_503960).length < 2 ^ (prefixWord ++ tailWord_503960).sum := by decide
  have hdescent : baseEnd_503960 < baseStart_503960 := by decide
  rcases family_descends (prefixWord ++ tailWord_503960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_503986 : List Nat := [3, 2, 1, 1, 1, 3, 2, 4, 1, 4]
def baseStart_503986 : Nat := 118140960795 + 503986 * 2 ^ 59
def prefixEnd_503986 : Nat := 4983230072969 + 3 ^ 40 * 503986 * 2
def baseEnd_503986 : Nat := 172524707424646924104811

theorem tailTrace_503986 : CollatzResearch.WordTrace tailWord_503986 prefixEnd_503986 172524707424646924104811 := by
  unfold tailWord_503986
  simp only [CollatzResearch.WordTrace]
  refine ⟨4595469888038067700302953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12254586368101513867474541 4595469888038067700302953)
  ·
    refine ⟨3446602416028550775227215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4595469888038067700302953 3446602416028550775227215)
    ·
      refine ⟨5169903624042826162840823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3446602416028550775227215 5169903624042826162840823)
      ·
        refine ⟨7754855436064239244261235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5169903624042826162840823 7754855436064239244261235)
        ·
          refine ⟨11632283154096358866391853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7754855436064239244261235 11632283154096358866391853)
          ·
            refine ⟨4362106182786134574896945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11632283154096358866391853 4362106182786134574896945)
            ·
              refine ⟨3271579637089600931172709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4362106182786134574896945 3271579637089600931172709)
              ·
                refine ⟨613421181954300174594883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3271579637089600931172709 613421181954300174594883)
                ·
                  refine ⟨920131772931450261892325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 613421181954300174594883 920131772931450261892325)
                  ·
                    refine ⟨172524707424646924104811, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 920131772931450261892325 172524707424646924104811)
                    ·
                      rfl

theorem cell22_503986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 2, 4, 1, 4].length) (baseStart_503986 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_503986 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_503986 prefixEnd_503986 := by exact prefixLift 503986
  have htrace : WordTrace (prefixWord ++ tailWord_503986) baseStart_503986 baseEnd_503986 := by
    simpa [prefixWord, tailWord_503986, baseEnd_503986] using wordTrace_append hprefix tailTrace_503986
  have hstable : (prefixWord ++ tailWord_503986).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_503986).length < 2 ^ (prefixWord ++ tailWord_503986).sum := by decide
  have hdescent : baseEnd_503986 < baseStart_503986 := by decide
  rcases family_descends (prefixWord ++ tailWord_503986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_504018 : List Nat := [3, 2, 2, 2, 1, 2, 2, 4, 4]
def baseStart_504018 : Nat := 118140960795 + 504018 * 2 ^ 59
def prefixEnd_504018 : Nat := 4983230072969 + 3 ^ 40 * 504018 * 2
def baseEnd_504018 : Nat := 57511887226203169101571

theorem tailTrace_504018 : CollatzResearch.WordTrace tailWord_504018 prefixEnd_504018 57511887226203169101571 := by
  unfold tailWord_504018
  simp only [CollatzResearch.WordTrace]
  refine ⟨4595761672009085066594177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12255364458690893510917805 4595761672009085066594177)
  ·
    refine ⟨3446821254006813799945633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4595761672009085066594177 3446821254006813799945633)
    ·
      refine ⟨2585115940505110349959225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3446821254006813799945633 2585115940505110349959225)
      ·
        refine ⟨1938836955378832762469419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2585115940505110349959225 1938836955378832762469419)
        ·
          refine ⟨2908255433068249143704129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1938836955378832762469419 2908255433068249143704129)
          ·
            refine ⟨2181191574801186857778097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2908255433068249143704129 2181191574801186857778097)
            ·
              refine ⟨1635893681100890143333573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2181191574801186857778097 1635893681100890143333573)
              ·
                refine ⟨306730065206416901875045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1635893681100890143333573 306730065206416901875045)
                ·
                  refine ⟨57511887226203169101571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 306730065206416901875045 57511887226203169101571)
                  ·
                    rfl

theorem cell22_504018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 2, 4, 4].length) (baseStart_504018 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_504018 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_504018 prefixEnd_504018 := by exact prefixLift 504018
  have htrace : WordTrace (prefixWord ++ tailWord_504018) baseStart_504018 baseEnd_504018 := by
    simpa [prefixWord, tailWord_504018, baseEnd_504018] using wordTrace_append hprefix tailTrace_504018
  have hstable : (prefixWord ++ tailWord_504018).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_504018).length < 2 ^ (prefixWord ++ tailWord_504018).sum := by decide
  have hdescent : baseEnd_504018 < baseStart_504018 := by decide
  rcases family_descends (prefixWord ++ tailWord_504018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_504044 : List Nat := [2, 2, 1, 1, 2, 3, 1, 1, 2, 7]
def baseStart_504044 : Nat := 118140960795 + 504044 * 2 ^ 59
def prefixEnd_504044 : Nat := 4983230072969 + 3 ^ 40 * 504044 * 2
def baseEnd_504044 : Nat := 172544562009954106154633

theorem tailTrace_504044 : CollatzResearch.WordTrace tailWord_504044 prefixEnd_504044 172544562009954106154633 := by
  unfold tailWord_504044
  simp only [CollatzResearch.WordTrace]
  refine ⟨9191997492971073353411593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12255996657294764471215457 9191997492971073353411593)
  ·
    refine ⟨6893998119728305015058695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9191997492971073353411593 6893998119728305015058695)
    ·
      refine ⟨10340997179592457522588043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6893998119728305015058695 10340997179592457522588043)
      ·
        refine ⟨15511495769388686283882065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10340997179592457522588043 15511495769388686283882065)
        ·
          refine ⟨11633621827041514712911549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15511495769388686283882065 11633621827041514712911549)
          ·
            refine ⟨4362608185140568017341831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11633621827041514712911549 4362608185140568017341831)
            ·
              refine ⟨6543912277710852026012747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4362608185140568017341831 6543912277710852026012747)
              ·
                refine ⟨9815868416566278039019121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6543912277710852026012747 9815868416566278039019121)
                ·
                  refine ⟨7361901312424708529264341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9815868416566278039019121 7361901312424708529264341)
                  ·
                    refine ⟨172544562009954106154633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 7361901312424708529264341 172544562009954106154633)
                    ·
                      rfl

theorem cell22_504044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 7].length) (baseStart_504044 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_504044 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_504044 prefixEnd_504044 := by exact prefixLift 504044
  have htrace : WordTrace (prefixWord ++ tailWord_504044) baseStart_504044 baseEnd_504044 := by
    simpa [prefixWord, tailWord_504044, baseEnd_504044] using wordTrace_append hprefix tailTrace_504044
  have hstable : (prefixWord ++ tailWord_504044).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_504044).length < 2 ^ (prefixWord ++ tailWord_504044).sum := by decide
  have hdescent : baseEnd_504044 < baseStart_504044 := by decide
  rcases family_descends (prefixWord ++ tailWord_504044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_504061 : List Nat := [1, 4, 1, 1, 1, 1, 1, 4, 5, 3]
def baseStart_504061 : Nat := 118140960795 + 504061 * 2 ^ 59
def prefixEnd_504061 : Nat := 4983230072969 + 3 ^ 40 * 504061 * 2
def baseEnd_504061 : Nat := 172550381457371728479581

theorem tailTrace_504061 : CollatzResearch.WordTrace tailWord_504061 prefixEnd_504061 172550381457371728479581 := by
  unfold tailWord_504061
  simp only [CollatzResearch.WordTrace]
  refine ⟨18384615026880558610192037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12256410017920372406794691 18384615026880558610192037)
  ·
    refine ⟨3447115317540104739411007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18384615026880558610192037 3447115317540104739411007)
    ·
      refine ⟨5170672976310157109116511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3447115317540104739411007 5170672976310157109116511)
      ·
        refine ⟨7756009464465235663674767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5170672976310157109116511 7756009464465235663674767)
        ·
          refine ⟨11634014196697853495512151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7756009464465235663674767 11634014196697853495512151)
          ·
            refine ⟨17451021295046780243268227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11634014196697853495512151 17451021295046780243268227)
            ·
              refine ⟨26176531942570170364902341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17451021295046780243268227 26176531942570170364902341)
              ·
                refine ⟨4908099739231906943419189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26176531942570170364902341 4908099739231906943419189)
                ·
                  refine ⟨460134350552991275945549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4908099739231906943419189 460134350552991275945549)
                  ·
                    refine ⟨172550381457371728479581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 460134350552991275945549 172550381457371728479581)
                    ·
                      rfl

theorem cell22_504061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 4, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 4, 5, 3].length) (baseStart_504061 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_504061 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_504061 prefixEnd_504061 := by exact prefixLift 504061
  have htrace : WordTrace (prefixWord ++ tailWord_504061) baseStart_504061 baseEnd_504061 := by
    simpa [prefixWord, tailWord_504061, baseEnd_504061] using wordTrace_append hprefix tailTrace_504061
  have hstable : (prefixWord ++ tailWord_504061).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_504061).length < 2 ^ (prefixWord ++ tailWord_504061).sum := by decide
  have hdescent : baseEnd_504061 < baseStart_504061 := by decide
  rcases family_descends (prefixWord ++ tailWord_504061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_504168 : List Nat := [2, 1, 4, 2, 2, 1, 2, 2, 1, 5]
def baseStart_504168 : Nat := 118140960795 + 504168 * 2 ^ 59
def prefixEnd_504168 : Nat := 4983230072969 + 3 ^ 40 * 504168 * 2
def baseEnd_504168 : Nat := 172587009744059116054253

theorem tailTrace_504168 : CollatzResearch.WordTrace tailWord_504168 prefixEnd_504168 172587009744059116054253 := by
  unfold tailWord_504168
  simp only [CollatzResearch.WordTrace]
  refine ⟨9194258818746457942168579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12259011758328610589558105 9194258818746457942168579)
  ·
    refine ⟨13791388228119686913252869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9194258818746457942168579 13791388228119686913252869)
    ·
      refine ⟨2585885292772441296234913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13791388228119686913252869 2585885292772441296234913)
      ·
        refine ⟨1939413969579330972176185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2585885292772441296234913 1939413969579330972176185)
        ·
          refine ⟨1454560477184498229132139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1939413969579330972176185 1454560477184498229132139)
          ·
            refine ⟨2181840715776747343698209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1454560477184498229132139 2181840715776747343698209)
            ·
              refine ⟨1636380536832560507773657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2181840715776747343698209 1636380536832560507773657)
              ·
                refine ⟨1227285402624420380830243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1636380536832560507773657 1227285402624420380830243)
                ·
                  refine ⟨1840928103936630571245365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1227285402624420380830243 1840928103936630571245365)
                  ·
                    refine ⟨172587009744059116054253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1840928103936630571245365 172587009744059116054253)
                    ·
                      rfl

theorem cell22_504168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 2, 2, 1, 5].length) (baseStart_504168 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_504168 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_504168 prefixEnd_504168 := by exact prefixLift 504168
  have htrace : WordTrace (prefixWord ++ tailWord_504168) baseStart_504168 baseEnd_504168 := by
    simpa [prefixWord, tailWord_504168, baseEnd_504168] using wordTrace_append hprefix tailTrace_504168
  have hstable : (prefixWord ++ tailWord_504168).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_504168).length < 2 ^ (prefixWord ++ tailWord_504168).sum := by decide
  have hdescent : baseEnd_504168 < baseStart_504168 := by decide
  rcases family_descends (prefixWord ++ tailWord_504168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_504170 : List Nat := [3, 1, 3, 3, 1, 1, 1, 5, 4]
def baseStart_504170 : Nat := 118140960795 + 504170 * 2 ^ 59
def prefixEnd_504170 : Nat := 4983230072969 + 3 ^ 40 * 504170 * 2
def baseEnd_504170 : Nat := 57529231461643925834749

theorem tailTrace_504170 : CollatzResearch.WordTrace tailWord_504170 prefixEnd_504170 57529231461643925834749 := by
  unfold tailWord_504170
  simp only [CollatzResearch.WordTrace]
  refine ⟨4597147645871417556477491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12259060388990446817273309 4597147645871417556477491)
  ·
    refine ⟨6895721468807126334716237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4597147645871417556477491 6895721468807126334716237)
    ·
      refine ⟨2585895550802672375518589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6895721468807126334716237 2585895550802672375518589)
      ·
        refine ⟨969710831551002140819471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2585895550802672375518589 969710831551002140819471)
        ·
          refine ⟨1454566247326503211229207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 969710831551002140819471 1454566247326503211229207)
          ·
            refine ⟨2181849370989754816843811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1454566247326503211229207 2181849370989754816843811)
            ·
              refine ⟨3272774056484632225265717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2181849370989754816843811 3272774056484632225265717)
              ·
                refine ⟨306822567795434271118661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3272774056484632225265717 306822567795434271118661)
                ·
                  refine ⟨57529231461643925834749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 306822567795434271118661 57529231461643925834749)
                  ·
                    rfl

theorem cell22_504170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 1, 5, 4].length) (baseStart_504170 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_504170 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_504170 prefixEnd_504170 := by exact prefixLift 504170
  have htrace : WordTrace (prefixWord ++ tailWord_504170) baseStart_504170 baseEnd_504170 := by
    simpa [prefixWord, tailWord_504170, baseEnd_504170] using wordTrace_append hprefix tailTrace_504170
  have hstable : (prefixWord ++ tailWord_504170).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_504170).length < 2 ^ (prefixWord ++ tailWord_504170).sum := by decide
  have hdescent : baseEnd_504170 < baseStart_504170 := by decide
  rcases family_descends (prefixWord ++ tailWord_504170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_504172 : List Nat := [2, 2, 1, 1, 6, 2, 2, 1, 1, 4]
def baseStart_504172 : Nat := 118140960795 + 504172 * 2 ^ 59
def prefixEnd_504172 : Nat := 4983230072969 + 3 ^ 40 * 504172 * 2
def baseEnd_504172 : Nat := 172588379025804438954241

theorem tailTrace_504172 : CollatzResearch.WordTrace tailWord_504172 prefixEnd_504172 172588379025804438954241 := by
  unfold tailWord_504172
  simp only [CollatzResearch.WordTrace]
  refine ⟨9194331764739212283741385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12259109019652283044988513 9194331764739212283741385)
  ·
    refine ⟨6895748823554409212806039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9194331764739212283741385 6895748823554409212806039)
    ·
      refine ⟨10343623235331613819209059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6895748823554409212806039 10343623235331613819209059)
      ·
        refine ⟨15515434852997420728813589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10343623235331613819209059 15515434852997420728813589)
        ·
          refine ⟨727286008734254096663137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 15515434852997420728813589 727286008734254096663137)
          ·
            refine ⟨545464506550690572497353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 727286008734254096663137 545464506550690572497353)
            ·
              refine ⟨409098379913017929373015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 545464506550690572497353 409098379913017929373015)
              ·
                refine ⟨613647569869526894059523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 409098379913017929373015 613647569869526894059523)
                ·
                  refine ⟨920471354804290341089285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 613647569869526894059523 920471354804290341089285)
                  ·
                    refine ⟨172588379025804438954241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 920471354804290341089285 172588379025804438954241)
                    ·
                      rfl

theorem cell22_504172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 4].length) (baseStart_504172 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_504172 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_504172 prefixEnd_504172 := by exact prefixLift 504172
  have htrace : WordTrace (prefixWord ++ tailWord_504172) baseStart_504172 baseEnd_504172 := by
    simpa [prefixWord, tailWord_504172, baseEnd_504172] using wordTrace_append hprefix tailTrace_504172
  have hstable : (prefixWord ++ tailWord_504172).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_504172).length < 2 ^ (prefixWord ++ tailWord_504172).sum := by decide
  have hdescent : baseEnd_504172 < baseStart_504172 := by decide
  rcases family_descends (prefixWord ++ tailWord_504172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_504202 : List Nat := [3, 1, 2, 5, 1, 2, 1, 1, 1, 5]
def baseStart_504202 : Nat := 118140960795 + 504202 * 2 ^ 59
def prefixEnd_504202 : Nat := 4983230072969 + 3 ^ 40 * 504202 * 2
def baseEnd_504202 : Nat := 172598648638894360704149

theorem tailTrace_504202 : CollatzResearch.WordTrace tailWord_504202 prefixEnd_504202 172598648638894360704149 := by
  unfold tailWord_504202
  simp only [CollatzResearch.WordTrace]
  refine ⟨4597439429842434922768715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12259838479579826460716573 4597439429842434922768715)
  ·
    refine ⟨6896159144763652384153073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4597439429842434922768715 6896159144763652384153073)
    ·
      refine ⟨5172119358572739288114805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6896159144763652384153073 5172119358572739288114805)
      ·
        refine ⟨484886189866194308260763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 5172119358572739288114805 484886189866194308260763)
        ·
          refine ⟨727329284799291462391145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 484886189866194308260763 727329284799291462391145)
          ·
            refine ⟨545496963599468596793359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 727329284799291462391145 545496963599468596793359)
            ·
              refine ⟨818245445399202895190039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 545496963599468596793359 818245445399202895190039)
              ·
                refine ⟨1227368168098804342785059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 818245445399202895190039 1227368168098804342785059)
                ·
                  refine ⟨1841052252148206514177589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1227368168098804342785059 1841052252148206514177589)
                  ·
                    refine ⟨172598648638894360704149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1841052252148206514177589 172598648638894360704149)
                    ·
                      rfl

theorem cell22_504202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 2, 1, 1, 1, 5].length) (baseStart_504202 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_504202 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_504202 prefixEnd_504202 := by exact prefixLift 504202
  have htrace : WordTrace (prefixWord ++ tailWord_504202) baseStart_504202 baseEnd_504202 := by
    simpa [prefixWord, tailWord_504202, baseEnd_504202] using wordTrace_append hprefix tailTrace_504202
  have hstable : (prefixWord ++ tailWord_504202).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_504202).length < 2 ^ (prefixWord ++ tailWord_504202).sum := by decide
  have hdescent : baseEnd_504202 < baseStart_504202 := by decide
  rcases family_descends (prefixWord ++ tailWord_504202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_504234 : List Nat := [3, 1, 6, 1, 1, 1, 1, 2, 2, 4]
def baseStart_504234 : Nat := 118140960795 + 504234 * 2 ^ 59
def prefixEnd_504234 : Nat := 4983230072969 + 3 ^ 40 * 504234 * 2
def baseEnd_504234 : Nat := 172609602892856943904051

theorem tailTrace_504234 : CollatzResearch.WordTrace tailWord_504234 prefixEnd_504234 172609602892856943904051 := by
  unfold tailWord_504234
  simp only [CollatzResearch.WordTrace]
  refine ⟨4597731213813452289059939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12260616570169206104159837 4597731213813452289059939)
  ·
    refine ⟨6896596820720178433589909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4597731213813452289059939 6896596820720178433589909)
    ·
      refine ⟨323277975971258364074527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 6896596820720178433589909 323277975971258364074527)
      ·
        refine ⟨484916963956887546111791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 323277975971258364074527 484916963956887546111791)
        ·
          refine ⟨727375445935331319167687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 484916963956887546111791 727375445935331319167687)
          ·
            refine ⟨1091063168902996978751531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 727375445935331319167687 1091063168902996978751531)
            ·
              refine ⟨1636594753354495468127297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1091063168902996978751531 1636594753354495468127297)
              ·
                refine ⟨1227446065015871601095473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1636594753354495468127297 1227446065015871601095473)
                ·
                  refine ⟨920584548761903700821605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1227446065015871601095473 920584548761903700821605)
                  ·
                    refine ⟨172609602892856943904051, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 920584548761903700821605 172609602892856943904051)
                    ·
                      rfl

theorem cell22_504234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 1, 1, 2, 2, 4].length) (baseStart_504234 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_504234 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_504234 prefixEnd_504234 := by exact prefixLift 504234
  have htrace : WordTrace (prefixWord ++ tailWord_504234) baseStart_504234 baseEnd_504234 := by
    simpa [prefixWord, tailWord_504234, baseEnd_504234] using wordTrace_append hprefix tailTrace_504234
  have hstable : (prefixWord ++ tailWord_504234).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_504234).length < 2 ^ (prefixWord ++ tailWord_504234).sum := by decide
  have hdescent : baseEnd_504234 < baseStart_504234 := by decide
  rcases family_descends (prefixWord ++ tailWord_504234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_504256 : List Nat := [2, 1, 1, 2, 3, 1, 1, 1, 2, 8]
def baseStart_504256 : Nat := 118140960795 + 504256 * 2 ^ 59
def prefixEnd_504256 : Nat := 4983230072969 + 3 ^ 40 * 504256 * 2
def baseEnd_504256 : Nat := 172617133942456219853983

theorem tailTrace_504256 : CollatzResearch.WordTrace tailWord_504256 prefixEnd_504256 172617133942456219853983 := by
  unfold tailWord_504256
  simp only [CollatzResearch.WordTrace]
  refine ⟨9195863630587053456770311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12261151507449404609027081 9195863630587053456770311)
  ·
    refine ⟨13793795445880580185155467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9195863630587053456770311 13793795445880580185155467)
    ·
      refine ⟨20690693168820870277733201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13793795445880580185155467 20690693168820870277733201)
      ·
        refine ⟨15518019876615652708299901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20690693168820870277733201 15518019876615652708299901)
        ·
          refine ⟨5819257453730869765612463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15518019876615652708299901 5819257453730869765612463)
          ·
            refine ⟨8728886180596304648418695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5819257453730869765612463 8728886180596304648418695)
            ·
              refine ⟨13093329270894456972628043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8728886180596304648418695 13093329270894456972628043)
              ·
                refine ⟨19639993906341685458942065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13093329270894456972628043 19639993906341685458942065)
                ·
                  refine ⟨14729995429756264094206549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19639993906341685458942065 14729995429756264094206549)
                  ·
                    refine ⟨172617133942456219853983, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 14729995429756264094206549 172617133942456219853983)
                    ·
                      rfl

theorem cell22_504256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 1, 2, 8].length) (baseStart_504256 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_504256 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_504256 prefixEnd_504256 := by exact prefixLift 504256
  have htrace : WordTrace (prefixWord ++ tailWord_504256) baseStart_504256 baseEnd_504256 := by
    simpa [prefixWord, tailWord_504256, baseEnd_504256] using wordTrace_append hprefix tailTrace_504256
  have hstable : (prefixWord ++ tailWord_504256).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_504256).length < 2 ^ (prefixWord ++ tailWord_504256).sum := by decide
  have hdescent : baseEnd_504256 < baseStart_504256 := by decide
  rcases family_descends (prefixWord ++ tailWord_504256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_504271 : List Nat := [1, 1, 2, 1, 1, 4, 1, 3, 8]
def baseStart_504271 : Nat := 118140960795 + 504271 * 2 ^ 59
def prefixEnd_504271 : Nat := 4983230072969 + 3 ^ 40 * 504271 * 2
def baseEnd_504271 : Nat := 57540756249667060242979

theorem tailTrace_504271 : CollatzResearch.WordTrace tailWord_504271 prefixEnd_504271 57540756249667060242979 := by
  unfold tailWord_504271
  simp only [CollatzResearch.WordTrace]
  refine ⟨18392274356119764475336667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12261516237413176316891111 18392274356119764475336667)
  ·
    refine ⟨27588411534179646713005001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18392274356119764475336667 27588411534179646713005001)
    ·
      refine ⟨20691308650634735034753751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27588411534179646713005001 20691308650634735034753751)
      ·
        refine ⟨31036962975952102552130627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20691308650634735034753751 31036962975952102552130627)
        ·
          refine ⟨46555444463928153828195941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31036962975952102552130627 46555444463928153828195941)
          ·
            refine ⟨8729145836986528842786739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 46555444463928153828195941 8729145836986528842786739)
            ·
              refine ⟨13093718755479793264180109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8729145836986528842786739 13093718755479793264180109)
              ·
                refine ⟨4910144533304922474067541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13093718755479793264180109 4910144533304922474067541)
                ·
                  refine ⟨57540756249667060242979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 4910144533304922474067541 57540756249667060242979)
                  ·
                    rfl

theorem cell22_504271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 3, 8].length) (baseStart_504271 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_504271 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_504271 prefixEnd_504271 := by exact prefixLift 504271
  have htrace : WordTrace (prefixWord ++ tailWord_504271) baseStart_504271 baseEnd_504271 := by
    simpa [prefixWord, tailWord_504271, baseEnd_504271] using wordTrace_append hprefix tailTrace_504271
  have hstable : (prefixWord ++ tailWord_504271).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_504271).length < 2 ^ (prefixWord ++ tailWord_504271).sum := by decide
  have hdescent : baseEnd_504271 < baseStart_504271 := by decide
  rcases family_descends (prefixWord ++ tailWord_504271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_504305 : List Nat := [1, 2, 2, 2, 3, 1, 3, 4, 4]
def baseStart_504305 : Nat := 118140960795 + 504305 * 2 ^ 59
def prefixEnd_504305 : Nat := 4983230072969 + 3 ^ 40 * 504305 * 2
def baseEnd_504305 : Nat := 57544635881278808459611

theorem tailTrace_504305 : CollatzResearch.WordTrace tailWord_504305 prefixEnd_504305 57544635881278808459611 := by
  unfold tailWord_504305
  simp only [CollatzResearch.WordTrace]
  refine ⟨18393514437996588282074369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12262342958664392188049579 18393514437996588282074369)
  ·
    refine ⟨13795135828497441211555777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18393514437996588282074369 13795135828497441211555777)
    ·
      refine ⟨10346351871373080908666833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13795135828497441211555777 10346351871373080908666833)
      ·
        refine ⟨7759763903529810681500125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10346351871373080908666833 7759763903529810681500125)
        ·
          refine ⟨2909911463823679005562547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7759763903529810681500125 2909911463823679005562547)
          ·
            refine ⟨4364867195735518508343821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2909911463823679005562547 4364867195735518508343821)
            ·
              refine ⟨1636825198400819440628933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4364867195735518508343821 1636825198400819440628933)
              ·
                refine ⟨306904724700153645117925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1636825198400819440628933 306904724700153645117925)
                ·
                  refine ⟨57544635881278808459611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 306904724700153645117925 57544635881278808459611)
                  ·
                    rfl

theorem cell22_504305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 3, 4, 4].length) (baseStart_504305 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_504305 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_504305 prefixEnd_504305 := by exact prefixLift 504305
  have htrace : WordTrace (prefixWord ++ tailWord_504305) baseStart_504305 baseEnd_504305 := by
    simpa [prefixWord, tailWord_504305, baseEnd_504305] using wordTrace_append hprefix tailTrace_504305
  have hstable : (prefixWord ++ tailWord_504305).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_504305).length < 2 ^ (prefixWord ++ tailWord_504305).sum := by decide
  have hdescent : baseEnd_504305 < baseStart_504305 := by decide
  rcases family_descends (prefixWord ++ tailWord_504305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_504322 : List Nat := [3, 4, 1, 2, 2, 1, 1, 2, 6]
def baseStart_504322 : Nat := 118140960795 + 504322 * 2 ^ 59
def prefixEnd_504322 : Nat := 4983230072969 + 3 ^ 40 * 504322 * 2
def baseEnd_504322 : Nat := 57546575697084682567927

theorem tailTrace_504322 : CollatzResearch.WordTrace tailWord_504322 prefixEnd_504322 57546575697084682567927 := by
  unfold tailWord_504322
  simp only [CollatzResearch.WordTrace]
  refine ⟨4598533619733750046360805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12262756319290000123628813 4598533619733750046360805)
  ·
    refine ⟨862225053700078133692651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4598533619733750046360805 862225053700078133692651)
    ·
      refine ⟨1293337580550117200538977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 862225053700078133692651 1293337580550117200538977)
      ·
        refine ⟨970003185412587900404233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1293337580550117200538977 970003185412587900404233)
        ·
          refine ⟨727502389059440925303175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 970003185412587900404233 727502389059440925303175)
          ·
            refine ⟨1091253583589161387954763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 727502389059440925303175 1091253583589161387954763)
            ·
              refine ⟨1636880375383742081932145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1091253583589161387954763 1636880375383742081932145)
              ·
                refine ⟨1227660281537806561449109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1636880375383742081932145 1227660281537806561449109)
                ·
                  refine ⟨57546575697084682567927, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1227660281537806561449109 57546575697084682567927)
                  ·
                    rfl

theorem cell22_504322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 1, 1, 2, 6].length) (baseStart_504322 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_504322 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_504322 prefixEnd_504322 := by exact prefixLift 504322
  have htrace : WordTrace (prefixWord ++ tailWord_504322) baseStart_504322 baseEnd_504322 := by
    simpa [prefixWord, tailWord_504322, baseEnd_504322] using wordTrace_append hprefix tailTrace_504322
  have hstable : (prefixWord ++ tailWord_504322).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_504322).length < 2 ^ (prefixWord ++ tailWord_504322).sum := by decide
  have hdescent : baseEnd_504322 < baseStart_504322 := by decide
  rcases family_descends (prefixWord ++ tailWord_504322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_504429 : List Nat := [1, 5, 1, 1, 3, 3, 2, 1, 5]
def baseStart_504429 : Nat := 118140960795 + 504429 * 2 ^ 59
def prefixEnd_504429 : Nat := 4983230072969 + 3 ^ 40 * 504429 * 2
def baseEnd_504429 : Nat := 57558785125980478426151

theorem tailTrace_504429 : CollatzResearch.WordTrace tailWord_504429 prefixEnd_504429 57558785125980478426151 := by
  unfold tailWord_504429
  simp only [CollatzResearch.WordTrace]
  refine ⟨18398037089547357459588341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12265358059698238306392227 18398037089547357459588341)
  ·
    refine ⟨1724815977145064761836407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 18398037089547357459588341 1724815977145064761836407)
    ·
      refine ⟨2587223965717597142754611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1724815977145064761836407 2587223965717597142754611)
      ·
        refine ⟨3880835948576395714131917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2587223965717597142754611 3880835948576395714131917)
        ·
          refine ⟨1455313480716148392799469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3880835948576395714131917 1455313480716148392799469)
          ·
            refine ⟨545742555268555647299801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1455313480716148392799469 545742555268555647299801)
            ·
              refine ⟨409306916451416735474851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 545742555268555647299801 409306916451416735474851)
              ·
                refine ⟨613960374677125103212277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 409306916451416735474851 613960374677125103212277)
                ·
                  refine ⟨57558785125980478426151, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 613960374677125103212277 57558785125980478426151)
                  ·
                    rfl

theorem cell22_504429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 3, 2, 1, 5].length) (baseStart_504429 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_504429 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_504429 prefixEnd_504429 := by exact prefixLift 504429
  have htrace : WordTrace (prefixWord ++ tailWord_504429) baseStart_504429 baseEnd_504429 := by
    simpa [prefixWord, tailWord_504429, baseEnd_504429] using wordTrace_append hprefix tailTrace_504429
  have hstable : (prefixWord ++ tailWord_504429).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_504429).length < 2 ^ (prefixWord ++ tailWord_504429).sum := by decide
  have hdescent : baseEnd_504429 < baseStart_504429 := by decide
  rcases family_descends (prefixWord ++ tailWord_504429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_504455 : List Nat := [1, 1, 4, 2, 1, 2, 3, 2, 1, 5]
def baseStart_504455 : Nat := 118140960795 + 504455 * 2 ^ 59
def prefixEnd_504455 : Nat := 4983230072969 + 3 ^ 40 * 504455 * 2
def baseEnd_504455 : Nat := 172685255709286034128373

theorem tailTrace_504455 : CollatzResearch.WordTrace tailWord_504455 prefixEnd_504455 172685255709286034128373 := by
  unfold tailWord_504455
  simp only [CollatzResearch.WordTrace]
  refine ⟨18398985387453163900034819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12265990258302109266689879 18398985387453163900034819)
  ·
    refine ⟨27598478081179745850052229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18398985387453163900034819 27598478081179745850052229)
    ·
      refine ⟨5174714640221202346884793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27598478081179745850052229 5174714640221202346884793)
      ·
        refine ⟨3881035980165901760163595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5174714640221202346884793 3881035980165901760163595)
        ·
          refine ⟨5821553970248852640245393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3881035980165901760163595 5821553970248852640245393)
          ·
            refine ⟨4366165477686639480184045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5821553970248852640245393 4366165477686639480184045)
            ·
              refine ⟨1637312054132489805069017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4366165477686639480184045 1637312054132489805069017)
              ·
                refine ⟨1227984040599367353801763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1637312054132489805069017 1227984040599367353801763)
                ·
                  refine ⟨1841976060899051030702645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1227984040599367353801763 1841976060899051030702645)
                  ·
                    refine ⟨172685255709286034128373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1841976060899051030702645 172685255709286034128373)
                    ·
                      rfl

theorem cell22_504455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 3, 2, 1, 5].length) (baseStart_504455 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_504455 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_504455 prefixEnd_504455 := by exact prefixLift 504455
  have htrace : WordTrace (prefixWord ++ tailWord_504455) baseStart_504455 baseEnd_504455 := by
    simpa [prefixWord, tailWord_504455, baseEnd_504455] using wordTrace_append hprefix tailTrace_504455
  have hstable : (prefixWord ++ tailWord_504455).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_504455).length < 2 ^ (prefixWord ++ tailWord_504455).sum := by decide
  have hdescent : baseEnd_504455 < baseStart_504455 := by decide
  rcases family_descends (prefixWord ++ tailWord_504455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_504620 : List Nat := [2, 2, 1, 1, 1, 4, 1, 10]
def baseStart_504620 : Nat := 118140960795 + 504620 * 2 ^ 59
def prefixEnd_504620 : Nat := 4983230072969 + 3 ^ 40 * 504620 * 2
def baseEnd_504620 : Nat := 19193526509031178194763

theorem tailTrace_504620 : CollatzResearch.WordTrace tailWord_504620 prefixEnd_504620 19193526509031178194763 := by
  unfold tailWord_504620
  simp only [CollatzResearch.WordTrace]
  refine ⟨9202501715927698539895657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12270002287903598053194209 9202501715927698539895657)
  ·
    refine ⟨6901876286945773904921743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9202501715927698539895657 6901876286945773904921743)
    ·
      refine ⟨10352814430418660857382615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6901876286945773904921743 10352814430418660857382615)
      ·
        refine ⟨15529221645627991286073923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10352814430418660857382615 15529221645627991286073923)
        ·
          refine ⟨23293832468441986929110885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15529221645627991286073923 23293832468441986929110885)
          ·
            refine ⟨4367593587832872549208291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23293832468441986929110885 4367593587832872549208291)
            ·
              refine ⟨6551390381749308823812437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4367593587832872549208291 6551390381749308823812437)
              ·
                refine ⟨19193526509031178194763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 6551390381749308823812437 19193526509031178194763)
                ·
                  rfl

theorem cell22_504620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 1, 10].length) (baseStart_504620 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_504620 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_504620 prefixEnd_504620 := by exact prefixLift 504620
  have htrace : WordTrace (prefixWord ++ tailWord_504620) baseStart_504620 baseEnd_504620 := by
    simpa [prefixWord, tailWord_504620, baseEnd_504620] using wordTrace_append hprefix tailTrace_504620
  have hstable : (prefixWord ++ tailWord_504620).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_504620).length < 2 ^ (prefixWord ++ tailWord_504620).sum := by decide
  have hdescent : baseEnd_504620 < baseStart_504620 := by decide
  rcases family_descends (prefixWord ++ tailWord_504620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_504628 : List Nat := [2, 5, 1, 1, 3, 1, 3, 1, 1, 4]
def baseStart_504628 : Nat := 118140960795 + 504628 * 2 ^ 59
def prefixEnd_504628 : Nat := 4983230072969 + 3 ^ 40 * 504628 * 2
def baseEnd_504628 : Nat := 172744477144771249552843

theorem tailTrace_504628 : CollatzResearch.WordTrace tailWord_504628 prefixEnd_504628 172744477144771249552843 := by
  unfold tailWord_504628
  simp only [CollatzResearch.WordTrace]
  refine ⟨9202647607913207223041269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12270196810550942964055025 9202647607913207223041269)
  ·
    refine ⟨862748213241863177160119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 9202647607913207223041269 862748213241863177160119)
    ·
      refine ⟨1294122319862794765740179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 862748213241863177160119 1294122319862794765740179)
      ·
        refine ⟨1941183479794192148610269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1294122319862794765740179 1941183479794192148610269)
        ·
          refine ⟨727943804922822055728851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1941183479794192148610269 727943804922822055728851)
          ·
            refine ⟨1091915707384233083593277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 727943804922822055728851 1091915707384233083593277)
            ·
              refine ⟨409468390269087406347479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1091915707384233083593277 409468390269087406347479)
              ·
                refine ⟨614202585403631109521219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 409468390269087406347479 614202585403631109521219)
                ·
                  refine ⟨921303878105446664281829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 614202585403631109521219 921303878105446664281829)
                  ·
                    refine ⟨172744477144771249552843, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 921303878105446664281829 172744477144771249552843)
                    ·
                      rfl

theorem cell22_504628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 1, 3, 1, 1, 4].length) (baseStart_504628 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_504628 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_504628 prefixEnd_504628 := by exact prefixLift 504628
  have htrace : WordTrace (prefixWord ++ tailWord_504628) baseStart_504628 baseEnd_504628 := by
    simpa [prefixWord, tailWord_504628, baseEnd_504628] using wordTrace_append hprefix tailTrace_504628
  have hstable : (prefixWord ++ tailWord_504628).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_504628).length < 2 ^ (prefixWord ++ tailWord_504628).sum := by decide
  have hdescent : baseEnd_504628 < baseStart_504628 := by decide
  rcases family_descends (prefixWord ++ tailWord_504628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_504637 : List Nat := [1, 4, 1, 4, 2, 10]
def baseStart_504637 : Nat := 118140960795 + 504637 * 2 ^ 59
def prefixEnd_504637 : Nat := 4983230072969 + 3 ^ 40 * 504637 * 2
def baseEnd_504637 : Nat := 2132685901588866988615

theorem tailTrace_504637 : CollatzResearch.WordTrace tailWord_504637 prefixEnd_504637 2132685901588866988615 := by
  unfold tailWord_504637
  simp only [CollatzResearch.WordTrace]
  refine ⟨18405623472793808983160165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12270415648529205988773443 18405623472793808983160165)
  ·
    refine ⟨3451054401148839184342531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18405623472793808983160165 3451054401148839184342531)
    ·
      refine ⟨5176581601723258776513797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3451054401148839184342531 5176581601723258776513797)
      ·
        refine ⟨970609050323111020596337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5176581601723258776513797 970609050323111020596337)
        ·
          refine ⟨727956787742333265447253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 970609050323111020596337 727956787742333265447253)
          ·
            refine ⟨2132685901588866988615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 727956787742333265447253 2132685901588866988615)
            ·
              rfl

theorem cell22_504637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 10].length) (baseStart_504637 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_504637 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_504637 prefixEnd_504637 := by exact prefixLift 504637
  have htrace : WordTrace (prefixWord ++ tailWord_504637) baseStart_504637 baseEnd_504637 := by
    simpa [prefixWord, tailWord_504637, baseEnd_504637] using wordTrace_append hprefix tailTrace_504637
  have hstable : (prefixWord ++ tailWord_504637).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_504637).length < 2 ^ (prefixWord ++ tailWord_504637).sum := by decide
  have hdescent : baseEnd_504637 < baseStart_504637 := by decide
  rcases family_descends (prefixWord ++ tailWord_504637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_504697 : List Nat := [1, 2, 1, 3, 2, 3, 1, 2, 2, 5]
def baseStart_504697 : Nat := 118140960795 + 504697 * 2 ^ 59
def prefixEnd_504697 : Nat := 4983230072969 + 3 ^ 40 * 504697 * 2
def baseEnd_504697 : Nat := 172768097254878069577631

theorem tailTrace_504697 : CollatzResearch.WordTrace tailWord_504697 prefixEnd_504697 172768097254878069577631 := by
  unfold tailWord_504697
  simp only [CollatzResearch.WordTrace]
  refine ⟨18407811852576439230344345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12271874568384292820229563 18407811852576439230344345)
  ·
    refine ⟨13805858889432329422758259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18407811852576439230344345 13805858889432329422758259)
    ·
      refine ⟨20708788334148494134137389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13805858889432329422758259 20708788334148494134137389)
      ·
        refine ⟨7765795625305685300301521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20708788334148494134137389 7765795625305685300301521)
        ·
          refine ⟨5824346718979263975226141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7765795625305685300301521 5824346718979263975226141)
          ·
            refine ⟨2184130019617223990709803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5824346718979263975226141 2184130019617223990709803)
            ·
              refine ⟨3276195029425835986064705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2184130019617223990709803 3276195029425835986064705)
              ·
                refine ⟨2457146272069376989548529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3276195029425835986064705 2457146272069376989548529)
                ·
                  refine ⟨1842859704052032742161397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2457146272069376989548529 1842859704052032742161397)
                  ·
                    refine ⟨172768097254878069577631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1842859704052032742161397 172768097254878069577631)
                    ·
                      rfl

theorem cell22_504697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 1, 2, 2, 5].length) (baseStart_504697 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_504697 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_504697 prefixEnd_504697 := by exact prefixLift 504697
  have htrace : WordTrace (prefixWord ++ tailWord_504697) baseStart_504697 baseEnd_504697 := by
    simpa [prefixWord, tailWord_504697, baseEnd_504697] using wordTrace_append hprefix tailTrace_504697
  have hstable : (prefixWord ++ tailWord_504697).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_504697).length < 2 ^ (prefixWord ++ tailWord_504697).sum := by decide
  have hdescent : baseEnd_504697 < baseStart_504697 := by decide
  rcases family_descends (prefixWord ++ tailWord_504697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_504714 : List Nat := [3, 1, 2, 4, 1, 1, 2, 1, 2, 5]
def baseStart_504714 : Nat := 118140960795 + 504714 * 2 ^ 59
def prefixEnd_504714 : Nat := 4983230072969 + 3 ^ 40 * 504714 * 2
def baseEnd_504714 : Nat := 172773916702295691902579

theorem tailTrace_504714 : CollatzResearch.WordTrace tailWord_504714 prefixEnd_504714 172773916702295691902579 := by
  unfold tailWord_504714
  simp only [CollatzResearch.WordTrace]
  refine ⟨4602107973378712783428299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12272287929009900755808797 4602107973378712783428299)
  ·
    refine ⟨6903161960068069175142449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4602107973378712783428299 6903161960068069175142449)
    ·
      refine ⟨5177371470051051881356837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6903161960068069175142449 5177371470051051881356837)
      ·
        refine ⟨970757150634572227754407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5177371470051051881356837 970757150634572227754407)
        ·
          refine ⟨1456135725951858341631611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 970757150634572227754407 1456135725951858341631611)
          ·
            refine ⟨2184203588927787512447417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1456135725951858341631611 2184203588927787512447417)
            ·
              refine ⟨1638152691695840634335563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2184203588927787512447417 1638152691695840634335563)
              ·
                refine ⟨2457229037543760951503345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1638152691695840634335563 2457229037543760951503345)
                ·
                  refine ⟨1842921778157820713627509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2457229037543760951503345 1842921778157820713627509)
                  ·
                    refine ⟨172773916702295691902579, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1842921778157820713627509 172773916702295691902579)
                    ·
                      rfl

theorem cell22_504714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 2, 1, 2, 5].length) (baseStart_504714 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_504714 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_504714 prefixEnd_504714 := by exact prefixLift 504714
  have htrace : WordTrace (prefixWord ++ tailWord_504714) baseStart_504714 baseEnd_504714 := by
    simpa [prefixWord, tailWord_504714, baseEnd_504714] using wordTrace_append hprefix tailTrace_504714
  have hstable : (prefixWord ++ tailWord_504714).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_504714).length < 2 ^ (prefixWord ++ tailWord_504714).sum := by decide
  have hdescent : baseEnd_504714 < baseStart_504714 := by decide
  rcases family_descends (prefixWord ++ tailWord_504714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_504727 : List Nat := [1, 1, 3, 3, 1, 2, 1, 4, 6]
def baseStart_504727 : Nat := 118140960795 + 504727 * 2 ^ 59
def prefixEnd_504727 : Nat := 4983230072969 + 3 ^ 40 * 504727 * 2
def baseEnd_504727 : Nat := 57592788955989330442513

theorem tailTrace_504727 : CollatzResearch.WordTrace tailWord_504727 prefixEnd_504727 57592788955989330442513 := by
  unfold tailWord_504727
  simp only [CollatzResearch.WordTrace]
  refine ⟨18408906042467754353936435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12272604028311836235957623 18408906042467754353936435)
  ·
    refine ⟨27613359063701631530904653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18408906042467754353936435 27613359063701631530904653)
    ·
      refine ⟨10355009648888111824089245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27613359063701631530904653 10355009648888111824089245)
      ·
        refine ⟨3883128618333041934033467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10355009648888111824089245 3883128618333041934033467)
        ·
          refine ⟨5824692927499562901050201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3883128618333041934033467 5824692927499562901050201)
          ·
            refine ⟨4368519695624672175787651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5824692927499562901050201 4368519695624672175787651)
            ·
              refine ⟨6552779543437008263681477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4368519695624672175787651 6552779543437008263681477)
              ·
                refine ⟨1228646164394439049440277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6552779543437008263681477 1228646164394439049440277)
                ·
                  refine ⟨57592788955989330442513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1228646164394439049440277 57592788955989330442513)
                  ·
                    rfl

theorem cell22_504727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 1, 4, 6].length) (baseStart_504727 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_504727 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_504727 prefixEnd_504727 := by exact prefixLift 504727
  have htrace : WordTrace (prefixWord ++ tailWord_504727) baseStart_504727 baseEnd_504727 := by
    simpa [prefixWord, tailWord_504727, baseEnd_504727] using wordTrace_append hprefix tailTrace_504727
  have hstable : (prefixWord ++ tailWord_504727).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_504727).length < 2 ^ (prefixWord ++ tailWord_504727).sum := by decide
  have hdescent : baseEnd_504727 < baseStart_504727 := by decide
  rcases family_descends (prefixWord ++ tailWord_504727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_504759 : List Nat := [1, 1, 3, 1, 3, 1, 4, 1, 4, 3]
def baseStart_504759 : Nat := 118140960795 + 504759 * 2 ^ 59
def prefixEnd_504759 : Nat := 4983230072969 + 3 ^ 40 * 504759 * 2
def baseEnd_504759 : Nat := 172789321121930574527441

theorem tailTrace_504759 : CollatzResearch.WordTrace tailWord_504759 prefixEnd_504759 172789321121930574527441 := by
  unfold tailWord_504759
  simp only [CollatzResearch.WordTrace]
  refine ⟨18410073178351823819101331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12273382118901215879400887 18410073178351823819101331)
  ·
    refine ⟨27615109767527735728651997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18410073178351823819101331 27615109767527735728651997)
    ·
      refine ⟨10355666162822900898244499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27615109767527735728651997 10355666162822900898244499)
      ·
        refine ⟨15533499244234351347366749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10355666162822900898244499 15533499244234351347366749)
        ·
          refine ⟨5825062216587881755262531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15533499244234351347366749 5825062216587881755262531)
          ·
            refine ⟨8737593324881822632893797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5825062216587881755262531 8737593324881822632893797)
            ·
              refine ⟨1638298748415341743667587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8737593324881822632893797 1638298748415341743667587)
              ·
                refine ⟨2457448122623012615501381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1638298748415341743667587 2457448122623012615501381)
                ·
                  refine ⟨460771522991814865406509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2457448122623012615501381 460771522991814865406509)
                  ·
                    refine ⟨172789321121930574527441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 460771522991814865406509 172789321121930574527441)
                    ·
                      rfl

theorem cell22_504759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 4, 1, 4, 3].length) (baseStart_504759 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_504759 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_504759 prefixEnd_504759 := by exact prefixLift 504759
  have htrace : WordTrace (prefixWord ++ tailWord_504759) baseStart_504759 baseEnd_504759 := by
    simpa [prefixWord, tailWord_504759, baseEnd_504759] using wordTrace_append hprefix tailTrace_504759
  have hstable : (prefixWord ++ tailWord_504759).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_504759).length < 2 ^ (prefixWord ++ tailWord_504759).sum := by decide
  have hdescent : baseEnd_504759 < baseStart_504759 := by decide
  rcases family_descends (prefixWord ++ tailWord_504759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_504804 : List Nat := [2, 3, 1, 1, 1, 1, 2, 1, 7, 3]
def baseStart_504804 : Nat := 118140960795 + 504804 * 2 ^ 59
def prefixEnd_504804 : Nat := 4983230072969 + 3 ^ 40 * 504804 * 2
def baseEnd_504804 : Nat := 172804725541565457152303

theorem tailTrace_504804 : CollatzResearch.WordTrace tailWord_504804 prefixEnd_504804 172804725541565457152303 := by
  unfold tailWord_504804
  simp only [CollatzResearch.WordTrace]
  refine ⟨9205857231594398252244733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12274476308792531002992977 9205857231594398252244733)
  ·
    refine ⟨3452196461847899344591775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9205857231594398252244733 3452196461847899344591775)
    ·
      refine ⟨5178294692771849016887663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3452196461847899344591775 5178294692771849016887663)
      ·
        refine ⟨7767442039157773525331495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5178294692771849016887663 7767442039157773525331495)
        ·
          refine ⟨11651163058736660287997243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7767442039157773525331495 11651163058736660287997243)
          ·
            refine ⟨17476744588104990431995865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11651163058736660287997243 17476744588104990431995865)
            ·
              refine ⟨13107558441078742823996899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17476744588104990431995865 13107558441078742823996899)
              ·
                refine ⟨19661337661618114235995349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13107558441078742823996899 19661337661618114235995349)
                ·
                  refine ⟨460812601444174552406141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19661337661618114235995349 460812601444174552406141)
                  ·
                    refine ⟨172804725541565457152303, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 460812601444174552406141 172804725541565457152303)
                    ·
                      rfl

theorem cell22_504804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 1, 7, 3].length) (baseStart_504804 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_504804 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_504804 prefixEnd_504804 := by exact prefixLift 504804
  have htrace : WordTrace (prefixWord ++ tailWord_504804) baseStart_504804 baseEnd_504804 := by
    simpa [prefixWord, tailWord_504804, baseEnd_504804] using wordTrace_append hprefix tailTrace_504804
  have hstable : (prefixWord ++ tailWord_504804).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_504804).length < 2 ^ (prefixWord ++ tailWord_504804).sum := by decide
  have hdescent : baseEnd_504804 < baseStart_504804 := by decide
  rcases family_descends (prefixWord ++ tailWord_504804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_504847 : List Nat := [1, 1, 2, 1, 1, 1, 2, 1, 4, 8]
def baseStart_504847 : Nat := 118140960795 + 504847 * 2 ^ 59
def prefixEnd_504847 : Nat := 4983230072969 + 3 ^ 40 * 504847 * 2
def baseEnd_504847 : Nat := 172819445320327678327171

theorem tailTrace_504847 : CollatzResearch.WordTrace tailWord_504847 prefixEnd_504847 172819445320327678327171 := by
  unfold tailWord_504847
  simp only [CollatzResearch.WordTrace]
  refine ⟨18413282802033014848304795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12275521868022009898869863 18413282802033014848304795)
  ·
    refine ⟨27619924203049522272457193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18413282802033014848304795 27619924203049522272457193)
    ·
      refine ⟨20714943152287141704342895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27619924203049522272457193 20714943152287141704342895)
      ·
        refine ⟨31072414728430712556514343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20714943152287141704342895 31072414728430712556514343)
        ·
          refine ⟨46608622092646068834771515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31072414728430712556514343 46608622092646068834771515)
          ·
            refine ⟨69912933138969103252157273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46608622092646068834771515 69912933138969103252157273)
            ·
              refine ⟨52434699854226827439117955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69912933138969103252157273 52434699854226827439117955)
              ·
                refine ⟨78652049781340241158676933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52434699854226827439117955 78652049781340241158676933)
                ·
                  refine ⟨14747259334001295217251925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 78652049781340241158676933 14747259334001295217251925)
                  ·
                    refine ⟨172819445320327678327171, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 14747259334001295217251925 172819445320327678327171)
                    ·
                      rfl

theorem cell22_504847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 1, 4, 8].length) (baseStart_504847 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_504847 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_504847 prefixEnd_504847 := by exact prefixLift 504847
  have htrace : WordTrace (prefixWord ++ tailWord_504847) baseStart_504847 baseEnd_504847 := by
    simpa [prefixWord, tailWord_504847, baseEnd_504847] using wordTrace_append hprefix tailTrace_504847
  have hstable : (prefixWord ++ tailWord_504847).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_504847).length < 2 ^ (prefixWord ++ tailWord_504847).sum := by decide
  have hdescent : baseEnd_504847 < baseStart_504847 := by decide
  rcases family_descends (prefixWord ++ tailWord_504847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_504855 : List Nat := [1, 1, 3, 5, 1, 2, 2, 3, 1, 3]
def baseStart_504855 : Nat := 118140960795 + 504855 * 2 ^ 59
def prefixEnd_504855 : Nat := 4983230072969 + 3 ^ 40 * 504855 * 2
def baseEnd_504855 : Nat := 172822183883818324127147

theorem tailTrace_504855 : CollatzResearch.WordTrace tailWord_504855 prefixEnd_504855 172822183883818324127147 := by
  unfold tailWord_504855
  simp only [CollatzResearch.WordTrace]
  refine ⟨18413574586004032214596019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12275716390669354809730679 18413574586004032214596019)
  ·
    refine ⟨27620361879006048321894029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18413574586004032214596019 27620361879006048321894029)
    ·
      refine ⟨10357635704627268120710261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27620361879006048321894029 10357635704627268120710261)
      ·
        refine ⟨971028347308806386316587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 10357635704627268120710261 971028347308806386316587)
        ·
          refine ⟨1456542520963209579474881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 971028347308806386316587 1456542520963209579474881)
          ·
            refine ⟨1092406890722407184606161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1456542520963209579474881 1092406890722407184606161)
            ·
              refine ⟨819305168041805388454621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1092406890722407184606161 819305168041805388454621)
              ·
                refine ⟨307239438015677020670483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 819305168041805388454621 307239438015677020670483)
                ·
                  refine ⟨460859157023515531005725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 307239438015677020670483 460859157023515531005725)
                  ·
                    refine ⟨172822183883818324127147, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 460859157023515531005725 172822183883818324127147)
                    ·
                      rfl

theorem cell22_504855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 2, 2, 3, 1, 3].length) (baseStart_504855 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_504855 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_504855 prefixEnd_504855 := by exact prefixLift 504855
  have htrace : WordTrace (prefixWord ++ tailWord_504855) baseStart_504855 baseEnd_504855 := by
    simpa [prefixWord, tailWord_504855, baseEnd_504855] using wordTrace_append hprefix tailTrace_504855
  have hstable : (prefixWord ++ tailWord_504855).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_504855).length < 2 ^ (prefixWord ++ tailWord_504855).sum := by decide
  have hdescent : baseEnd_504855 < baseStart_504855 := by decide
  rcases family_descends (prefixWord ++ tailWord_504855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_504868 : List Nat := [2, 3, 1, 4, 1, 3, 1, 2, 5]
def baseStart_504868 : Nat := 118140960795 + 504868 * 2 ^ 59
def prefixEnd_504868 : Nat := 4983230072969 + 3 ^ 40 * 504868 * 2
def baseEnd_504868 : Nat := 57608878016496874517369

theorem tailTrace_504868 : CollatzResearch.WordTrace tailWord_504868 prefixEnd_504868 57608878016496874517369 := by
  unfold tailWord_504868
  simp only [CollatzResearch.WordTrace]
  refine ⟨9207024367478467717409629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12276032489971290289879505 9207024367478467717409629)
  ·
    refine ⟨3452634137804425394028611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9207024367478467717409629 3452634137804425394028611)
    ·
      refine ⟨5178951206706638091042917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3452634137804425394028611 5178951206706638091042917)
      ·
        refine ⟨971053351257494642070547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5178951206706638091042917 971053351257494642070547)
        ·
          refine ⟨1456580026886241963105821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 971053351257494642070547 1456580026886241963105821)
          ·
            refine ⟨546217510082340736164683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1456580026886241963105821 546217510082340736164683)
            ·
              refine ⟨819326265123511104247025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 546217510082340736164683 819326265123511104247025)
              ·
                refine ⟨614494698842633328185269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 819326265123511104247025 614494698842633328185269)
                ·
                  refine ⟨57608878016496874517369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 614494698842633328185269 57608878016496874517369)
                  ·
                    rfl

theorem cell22_504868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 3, 1, 2, 5].length) (baseStart_504868 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_504868 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_504868 prefixEnd_504868 := by exact prefixLift 504868
  have htrace : WordTrace (prefixWord ++ tailWord_504868) baseStart_504868 baseEnd_504868 := by
    simpa [prefixWord, tailWord_504868, baseEnd_504868] using wordTrace_append hprefix tailTrace_504868
  have hstable : (prefixWord ++ tailWord_504868).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_504868).length < 2 ^ (prefixWord ++ tailWord_504868).sum := by decide
  have hdescent : baseEnd_504868 < baseStart_504868 := by decide
  rcases family_descends (prefixWord ++ tailWord_504868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_504941 : List Nat := [1, 5, 1, 1, 2, 3, 2, 7]
def baseStart_504941 : Nat := 118140960795 + 504941 * 2 ^ 59
def prefixEnd_504941 : Nat := 4983230072969 + 3 ^ 40 * 504941 * 2
def baseEnd_504941 : Nat := 19205735937926974052987

theorem tailTrace_504941 : CollatzResearch.WordTrace tailWord_504941 prefixEnd_504941 19205735937926974052987 := by
  unfold tailWord_504941
  simp only [CollatzResearch.WordTrace]
  refine ⟨18416711263692468902226677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12277807509128312601484451 18416711263692468902226677)
  ·
    refine ⟨1726566680971168959583751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 18416711263692468902226677 1726566680971168959583751)
    ·
      refine ⟨2589850021456753439375627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1726566680971168959583751 2589850021456753439375627)
      ·
        refine ⟨3884775032185130159063441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2589850021456753439375627 3884775032185130159063441)
        ·
          refine ⟨2913581274138847619297581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3884775032185130159063441 2913581274138847619297581)
          ·
            refine ⟨1092592977802067857236593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2913581274138847619297581 1092592977802067857236593)
            ·
              refine ⟨819444733351550892927445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1092592977802067857236593 819444733351550892927445)
              ·
                refine ⟨19205735937926974052987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 819444733351550892927445 19205735937926974052987)
                ·
                  rfl

theorem cell22_504941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 3, 2, 7].length) (baseStart_504941 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_504941 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_504941 prefixEnd_504941 := by exact prefixLift 504941
  have htrace : WordTrace (prefixWord ++ tailWord_504941) baseStart_504941 baseEnd_504941 := by
    simpa [prefixWord, tailWord_504941, baseEnd_504941] using wordTrace_append hprefix tailTrace_504941
  have hstable : (prefixWord ++ tailWord_504941).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_504941).length < 2 ^ (prefixWord ++ tailWord_504941).sum := by decide
  have hdescent : baseEnd_504941 < baseStart_504941 := by decide
  rcases family_descends (prefixWord ++ tailWord_504941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_504956 : List Nat := [2, 2, 2, 1, 1, 3, 2, 1, 5, 3]
def baseStart_504956 : Nat := 118140960795 + 504956 * 2 ^ 59
def prefixEnd_504956 : Nat := 4983230072969 + 3 ^ 40 * 504956 * 2
def baseEnd_504956 : Nat := 172856758247887727351837

theorem tailTrace_504956 : CollatzResearch.WordTrace tailWord_504956 prefixEnd_504956 172856758247887727351837 := by
  unfold tailWord_504956
  simp only [CollatzResearch.WordTrace]
  refine ⟨9208629179319063232011361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12278172239092084309348481 9208629179319063232011361)
  ·
    refine ⟨6906471884489297424008521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9208629179319063232011361 6906471884489297424008521)
    ·
      refine ⟨5179853913366973068006391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6906471884489297424008521 5179853913366973068006391)
      ·
        refine ⟨7769780870050459602009587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5179853913366973068006391 7769780870050459602009587)
        ·
          refine ⟨11654671305075689403014381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7769780870050459602009587 11654671305075689403014381)
          ·
            refine ⟨4370501739403383526130393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11654671305075689403014381 4370501739403383526130393)
            ·
              refine ⟨3277876304552537644597795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4370501739403383526130393 3277876304552537644597795)
              ·
                refine ⟨4916814456828806466896693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3277876304552537644597795 4916814456828806466896693)
                ·
                  refine ⟨460951355327700606271565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4916814456828806466896693 460951355327700606271565)
                  ·
                    refine ⟨172856758247887727351837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 460951355327700606271565 172856758247887727351837)
                    ·
                      rfl

theorem cell22_504956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 2, 1, 5, 3].length) (baseStart_504956 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_504956 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_504956 prefixEnd_504956 := by exact prefixLift 504956
  have htrace : WordTrace (prefixWord ++ tailWord_504956) baseStart_504956 baseEnd_504956 := by
    simpa [prefixWord, tailWord_504956, baseEnd_504956] using wordTrace_append hprefix tailTrace_504956
  have hstable : (prefixWord ++ tailWord_504956).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_504956).length < 2 ^ (prefixWord ++ tailWord_504956).sum := by decide
  have hdescent : baseEnd_504956 < baseStart_504956 := by decide
  rcases family_descends (prefixWord ++ tailWord_504956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_505048 : List Nat := [2, 1, 2, 2, 5, 1, 2, 1, 6]
def baseStart_505048 : Nat := 118140960795 + 505048 * 2 ^ 59
def prefixEnd_505048 : Nat := 4983230072969 + 3 ^ 40 * 505048 * 2
def baseEnd_505048 : Nat := 57629417242676718017185

theorem tailTrace_505048 : CollatzResearch.WordTrace tailWord_505048 prefixEnd_505048 57629417242676718017185 := by
  unfold tailWord_505048
  simp only [CollatzResearch.WordTrace]
  refine ⟨9210306937152413088185899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12280409249536550784247865 9210306937152413088185899)
  ·
    refine ⟨13815460405728619632278849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9210306937152413088185899 13815460405728619632278849)
    ·
      refine ⟨10361595304296464724209137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13815460405728619632278849 10361595304296464724209137)
      ·
        refine ⟨7771196478222348543156853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10361595304296464724209137 7771196478222348543156853)
        ·
          refine ⟨728549669833345175920955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 7771196478222348543156853 728549669833345175920955)
          ·
            refine ⟨1092824504750017763881433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 728549669833345175920955 1092824504750017763881433)
            ·
              refine ⟨819618378562513322911075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1092824504750017763881433 819618378562513322911075)
              ·
                refine ⟨1229427567843769984366613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 819618378562513322911075 1229427567843769984366613)
                ·
                  refine ⟨57629417242676718017185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1229427567843769984366613 57629417242676718017185)
                  ·
                    rfl

theorem cell22_505048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 1, 2, 1, 6].length) (baseStart_505048 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_505048 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_505048 prefixEnd_505048 := by exact prefixLift 505048
  have htrace : WordTrace (prefixWord ++ tailWord_505048) baseStart_505048 baseEnd_505048 := by
    simpa [prefixWord, tailWord_505048, baseEnd_505048] using wordTrace_append hprefix tailTrace_505048
  have hstable : (prefixWord ++ tailWord_505048).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_505048).length < 2 ^ (prefixWord ++ tailWord_505048).sum := by decide
  have hdescent : baseEnd_505048 < baseStart_505048 := by decide
  rcases family_descends (prefixWord ++ tailWord_505048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_505078 : List Nat := [5, 1, 1, 1, 1, 1, 1, 5, 2, 4]
def baseStart_505078 : Nat := 118140960795 + 505078 * 2 ^ 59
def prefixEnd_505078 : Nat := 4983230072969 + 3 ^ 40 * 505078 * 2
def baseEnd_505078 : Nat := 172898521341120075801463

theorem tailTrace_505078 : CollatzResearch.WordTrace tailWord_505078 prefixEnd_505078 172898521341120075801463 := by
  unfold tailWord_505078
  simp only [CollatzResearch.WordTrace]
  refine ⟨1151356754012258831247743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 12281138709464094199975925 1151356754012258831247743)
  ·
    refine ⟨1727035131018388246871615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1151356754012258831247743 1727035131018388246871615)
    ·
      refine ⟨2590552696527582370307423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1727035131018388246871615 2590552696527582370307423)
      ·
        refine ⟨3885829044791373555461135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2590552696527582370307423 3885829044791373555461135)
        ·
          refine ⟨5828743567187060333191703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3885829044791373555461135 5828743567187060333191703)
          ·
            refine ⟨8743115350780590499787555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5828743567187060333191703 8743115350780590499787555)
            ·
              refine ⟨13114673026170885749681333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8743115350780590499787555 13114673026170885749681333)
              ·
                refine ⟨1229500596203520539032625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13114673026170885749681333 1229500596203520539032625)
                ·
                  refine ⟨922125447152640404274469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1229500596203520539032625 922125447152640404274469)
                  ·
                    refine ⟨172898521341120075801463, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 922125447152640404274469 172898521341120075801463)
                    ·
                      rfl

theorem cell22_505078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 5, 2, 4].length) (baseStart_505078 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_505078 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_505078 prefixEnd_505078 := by exact prefixLift 505078
  have htrace : WordTrace (prefixWord ++ tailWord_505078) baseStart_505078 baseEnd_505078 := by
    simpa [prefixWord, tailWord_505078, baseEnd_505078] using wordTrace_append hprefix tailTrace_505078
  have hstable : (prefixWord ++ tailWord_505078).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_505078).length < 2 ^ (prefixWord ++ tailWord_505078).sum := by decide
  have hdescent : baseEnd_505078 < baseStart_505078 := by decide
  rcases family_descends (prefixWord ++ tailWord_505078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_505159 : List Nat := [1, 1, 4, 1, 2, 5, 2, 2, 1, 3]
def baseStart_505159 : Nat := 118140960795 + 505159 * 2 ^ 59
def prefixEnd_505159 : Nat := 4983230072969 + 3 ^ 40 * 505159 * 2
def baseEnd_505159 : Nat := 172926249296462864526215

theorem tailTrace_505159 : CollatzResearch.WordTrace tailWord_505159 prefixEnd_505159 172926249296462864526215 := by
  unfold tailWord_505159
  simp only [CollatzResearch.WordTrace]
  refine ⟨18424662376902692133662531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12283108251268461422441687 18424662376902692133662531)
  ·
    refine ⟨27636993565354038200493797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18424662376902692133662531 27636993565354038200493797)
    ·
      refine ⟨5181936293503882162592587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27636993565354038200493797 5181936293503882162592587)
      ·
        refine ⟨7772904440255823243888881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5181936293503882162592587 7772904440255823243888881)
        ·
          refine ⟨5829678330191867432916661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7772904440255823243888881 5829678330191867432916661)
          ·
            refine ⟨546532343455487571835937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 5829678330191867432916661 546532343455487571835937)
            ·
              refine ⟨409899257591615678876953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 546532343455487571835937 409899257591615678876953)
              ·
                refine ⟨307424443193711759157715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 409899257591615678876953 307424443193711759157715)
                ·
                  refine ⟨461136664790567638736573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 307424443193711759157715 461136664790567638736573)
                  ·
                    refine ⟨172926249296462864526215, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 461136664790567638736573 172926249296462864526215)
                    ·
                      rfl

theorem cell22_505159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 5, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 5, 2, 2, 1, 3].length) (baseStart_505159 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_505159 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_505159 prefixEnd_505159 := by exact prefixLift 505159
  have htrace : WordTrace (prefixWord ++ tailWord_505159) baseStart_505159 baseEnd_505159 := by
    simpa [prefixWord, tailWord_505159, baseEnd_505159] using wordTrace_append hprefix tailTrace_505159
  have hstable : (prefixWord ++ tailWord_505159).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_505159).length < 2 ^ (prefixWord ++ tailWord_505159).sum := by decide
  have hdescent : baseEnd_505159 < baseStart_505159 := by decide
  rcases family_descends (prefixWord ++ tailWord_505159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_505200 : List Nat := [2, 1, 1, 1, 4, 2, 4, 3, 4]
def baseStart_505200 : Nat := 118140960795 + 505200 * 2 ^ 59
def prefixEnd_505200 : Nat := 4983230072969 + 3 ^ 40 * 505200 * 2
def baseEnd_505200 : Nat := 57646761478117474750363

theorem tailTrace_505200 : CollatzResearch.WordTrace tailWord_505200 prefixEnd_505200 57646761478117474750363 := by
  unfold tailWord_505200
  simp only [CollatzResearch.WordTrace]
  refine ⟨9213078884877078067952527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12284105179836104090603369 9213078884877078067952527)
  ·
    refine ⟨13819618327315617101928791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9213078884877078067952527 13819618327315617101928791)
    ·
      refine ⟨20729427490973425652893187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13819618327315617101928791 20729427490973425652893187)
      ·
        refine ⟨31094141236460138479339781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20729427490973425652893187 31094141236460138479339781)
        ·
          refine ⟨5830151481836275964876209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31094141236460138479339781 5830151481836275964876209)
          ·
            refine ⟨4372613611377206973657157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5830151481836275964876209 4372613611377206973657157)
            ·
              refine ⟨819865052133226307560717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4372613611377206973657157 819865052133226307560717)
              ·
                refine ⟨307449394549959865335269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 819865052133226307560717 307449394549959865335269)
                ·
                  refine ⟨57646761478117474750363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 307449394549959865335269 57646761478117474750363)
                  ·
                    rfl

theorem cell22_505200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 4, 3, 4].length) (baseStart_505200 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_505200 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_505200 prefixEnd_505200 := by exact prefixLift 505200
  have htrace : WordTrace (prefixWord ++ tailWord_505200) baseStart_505200 baseEnd_505200 := by
    simpa [prefixWord, tailWord_505200, baseEnd_505200] using wordTrace_append hprefix tailTrace_505200
  have hstable : (prefixWord ++ tailWord_505200).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_505200).length < 2 ^ (prefixWord ++ tailWord_505200).sum := by decide
  have hdescent : baseEnd_505200 < baseStart_505200 := by decide
  rcases family_descends (prefixWord ++ tailWord_505200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_505211 : List Nat := [1, 1, 1, 1, 1, 6, 11]
def baseStart_505211 : Nat := 118140960795 + 505211 * 2 ^ 59
def prefixEnd_505211 : Nat := 4983230072969 + 3 ^ 40 * 505211 * 2
def baseEnd_505211 : Nat := 6405335183672298600965

theorem tailTrace_505211 : CollatzResearch.WordTrace tailWord_505211 prefixEnd_505211 6405335183672298600965 := by
  unfold tailWord_505211
  simp only [CollatzResearch.WordTrace]
  refine ⟨18426558972714305014555487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12284372648476203343036991 18426558972714305014555487)
  ·
    refine ⟨27639838459071457521833231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18426558972714305014555487 27639838459071457521833231)
    ·
      refine ⟨41459757688607186282749847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27639838459071457521833231 41459757688607186282749847)
      ·
        refine ⟨62189636532910779424124771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41459757688607186282749847 62189636532910779424124771)
        ·
          refine ⟨93284454799366169136187157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62189636532910779424124771 93284454799366169136187157)
          ·
            refine ⟨4372708818720289178258773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 93284454799366169136187157 4372708818720289178258773)
            ·
              refine ⟨6405335183672298600965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 4372708818720289178258773 6405335183672298600965)
              ·
                rfl

theorem cell22_505211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 11].length) (baseStart_505211 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_505211 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_505211 prefixEnd_505211 := by exact prefixLift 505211
  have htrace : WordTrace (prefixWord ++ tailWord_505211) baseStart_505211 baseEnd_505211 := by
    simpa [prefixWord, tailWord_505211, baseEnd_505211] using wordTrace_append hprefix tailTrace_505211
  have hstable : (prefixWord ++ tailWord_505211).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_505211).length < 2 ^ (prefixWord ++ tailWord_505211).sum := by decide
  have hdescent : baseEnd_505211 < baseStart_505211 := by decide
  rcases family_descends (prefixWord ++ tailWord_505211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_505213 : List Nat := [1, 4, 1, 1, 2, 2, 2, 1, 4, 4]
def baseStart_505213 : Nat := 118140960795 + 505213 * 2 ^ 59
def prefixEnd_505213 : Nat := 4983230072969 + 3 ^ 40 * 505213 * 2
def baseEnd_505213 : Nat := 172944734600024723676049

theorem tailTrace_505213 : CollatzResearch.WordTrace tailWord_505213 prefixEnd_505213 172944734600024723676049 := by
  unfold tailWord_505213
  simp only [CollatzResearch.WordTrace]
  refine ⟨18426631918707059356128293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12284421279138039570752195 18426631918707059356128293)
  ·
    refine ⟨3454993484757573629274055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18426631918707059356128293 3454993484757573629274055)
    ·
      refine ⟨5182490227136360443911083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3454993484757573629274055 5182490227136360443911083)
      ·
        refine ⟨7773735340704540665866625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5182490227136360443911083 7773735340704540665866625)
        ·
          refine ⟨5830301505528405499399969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7773735340704540665866625 5830301505528405499399969)
          ·
            refine ⟨4372726129146304124549977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5830301505528405499399969 4372726129146304124549977)
            ·
              refine ⟨3279544596859728093412483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4372726129146304124549977 3279544596859728093412483)
              ·
                refine ⟨4919316895289592140118725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3279544596859728093412483 4919316895289592140118725)
                ·
                  refine ⟨922371917866798526272261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4919316895289592140118725 922371917866798526272261)
                  ·
                    refine ⟨172944734600024723676049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 922371917866798526272261 172944734600024723676049)
                    ·
                      rfl

theorem cell22_505213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 2, 1, 4, 4].length) (baseStart_505213 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_505213 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_505213 prefixEnd_505213 := by exact prefixLift 505213
  have htrace : WordTrace (prefixWord ++ tailWord_505213) baseStart_505213 baseEnd_505213 := by
    simpa [prefixWord, tailWord_505213, baseEnd_505213] using wordTrace_append hprefix tailTrace_505213
  have hstable : (prefixWord ++ tailWord_505213).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_505213).length < 2 ^ (prefixWord ++ tailWord_505213).sum := by decide
  have hdescent : baseEnd_505213 < baseStart_505213 := by decide
  rcases family_descends (prefixWord ++ tailWord_505213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_505245 : List Nat := [1, 4, 2, 1, 3, 1, 4, 6]
def baseStart_505245 : Nat := 118140960795 + 505245 * 2 ^ 59
def prefixEnd_505245 : Nat := 4983230072969 + 3 ^ 40 * 505245 * 2
def baseEnd_505245 : Nat := 19217298761554145208439

theorem tailTrace_505245 : CollatzResearch.WordTrace tailWord_505245 prefixEnd_505245 19217298761554145208439 := by
  unfold tailWord_505245
  simp only [CollatzResearch.WordTrace]
  refine ⟨18427799054591128821293189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12285199369727419214195459 18427799054591128821293189)
  ·
    refine ⟨3455212322735836653992473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18427799054591128821293189 3455212322735836653992473)
    ·
      refine ⟨2591409242051877490494355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3455212322735836653992473 2591409242051877490494355)
      ·
        refine ⟨3887113863077816235741533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2591409242051877490494355 3887113863077816235741533)
        ·
          refine ⟨1457667698654181088403075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3887113863077816235741533 1457667698654181088403075)
          ·
            refine ⟨2186501547981271632604613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1457667698654181088403075 2186501547981271632604613)
            ·
              refine ⟨409969040246488431113365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2186501547981271632604613 409969040246488431113365)
              ·
                refine ⟨19217298761554145208439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 409969040246488431113365 19217298761554145208439)
                ·
                  rfl

theorem cell22_505245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 4, 6].length) (baseStart_505245 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_505245 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_505245 prefixEnd_505245 := by exact prefixLift 505245
  have htrace : WordTrace (prefixWord ++ tailWord_505245) baseStart_505245 baseEnd_505245 := by
    simpa [prefixWord, tailWord_505245, baseEnd_505245] using wordTrace_append hprefix tailTrace_505245
  have hstable : (prefixWord ++ tailWord_505245).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_505245).length < 2 ^ (prefixWord ++ tailWord_505245).sum := by decide
  have hdescent : baseEnd_505245 < baseStart_505245 := by decide
  rcases family_descends (prefixWord ++ tailWord_505245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_505288 : List Nat := [2, 1, 3, 1, 3, 1, 2, 1, 1, 7]
def baseStart_505288 : Nat := 118140960795 + 505288 * 2 ^ 59
def prefixEnd_505288 : Nat := 4983230072969 + 3 ^ 40 * 505288 * 2
def baseEnd_505288 : Nat := 172970408632749528050819

theorem tailTrace_505288 : CollatzResearch.WordTrace tailWord_505288 prefixEnd_505288 172970408632749528050819 := by
  unfold tailWord_505288
  simp only [CollatzResearch.WordTrace]
  refine ⟨9214683696717673582554259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12286244928956898110072345 9214683696717673582554259)
  ·
    refine ⟨13822025545076510373831389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9214683696717673582554259 13822025545076510373831389)
    ·
      refine ⟨5183259579403691390186771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13822025545076510373831389 5183259579403691390186771)
      ·
        refine ⟨7774889369105537085280157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5183259579403691390186771 7774889369105537085280157)
        ·
          refine ⟨2915583513414576406980059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7774889369105537085280157 2915583513414576406980059)
          ·
            refine ⟨4373375270121864610470089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2915583513414576406980059 4373375270121864610470089)
            ·
              refine ⟨3280031452591398457852567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4373375270121864610470089 3280031452591398457852567)
              ·
                refine ⟨4920047178887097686778851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3280031452591398457852567 4920047178887097686778851)
                ·
                  refine ⟨7380070768330646530168277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4920047178887097686778851 7380070768330646530168277)
                  ·
                    refine ⟨172970408632749528050819, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 7380070768330646530168277 172970408632749528050819)
                    ·
                      rfl

theorem cell22_505288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 2, 1, 1, 7].length) (baseStart_505288 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_505288 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_505288 prefixEnd_505288 := by exact prefixLift 505288
  have htrace : WordTrace (prefixWord ++ tailWord_505288) baseStart_505288 baseEnd_505288 := by
    simpa [prefixWord, tailWord_505288, baseEnd_505288] using wordTrace_append hprefix tailTrace_505288
  have hstable : (prefixWord ++ tailWord_505288).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_505288).length < 2 ^ (prefixWord ++ tailWord_505288).sum := by decide
  have hdescent : baseEnd_505288 < baseStart_505288 := by decide
  rcases family_descends (prefixWord ++ tailWord_505288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_505290 : List Nat := [3, 1, 2, 1, 2, 4, 1, 3, 5]
def baseStart_505290 : Nat := 118140960795 + 505290 * 2 ^ 59
def prefixEnd_505290 : Nat := 4983230072969 + 3 ^ 40 * 505290 * 2
def baseEnd_505290 : Nat := 57657031091207396500271

theorem tailTrace_505290 : CollatzResearch.WordTrace tailWord_505290 prefixEnd_505290 57657031091207396500271 := by
  unfold tailWord_505290
  simp only [CollatzResearch.WordTrace]
  refine ⟨4607360084857025376670331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12286293559618734337787549 4607360084857025376670331)
  ·
    refine ⟨6911040127285538065005497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4607360084857025376670331 6911040127285538065005497)
    ·
      refine ⟨5183280095464153548754123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6911040127285538065005497 5183280095464153548754123)
      ·
        refine ⟨7774920143196230323131185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5183280095464153548754123 7774920143196230323131185)
        ·
          refine ⟨5831190107397172742348389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7774920143196230323131185 5831190107397172742348389)
          ·
            refine ⟨1093348145136969889190323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5831190107397172742348389 1093348145136969889190323)
            ·
              refine ⟨1640022217705454833785485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1093348145136969889190323 1640022217705454833785485)
              ·
                refine ⟨615008331639545562669557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1640022217705454833785485 615008331639545562669557)
                ·
                  refine ⟨57657031091207396500271, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 615008331639545562669557 57657031091207396500271)
                  ·
                    rfl

theorem cell22_505290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 4, 1, 3, 5].length) (baseStart_505290 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_505290 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_505290 prefixEnd_505290 := by exact prefixLift 505290
  have htrace : WordTrace (prefixWord ++ tailWord_505290) baseStart_505290 baseEnd_505290 := by
    simpa [prefixWord, tailWord_505290, baseEnd_505290] using wordTrace_append hprefix tailTrace_505290
  have hstable : (prefixWord ++ tailWord_505290).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_505290).length < 2 ^ (prefixWord ++ tailWord_505290).sum := by decide
  have hdescent : baseEnd_505290 < baseStart_505290 := by decide
  rcases family_descends (prefixWord ++ tailWord_505290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_505365 : List Nat := [1, 3, 2, 1, 3, 3, 1, 1, 1, 6]
def baseStart_505365 : Nat := 118140960795 + 505365 * 2 ^ 59
def prefixEnd_505365 : Nat := 4983230072969 + 3 ^ 40 * 505365 * 2
def baseEnd_505365 : Nat := 172996767306346993875583

theorem tailTrace_505365 : CollatzResearch.WordTrace tailWord_505365 prefixEnd_505365 172996767306346993875583 := by
  unfold tailWord_505365
  simp only [CollatzResearch.WordTrace]
  refine ⟨18432175814156389315661549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12288117209437592877107699 18432175814156389315661549)
  ·
    refine ⟨6912065930308645993373081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18432175814156389315661549 6912065930308645993373081)
    ·
      refine ⟨5184049447731484495029811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6912065930308645993373081 5184049447731484495029811)
      ·
        refine ⟨7776074171597226742544717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5184049447731484495029811 7776074171597226742544717)
        ·
          refine ⟨2916027814348960028454269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7776074171597226742544717 2916027814348960028454269)
          ·
            refine ⟨1093510430380860010670351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2916027814348960028454269 1093510430380860010670351)
            ·
              refine ⟨1640265645571290016005527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1093510430380860010670351 1640265645571290016005527)
              ·
                refine ⟨2460398468356935024008291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1640265645571290016005527 2460398468356935024008291)
                ·
                  refine ⟨3690597702535402536012437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2460398468356935024008291 3690597702535402536012437)
                  ·
                    refine ⟨172996767306346993875583, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3690597702535402536012437 172996767306346993875583)
                    ·
                      rfl

theorem cell22_505365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 3, 1, 1, 1, 6].length) (baseStart_505365 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_505365 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_505365 prefixEnd_505365 := by exact prefixLift 505365
  have htrace : WordTrace (prefixWord ++ tailWord_505365) baseStart_505365 baseEnd_505365 := by
    simpa [prefixWord, tailWord_505365, baseEnd_505365] using wordTrace_append hprefix tailTrace_505365
  have hstable : (prefixWord ++ tailWord_505365).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_505365).length < 2 ^ (prefixWord ++ tailWord_505365).sum := by decide
  have hdescent : baseEnd_505365 < baseStart_505365 := by decide
  rcases family_descends (prefixWord ++ tailWord_505365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_505384 : List Nat := [2, 1, 5, 2, 2, 1, 1, 1, 4, 3]
def baseStart_505384 : Nat := 118140960795 + 505384 * 2 ^ 59
def prefixEnd_505384 : Nat := 4983230072969 + 3 ^ 40 * 505384 * 2
def baseEnd_505384 : Nat := 173003271394637277650525

theorem tailTrace_505384 : CollatzResearch.WordTrace tailWord_505384 prefixEnd_505384 173003271394637277650525 := by
  unfold tailWord_505384
  simp only [CollatzResearch.WordTrace]
  refine ⟨9216434400543777780301603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12288579200725037040402137 9216434400543777780301603)
  ·
    refine ⟨13824651600815666670452405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9216434400543777780301603 13824651600815666670452405)
    ·
      refine ⟨1296061087576468750354913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 13824651600815666670452405 1296061087576468750354913)
      ·
        refine ⟨972045815682351562766185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1296061087576468750354913 972045815682351562766185)
        ·
          refine ⟨729034361761763672074639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 972045815682351562766185 729034361761763672074639)
          ·
            refine ⟨1093551542642645508111959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 729034361761763672074639 1093551542642645508111959)
            ·
              refine ⟨1640327313963968262167939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1093551542642645508111959 1640327313963968262167939)
              ·
                refine ⟨2460490970945952393251909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1640327313963968262167939 2460490970945952393251909)
                ·
                  refine ⟨461342057052366073734733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2460490970945952393251909 461342057052366073734733)
                  ·
                    refine ⟨173003271394637277650525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 461342057052366073734733 173003271394637277650525)
                    ·
                      rfl

theorem cell22_505384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 1, 1, 1, 4, 3].length) (baseStart_505384 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_505384 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_505384 prefixEnd_505384 := by exact prefixLift 505384
  have htrace : WordTrace (prefixWord ++ tailWord_505384) baseStart_505384 baseEnd_505384 := by
    simpa [prefixWord, tailWord_505384, baseEnd_505384] using wordTrace_append hprefix tailTrace_505384
  have hstable : (prefixWord ++ tailWord_505384).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_505384).length < 2 ^ (prefixWord ++ tailWord_505384).sum := by decide
  have hdescent : baseEnd_505384 < baseStart_505384 := by decide
  rcases family_descends (prefixWord ++ tailWord_505384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_505414 : List Nat := [6, 1, 1, 1, 3, 1, 1, 8]
def baseStart_505414 : Nat := 118140960795 + 505414 * 2 ^ 59
def prefixEnd_505414 : Nat := 4983230072969 + 3 ^ 40 * 505414 * 2
def baseEnd_505414 : Nat := 19223726778636355488937

theorem tailTrace_505414 : CollatzResearch.WordTrace tailWord_505414 prefixEnd_505414 19223726778636355488937 := by
  unfold tailWord_505414
  simp only [CollatzResearch.WordTrace]
  refine ⟨576061343468089708881103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 12289308660652580456130197 576061343468089708881103)
  ·
    refine ⟨864092015202134563321655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 576061343468089708881103 864092015202134563321655)
    ·
      refine ⟨1296138022803201844982483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 864092015202134563321655 1296138022803201844982483)
      ·
        refine ⟨1944207034204802767473725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1296138022803201844982483 1944207034204802767473725)
        ·
          refine ⟨729077637826801037802647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1944207034204802767473725 729077637826801037802647)
          ·
            refine ⟨1093616456740201556703971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 729077637826801037802647 1093616456740201556703971)
            ·
              refine ⟨1640424685110302335055957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1093616456740201556703971 1640424685110302335055957)
              ·
                refine ⟨19223726778636355488937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1640424685110302335055957 19223726778636355488937)
                ·
                  rfl

theorem cell22_505414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 1, 1, 8].length) (baseStart_505414 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_505414 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_505414 prefixEnd_505414 := by exact prefixLift 505414
  have htrace : WordTrace (prefixWord ++ tailWord_505414) baseStart_505414 baseEnd_505414 := by
    simpa [prefixWord, tailWord_505414, baseEnd_505414] using wordTrace_append hprefix tailTrace_505414
  have hstable : (prefixWord ++ tailWord_505414).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_505414).length < 2 ^ (prefixWord ++ tailWord_505414).sum := by decide
  have hdescent : baseEnd_505414 < baseStart_505414 := by decide
  rcases family_descends (prefixWord ++ tailWord_505414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_505455 : List Nat := [1, 1, 2, 1, 3, 2, 1, 4, 3, 4]
def baseStart_505455 : Nat := 118140960795 + 505455 * 2 ^ 59
def prefixEnd_505455 : Nat := 4983230072969 + 3 ^ 40 * 505455 * 2
def baseEnd_505455 : Nat := 173027576145616759125307

theorem tailTrace_505455 : CollatzResearch.WordTrace tailWord_505455 prefixEnd_505455 173027576145616759125307 := by
  unfold tailWord_505455
  simp only [CollatzResearch.WordTrace]
  refine ⟨18435458383830334686437819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12290305589220223124291879 18435458383830334686437819)
  ·
    refine ⟨27653187575745502029656729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18435458383830334686437819 27653187575745502029656729)
    ·
      refine ⟨20739890681809126522242547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27653187575745502029656729 20739890681809126522242547)
      ·
        refine ⟨31109836022713689783363821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20739890681809126522242547 31109836022713689783363821)
        ·
          refine ⟨11666188508517633668761433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31109836022713689783363821 11666188508517633668761433)
          ·
            refine ⟨8749641381388225251571075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11666188508517633668761433 8749641381388225251571075)
            ·
              refine ⟨13124462072082337877356613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8749641381388225251571075 13124462072082337877356613)
              ·
                refine ⟨2460836638515438352004365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13124462072082337877356613 2460836638515438352004365)
                ·
                  refine ⟨922813739443289382001637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2460836638515438352004365 922813739443289382001637)
                  ·
                    refine ⟨173027576145616759125307, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 922813739443289382001637 173027576145616759125307)
                    ·
                      rfl

theorem cell22_505455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 4, 3, 4].length) (baseStart_505455 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_505455 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_505455 prefixEnd_505455 := by exact prefixLift 505455
  have htrace : WordTrace (prefixWord ++ tailWord_505455) baseStart_505455 baseEnd_505455 := by
    simpa [prefixWord, tailWord_505455, baseEnd_505455] using wordTrace_append hprefix tailTrace_505455
  have hstable : (prefixWord ++ tailWord_505455).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_505455).length < 2 ^ (prefixWord ++ tailWord_505455).sum := by decide
  have hdescent : baseEnd_505455 < baseStart_505455 := by decide
  rcases family_descends (prefixWord ++ tailWord_505455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_505504 : List Nat := [2, 1, 1, 4, 3, 2, 1, 4, 4]
def baseStart_505504 : Nat := 118140960795 + 505504 * 2 ^ 59
def prefixEnd_505504 : Nat := 4983230072969 + 3 ^ 40 * 505504 * 2
def baseEnd_505504 : Nat := 57681449948998988216719

theorem tailTrace_505504 : CollatzResearch.WordTrace tailWord_505504 prefixEnd_505504 57681449948998988216719 := by
  unfold tailWord_505504
  simp only [CollatzResearch.WordTrace]
  refine ⟨9218622780326408027485783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12291497040435210703314377 9218622780326408027485783)
  ·
    refine ⟨13827934170489612041228675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9218622780326408027485783 13827934170489612041228675)
    ·
      refine ⟨20741901255734418061843013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13827934170489612041228675 20741901255734418061843013)
      ·
        refine ⟨3889106485450203386595565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20741901255734418061843013 3889106485450203386595565)
        ·
          refine ⟨1458414932043826269973337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3889106485450203386595565 1458414932043826269973337)
          ·
            refine ⟨1093811199032869702480003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1458414932043826269973337 1093811199032869702480003)
            ·
              refine ⟨1640716798549304553720005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1093811199032869702480003 1640716798549304553720005)
              ·
                refine ⟨307634399727994603822501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1640716798549304553720005 307634399727994603822501)
                ·
                  refine ⟨57681449948998988216719, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 307634399727994603822501 57681449948998988216719)
                  ·
                    rfl

theorem cell22_505504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 2, 1, 4, 4].length) (baseStart_505504 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_505504 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_505504 prefixEnd_505504 := by exact prefixLift 505504
  have htrace : WordTrace (prefixWord ++ tailWord_505504) baseStart_505504 baseEnd_505504 := by
    simpa [prefixWord, tailWord_505504, baseEnd_505504] using wordTrace_append hprefix tailTrace_505504
  have hstable : (prefixWord ++ tailWord_505504).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_505504).length < 2 ^ (prefixWord ++ tailWord_505504).sum := by decide
  have hdescent : baseEnd_505504 < baseStart_505504 := by decide
  rcases family_descends (prefixWord ++ tailWord_505504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_505517 : List Nat := [1, 5, 2, 1, 1, 1, 2, 2, 1, 6]
def baseStart_505517 : Nat := 118140960795 + 505517 * 2 ^ 59
def prefixEnd_505517 : Nat := 4983230072969 + 3 ^ 40 * 505517 * 2
def baseEnd_505517 : Nat := 173048800012669264075117

theorem tailTrace_505517 : CollatzResearch.WordTrace tailWord_505517 prefixEnd_505517 173048800012669264075117 := by
  unfold tailWord_505517
  simp only [CollatzResearch.WordTrace]
  refine ⟨18437719709605719275194805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12291813139737146183463203 18437719709605719275194805)
  ·
    refine ⟨1728536222775536182049513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 18437719709605719275194805 1728536222775536182049513)
    ·
      refine ⟨1296402167081652136537135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1728536222775536182049513 1296402167081652136537135)
      ·
        refine ⟨1944603250622478204805703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1296402167081652136537135 1944603250622478204805703)
        ·
          refine ⟨2916904875933717307208555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1944603250622478204805703 2916904875933717307208555)
          ·
            refine ⟨4375357313900575960812833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2916904875933717307208555 4375357313900575960812833)
            ·
              refine ⟨3281517985425431970609625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4375357313900575960812833 3281517985425431970609625)
              ·
                refine ⟨2461138489069073977957219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3281517985425431970609625 2461138489069073977957219)
                ·
                  refine ⟨3691707733603610966935829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2461138489069073977957219 3691707733603610966935829)
                  ·
                    refine ⟨173048800012669264075117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3691707733603610966935829 173048800012669264075117)
                    ·
                      rfl

theorem cell22_505517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 2, 2, 1, 6].length) (baseStart_505517 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_505517 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_505517 prefixEnd_505517 := by exact prefixLift 505517
  have htrace : WordTrace (prefixWord ++ tailWord_505517) baseStart_505517 baseEnd_505517 := by
    simpa [prefixWord, tailWord_505517, baseEnd_505517] using wordTrace_append hprefix tailTrace_505517
  have hstable : (prefixWord ++ tailWord_505517).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_505517).length < 2 ^ (prefixWord ++ tailWord_505517).sum := by decide
  have hdescent : baseEnd_505517 < baseStart_505517 := by decide
  rcases family_descends (prefixWord ++ tailWord_505517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_505534 : List Nat := [4, 2, 1, 1, 2, 2, 3, 1, 2, 4]
def baseStart_505534 : Nat := 118140960795 + 505534 * 2 ^ 59
def prefixEnd_505534 : Nat := 4983230072969 + 3 ^ 40 * 505534 * 2
def baseEnd_505534 : Nat := 173054619460086886400065

theorem tailTrace_505534 : CollatzResearch.WordTrace tailWord_505534 prefixEnd_505534 173054619460086886400065 := by
  unfold tailWord_505534
  simp only [CollatzResearch.WordTrace]
  refine ⟨2304792468818016397320457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12292226500362754119042437 2304792468818016397320457)
  ·
    refine ⟨1728594351613512297990343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2304792468818016397320457 1728594351613512297990343)
    ·
      refine ⟨2592891527420268446985515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1728594351613512297990343 2592891527420268446985515)
      ·
        refine ⟨3889337291130402670478273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2592891527420268446985515 3889337291130402670478273)
        ·
          refine ⟨2917002968347802002858705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3889337291130402670478273 2917002968347802002858705)
          ·
            refine ⟨2187752226260851502144029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2917002968347802002858705 2187752226260851502144029)
            ·
              refine ⟨820407084847819313304011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2187752226260851502144029 820407084847819313304011)
              ·
                refine ⟨1230610627271728969956017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 820407084847819313304011 1230610627271728969956017)
                ·
                  refine ⟨922957970453796727467013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1230610627271728969956017 922957970453796727467013)
                  ·
                    refine ⟨173054619460086886400065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 922957970453796727467013 173054619460086886400065)
                    ·
                      rfl

theorem cell22_505534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 3, 1, 2, 4].length) (baseStart_505534 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_505534 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_505534 prefixEnd_505534 := by exact prefixLift 505534
  have htrace : WordTrace (prefixWord ++ tailWord_505534) baseStart_505534 baseEnd_505534 := by
    simpa [prefixWord, tailWord_505534, baseEnd_505534] using wordTrace_append hprefix tailTrace_505534
  have hstable : (prefixWord ++ tailWord_505534).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_505534).length < 2 ^ (prefixWord ++ tailWord_505534).sum := by decide
  have hdescent : baseEnd_505534 < baseStart_505534 := by decide
  rcases family_descends (prefixWord ++ tailWord_505534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_505549 : List Nat := [1, 6, 2, 1, 1, 2, 9]
def baseStart_505549 : Nat := 118140960795 + 505549 * 2 ^ 59
def prefixEnd_505549 : Nat := 4983230072969 + 3 ^ 40 * 505549 * 2
def baseEnd_505549 : Nat := 6409620528393772121297

theorem tailTrace_505549 : CollatzResearch.WordTrace tailWord_505549 prefixEnd_505549 6409620528393772121297 := by
  unfold tailWord_505549
  simp only [CollatzResearch.WordTrace]
  refine ⟨18438886845489788740359701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12292591230326525826906467 18438886845489788740359701)
  ·
    refine ⟨864322820882333847204361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 18438886845489788740359701 864322820882333847204361)
    ·
      refine ⟨648242115661750385403271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 864322820882333847204361 648242115661750385403271)
      ·
        refine ⟨972363173492625578104907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 648242115661750385403271 972363173492625578104907)
        ·
          refine ⟨1458544760238938367157361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 972363173492625578104907 1458544760238938367157361)
          ·
            refine ⟨1093908570179203775368021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1458544760238938367157361 1093908570179203775368021)
            ·
              refine ⟨6409620528393772121297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1093908570179203775368021 6409620528393772121297)
              ·
                rfl

theorem cell22_505549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 2, 9].length) (baseStart_505549 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_505549 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_505549 prefixEnd_505549 := by exact prefixLift 505549
  have htrace : WordTrace (prefixWord ++ tailWord_505549) baseStart_505549 baseEnd_505549 := by
    simpa [prefixWord, tailWord_505549, baseEnd_505549] using wordTrace_append hprefix tailTrace_505549
  have hstable : (prefixWord ++ tailWord_505549).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_505549).length < 2 ^ (prefixWord ++ tailWord_505549).sum := by decide
  have hdescent : baseEnd_505549 < baseStart_505549 := by decide
  rcases family_descends (prefixWord ++ tailWord_505549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_505684 : List Nat := [2, 4, 1, 1, 3, 1, 3, 7]
def baseStart_505684 : Nat := 118140960795 + 505684 * 2 ^ 59
def prefixEnd_505684 : Nat := 4983230072969 + 3 ^ 40 * 505684 * 2
def baseEnd_505684 : Nat := 19233996391726277238845

theorem tailTrace_505684 : CollatzResearch.WordTrace tailWord_505684 prefixEnd_505684 19233996391726277238845 := by
  unfold tailWord_505684
  simp only [CollatzResearch.WordTrace]
  refine ⟨9221905350000353398262053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12295873800000471197682737 9221905350000353398262053)
  ·
    refine ⟨1729107253125066262174135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9221905350000353398262053 1729107253125066262174135)
    ·
      refine ⟨2593660879687599393261203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1729107253125066262174135 2593660879687599393261203)
      ·
        refine ⟨3890491319531399089891805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2593660879687599393261203 3890491319531399089891805)
        ·
          refine ⟨1458934244824274658709427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3890491319531399089891805 1458934244824274658709427)
          ·
            refine ⟨2188401367236411988064141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1458934244824274658709427 2188401367236411988064141)
            ·
              refine ⟨820650512713654495524053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2188401367236411988064141 820650512713654495524053)
              ·
                refine ⟨19233996391726277238845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 820650512713654495524053 19233996391726277238845)
                ·
                  rfl

theorem cell22_505684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 3, 7].length) (baseStart_505684 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_505684 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_505684 prefixEnd_505684 := by exact prefixLift 505684
  have htrace : WordTrace (prefixWord ++ tailWord_505684) baseStart_505684 baseEnd_505684 := by
    simpa [prefixWord, tailWord_505684, baseEnd_505684] using wordTrace_append hprefix tailTrace_505684
  have hstable : (prefixWord ++ tailWord_505684).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_505684).length < 2 ^ (prefixWord ++ tailWord_505684).sum := by decide
  have hdescent : baseEnd_505684 < baseStart_505684 := by decide
  rcases family_descends (prefixWord ++ tailWord_505684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_505697 : List Nat := [1, 2, 3, 1, 1, 1, 3, 2, 2, 6]
def baseStart_505697 : Nat := 118140960795 + 505697 * 2 ^ 59
def prefixEnd_505697 : Nat := 4983230072969 + 3 ^ 40 * 505697 * 2
def baseEnd_505697 : Nat := 173110417691208794574565

theorem tailTrace_505697 : CollatzResearch.WordTrace tailWord_505697 prefixEnd_505697 173110417691208794574565 := by
  unfold tailWord_505697
  simp only [CollatzResearch.WordTrace]
  refine ⟨18444284848953610016747345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12296189899302406677831563 18444284848953610016747345)
  ·
    refine ⟨13833213636715207512560509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18444284848953610016747345 13833213636715207512560509)
    ·
      refine ⟨5187455113768202817210191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13833213636715207512560509 5187455113768202817210191)
      ·
        refine ⟨7781182670652304225815287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5187455113768202817210191 7781182670652304225815287)
        ·
          refine ⟨11671774005978456338722931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7781182670652304225815287 11671774005978456338722931)
          ·
            refine ⟨17507661008967684508084397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11671774005978456338722931 17507661008967684508084397)
            ·
              refine ⟨6565372878362881690531649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17507661008967684508084397 6565372878362881690531649)
              ·
                refine ⟨4924029658772161267898737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6565372878362881690531649 4924029658772161267898737)
                ·
                  refine ⟨3693022244079120950924053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4924029658772161267898737 3693022244079120950924053)
                  ·
                    refine ⟨173110417691208794574565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3693022244079120950924053 173110417691208794574565)
                    ·
                      rfl

theorem cell22_505697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 3, 2, 2, 6].length) (baseStart_505697 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_505697 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_505697 prefixEnd_505697 := by exact prefixLift 505697
  have htrace : WordTrace (prefixWord ++ tailWord_505697) baseStart_505697 baseEnd_505697 := by
    simpa [prefixWord, tailWord_505697, baseEnd_505697] using wordTrace_append hprefix tailTrace_505697
  have hstable : (prefixWord ++ tailWord_505697).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_505697).length < 2 ^ (prefixWord ++ tailWord_505697).sum := by decide
  have hdescent : baseEnd_505697 < baseStart_505697 := by decide
  rcases family_descends (prefixWord ++ tailWord_505697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_505712 : List Nat := [2, 1, 1, 1, 4, 1, 1, 4, 7]
def baseStart_505712 : Nat := 118140960795 + 505712 * 2 ^ 59
def prefixEnd_505712 : Nat := 4983230072969 + 3 ^ 40 * 505712 * 2
def baseEnd_505712 : Nat := 57705184165917918483173

theorem tailTrace_505712 : CollatzResearch.WordTrace tailWord_505712 prefixEnd_505712 57705184165917918483173 := by
  unfold tailWord_505712
  simp only [CollatzResearch.WordTrace]
  refine ⟨9222415971949633789271695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12296554629266178385695593 9222415971949633789271695)
  ·
    refine ⟨13833623957924450683907543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9222415971949633789271695 13833623957924450683907543)
    ·
      refine ⟨20750435936886676025861315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13833623957924450683907543 20750435936886676025861315)
      ·
        refine ⟨31125653905330014038791973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20750435936886676025861315 31125653905330014038791973)
        ·
          refine ⟨5836060107249377632273495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31125653905330014038791973 5836060107249377632273495)
          ·
            refine ⟨8754090160874066448410243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5836060107249377632273495 8754090160874066448410243)
            ·
              refine ⟨13131135241311099672615365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8754090160874066448410243 13131135241311099672615365)
              ·
                refine ⟨2462087857745831188615381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13131135241311099672615365 2462087857745831188615381)
                ·
                  refine ⟨57705184165917918483173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2462087857745831188615381 57705184165917918483173)
                  ·
                    rfl

theorem cell22_505712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 4, 7].length) (baseStart_505712 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_505712 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_505712 prefixEnd_505712 := by exact prefixLift 505712
  have htrace : WordTrace (prefixWord ++ tailWord_505712) baseStart_505712 baseEnd_505712 := by
    simpa [prefixWord, tailWord_505712, baseEnd_505712] using wordTrace_append hprefix tailTrace_505712
  have hstable : (prefixWord ++ tailWord_505712).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_505712).length < 2 ^ (prefixWord ++ tailWord_505712).sum := by decide
  have hdescent : baseEnd_505712 < baseStart_505712 := by decide
  rcases family_descends (prefixWord ++ tailWord_505712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_505810 : List Nat := [3, 2, 2, 3, 2, 2, 1, 2, 1, 4]
def baseStart_505810 : Nat := 118140960795 + 505810 * 2 ^ 59
def prefixEnd_505810 : Nat := 4983230072969 + 3 ^ 40 * 505810 * 2
def baseEnd_505810 : Nat := 173149099900514166499219

theorem tailTrace_505810 : CollatzResearch.WordTrace tailWord_505810 prefixEnd_505810 173149099900514166499219 := by
  unfold tailWord_505810
  simp only [CollatzResearch.WordTrace]
  refine ⟨4612101574386057578902721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12298937531696153543740589 4612101574386057578902721)
  ·
    refine ⟨3459076180789543184177041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4612101574386057578902721 3459076180789543184177041)
    ·
      refine ⟨2594307135592157388132781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3459076180789543184177041 2594307135592157388132781)
      ·
        refine ⟨972865175847059020549793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2594307135592157388132781 972865175847059020549793)
        ·
          refine ⟨729648881885294265412345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 972865175847059020549793 729648881885294265412345)
          ·
            refine ⟨547236661413970699059259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 729648881885294265412345 547236661413970699059259)
            ·
              refine ⟨820854992120956048588889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 547236661413970699059259 820854992120956048588889)
              ·
                refine ⟨615641244090717036441667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 820854992120956048588889 615641244090717036441667)
                ·
                  refine ⟨923461866136075554662501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 615641244090717036441667 923461866136075554662501)
                  ·
                    refine ⟨173149099900514166499219, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 923461866136075554662501 173149099900514166499219)
                    ·
                      rfl

theorem cell22_505810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 2, 1, 2, 1, 4].length) (baseStart_505810 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_505810 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_505810 prefixEnd_505810 := by exact prefixLift 505810
  have htrace : WordTrace (prefixWord ++ tailWord_505810) baseStart_505810 baseEnd_505810 := by
    simpa [prefixWord, tailWord_505810, baseEnd_505810] using wordTrace_append hprefix tailTrace_505810
  have hstable : (prefixWord ++ tailWord_505810).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_505810).length < 2 ^ (prefixWord ++ tailWord_505810).sum := by decide
  have hdescent : baseEnd_505810 < baseStart_505810 := by decide
  rcases family_descends (prefixWord ++ tailWord_505810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_505849 : List Nat := [1, 2, 1, 3, 1, 4, 1, 1, 2, 6]
def baseStart_505849 : Nat := 118140960795 + 505849 * 2 ^ 59
def prefixEnd_505849 : Nat := 4983230072969 + 3 ^ 40 * 505849 * 2
def baseEnd_505849 : Nat := 173162450397531064774099

theorem tailTrace_505849 : CollatzResearch.WordTrace tailWord_505849 prefixEnd_505849 173162450397531064774099 := by
  unfold tailWord_505849
  simp only [CollatzResearch.WordTrace]
  refine ⟨18449828744402939976280601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12299885829601959984187067 18449828744402939976280601)
  ·
    refine ⟨13837371558302204982210451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18449828744402939976280601 13837371558302204982210451)
    ·
      refine ⟨20756057337453307473315677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13837371558302204982210451 20756057337453307473315677)
      ·
        refine ⟨7783521501544990302493379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20756057337453307473315677 7783521501544990302493379)
        ·
          refine ⟨11675282252317485453740069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7783521501544990302493379 11675282252317485453740069)
          ·
            refine ⟨2189115422309528522576263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11675282252317485453740069 2189115422309528522576263)
            ·
              refine ⟨3283673133464292783864395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2189115422309528522576263 3283673133464292783864395)
              ·
                refine ⟨4925509700196439175796593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3283673133464292783864395 4925509700196439175796593)
                ·
                  refine ⟨3694132275147329381847445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4925509700196439175796593 3694132275147329381847445)
                  ·
                    refine ⟨173162450397531064774099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3694132275147329381847445 173162450397531064774099)
                    ·
                      rfl

theorem cell22_505849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 1, 1, 2, 6].length) (baseStart_505849 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_505849 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_505849 prefixEnd_505849 := by exact prefixLift 505849
  have htrace : WordTrace (prefixWord ++ tailWord_505849) baseStart_505849 baseEnd_505849 := by
    simpa [prefixWord, tailWord_505849, baseEnd_505849] using wordTrace_append hprefix tailTrace_505849
  have hstable : (prefixWord ++ tailWord_505849).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_505849).length < 2 ^ (prefixWord ++ tailWord_505849).sum := by decide
  have hdescent : baseEnd_505849 < baseStart_505849 := by decide
  rcases family_descends (prefixWord ++ tailWord_505849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_505885 : List Nat := [1, 4, 2, 2, 2, 1, 1, 5, 1, 3]
def baseStart_505885 : Nat := 118140960795 + 505885 * 2 ^ 59
def prefixEnd_505885 : Nat := 4983230072969 + 3 ^ 40 * 505885 * 2
def baseEnd_505885 : Nat := 173174773933238970873989

theorem tailTrace_505885 : CollatzResearch.WordTrace tailWord_505885 prefixEnd_505885 173174773933238970873989 := by
  unfold tailWord_505885
  simp only [CollatzResearch.WordTrace]
  refine ⟨18451141772272518124591109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12300761181515012083060739 18451141772272518124591109)
  ·
    refine ⟨3459589082301097148360833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18451141772272518124591109 3459589082301097148360833)
    ·
      refine ⟨2594691811725822861270625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3459589082301097148360833 2594691811725822861270625)
      ·
        refine ⟨1946018858794367145952969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2594691811725822861270625 1946018858794367145952969)
        ·
          refine ⟨1459514144095775359464727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1946018858794367145952969 1459514144095775359464727)
          ·
            refine ⟨2189271216143663039197091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1459514144095775359464727 2189271216143663039197091)
            ·
              refine ⟨3283906824215494558795637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2189271216143663039197091 3283906824215494558795637)
              ·
                refine ⟨307866264770202614887091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3283906824215494558795637 307866264770202614887091)
                ·
                  refine ⟨461799397155303922330637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 307866264770202614887091 461799397155303922330637)
                  ·
                    refine ⟨173174773933238970873989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 461799397155303922330637 173174773933238970873989)
                    ·
                      rfl

theorem cell22_505885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 1, 5, 1, 3].length) (baseStart_505885 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_505885 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_505885 prefixEnd_505885 := by exact prefixLift 505885
  have htrace : WordTrace (prefixWord ++ tailWord_505885) baseStart_505885 baseEnd_505885 := by
    simpa [prefixWord, tailWord_505885, baseEnd_505885] using wordTrace_append hprefix tailTrace_505885
  have hstable : (prefixWord ++ tailWord_505885).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_505885).length < 2 ^ (prefixWord ++ tailWord_505885).sum := by decide
  have hdescent : baseEnd_505885 < baseStart_505885 := by decide
  rcases family_descends (prefixWord ++ tailWord_505885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_505898 : List Nat := [3, 1, 4, 1, 2, 1, 3, 2, 5]
def baseStart_505898 : Nat := 118140960795 + 505898 * 2 ^ 59
def prefixEnd_505898 : Nat := 4983230072969 + 3 ^ 40 * 505898 * 2
def baseEnd_505898 : Nat := 57726408032970423432983

theorem tailTrace_505898 : CollatzResearch.WordTrace tailWord_505898 prefixEnd_505898 57726408032970423432983 := by
  unfold tailWord_505898
  simp only [CollatzResearch.WordTrace]
  refine ⟨4612903980306355336203587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12301077280816947563209565 4612903980306355336203587)
  ·
    refine ⟨6919355970459533004305381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4612903980306355336203587 6919355970459533004305381)
    ·
      refine ⟨1297379244461162438307259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6919355970459533004305381 1297379244461162438307259)
      ·
        refine ⟨1946068866691743657460889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1297379244461162438307259 1946068866691743657460889)
        ·
          refine ⟨1459551650018807743095667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1946068866691743657460889 1459551650018807743095667)
          ·
            refine ⟨2189327475028211614643501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1459551650018807743095667 2189327475028211614643501)
            ·
              refine ⟨820997803135579355491313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2189327475028211614643501 820997803135579355491313)
              ·
                refine ⟨615748352351684516618485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 820997803135579355491313 615748352351684516618485)
                ·
                  refine ⟨57726408032970423432983, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 615748352351684516618485 57726408032970423432983)
                  ·
                    rfl

theorem cell22_505898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 3, 2, 5].length) (baseStart_505898 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_505898 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_505898 prefixEnd_505898 := by exact prefixLift 505898
  have htrace : WordTrace (prefixWord ++ tailWord_505898) baseStart_505898 baseEnd_505898 := by
    simpa [prefixWord, tailWord_505898, baseEnd_505898] using wordTrace_append hprefix tailTrace_505898
  have hstable : (prefixWord ++ tailWord_505898).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_505898).length < 2 ^ (prefixWord ++ tailWord_505898).sum := by decide
  have hdescent : baseEnd_505898 < baseStart_505898 := by decide
  rcases family_descends (prefixWord ++ tailWord_505898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_505939 : List Nat := [1, 1, 1, 2, 1, 1, 2, 2, 5, 6]
def baseStart_505939 : Nat := 118140960795 + 505939 * 2 ^ 59
def prefixEnd_505939 : Nat := 4983230072969 + 3 ^ 40 * 505939 * 2
def baseEnd_505939 : Nat := 173193259236800830023823

theorem tailTrace_505939 : CollatzResearch.WordTrace tailWord_505939 prefixEnd_505939 173193259236800830023823 := by
  unfold tailWord_505939
  simp only [CollatzResearch.WordTrace]
  refine ⟨18453111314076885347056871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12302074209384590231371247 18453111314076885347056871)
  ·
    refine ⟨27679666971115328020585307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18453111314076885347056871 27679666971115328020585307)
    ·
      refine ⟨41519500456672992030877961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27679666971115328020585307 41519500456672992030877961)
      ·
        refine ⟨31139625342504744023158471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41519500456672992030877961 31139625342504744023158471)
        ·
          refine ⟨46709438013757116034737707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31139625342504744023158471 46709438013757116034737707)
          ·
            refine ⟨70064157020635674052106561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46709438013757116034737707 70064157020635674052106561)
            ·
              refine ⟨52548117765476755539079921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70064157020635674052106561 52548117765476755539079921)
              ·
                refine ⟨39411088324107566654309941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52548117765476755539079921 39411088324107566654309941)
                ·
                  refine ⟨3694789530385084373841557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 39411088324107566654309941 3694789530385084373841557)
                  ·
                    refine ⟨173193259236800830023823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3694789530385084373841557 173193259236800830023823)
                    ·
                      rfl

theorem cell22_505939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 2, 5, 6].length) (baseStart_505939 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_505939 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_505939 prefixEnd_505939 := by exact prefixLift 505939
  have htrace : WordTrace (prefixWord ++ tailWord_505939) baseStart_505939 baseEnd_505939 := by
    simpa [prefixWord, tailWord_505939, baseEnd_505939] using wordTrace_append hprefix tailTrace_505939
  have hstable : (prefixWord ++ tailWord_505939).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_505939).length < 2 ^ (prefixWord ++ tailWord_505939).sum := by decide
  have hdescent : baseEnd_505939 < baseStart_505939 := by decide
  rcases family_descends (prefixWord ++ tailWord_505939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_505943 : List Nat := [1, 1, 3, 2, 2, 1, 5, 3, 4]
def baseStart_505943 : Nat := 118140960795 + 505943 * 2 ^ 59
def prefixEnd_505943 : Nat := 4983230072969 + 3 ^ 40 * 505943 * 2
def baseEnd_505943 : Nat := 57731542839515384307937

theorem tailTrace_505943 : CollatzResearch.WordTrace tailWord_505943 prefixEnd_505943 57731542839515384307937 := by
  unfold tailWord_505943
  simp only [CollatzResearch.WordTrace]
  refine ⟨18453257206062394030202483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12302171470708262686801655 18453257206062394030202483)
  ·
    refine ⟨27679885809093591045303725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18453257206062394030202483 27679885809093591045303725)
    ·
      refine ⟨10379957178410096641988897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27679885809093591045303725 10379957178410096641988897)
      ·
        refine ⟨7784967883807572481491673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10379957178410096641988897 7784967883807572481491673)
        ·
          refine ⟨5838725912855679361118755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7784967883807572481491673 5838725912855679361118755)
          ·
            refine ⟨8758088869283519041678133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5838725912855679361118755 8758088869283519041678133)
            ·
              refine ⟨821070831495329910157325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8758088869283519041678133 821070831495329910157325)
              ·
                refine ⟨307901561810748716308997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 821070831495329910157325 307901561810748716308997)
                ·
                  refine ⟨57731542839515384307937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 307901561810748716308997 57731542839515384307937)
                  ·
                    rfl

theorem cell22_505943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 5, 3, 4].length) (baseStart_505943 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_505943 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_505943 prefixEnd_505943 := by exact prefixLift 505943
  have htrace : WordTrace (prefixWord ++ tailWord_505943) baseStart_505943 baseEnd_505943 := by
    simpa [prefixWord, tailWord_505943, baseEnd_505943] using wordTrace_append hprefix tailTrace_505943
  have hstable : (prefixWord ++ tailWord_505943).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_505943).length < 2 ^ (prefixWord ++ tailWord_505943).sum := by decide
  have hdescent : baseEnd_505943 < baseStart_505943 := by decide
  rcases family_descends (prefixWord ++ tailWord_505943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_505956 : List Nat := [2, 3, 1, 1, 2, 1, 3, 1, 4, 4]
def baseStart_505956 : Nat := 118140960795 + 505956 * 2 ^ 59
def prefixEnd_505956 : Nat := 4983230072969 + 3 ^ 40 * 505956 * 2
def baseEnd_505956 : Nat := 173199078684218452348771

theorem tailTrace_505956 : CollatzResearch.WordTrace tailWord_505956 prefixEnd_505956 173199078684218452348771 := by
  unfold tailWord_505956
  simp only [CollatzResearch.WordTrace]
  refine ⟨9226865677507648625212861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12302487570010198166950481 9226865677507648625212861)
  ·
    refine ⟨3460074629065368234454823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9226865677507648625212861 3460074629065368234454823)
    ·
      refine ⟨5190111943598052351682235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3460074629065368234454823 5190111943598052351682235)
      ·
        refine ⟨7785167915397078527523353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5190111943598052351682235 7785167915397078527523353)
        ·
          refine ⟨5838875936547808895642515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7785167915397078527523353 5838875936547808895642515)
          ·
            refine ⟨8758313904821713343463773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5838875936547808895642515 8758313904821713343463773)
            ·
              refine ⟨3284367714308142503798915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8758313904821713343463773 3284367714308142503798915)
              ·
                refine ⟨4926551571462213755698373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3284367714308142503798915 4926551571462213755698373)
                ·
                  refine ⟨923728419649165079193445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4926551571462213755698373 923728419649165079193445)
                  ·
                    refine ⟨173199078684218452348771, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 923728419649165079193445 173199078684218452348771)
                    ·
                      rfl

theorem cell22_505956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 3, 1, 4, 4].length) (baseStart_505956 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_505956 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_505956 prefixEnd_505956 := by exact prefixLift 505956
  have htrace : WordTrace (prefixWord ++ tailWord_505956) baseStart_505956 baseEnd_505956 := by
    simpa [prefixWord, tailWord_505956, baseEnd_505956] using wordTrace_append hprefix tailTrace_505956
  have hstable : (prefixWord ++ tailWord_505956).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_505956).length < 2 ^ (prefixWord ++ tailWord_505956).sum := by decide
  have hdescent : baseEnd_505956 < baseStart_505956 := by decide
  rcases family_descends (prefixWord ++ tailWord_505956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_505975 : List Nat := [1, 1, 3, 1, 1, 5, 4, 1, 2, 3]
def baseStart_505975 : Nat := 118140960795 + 505975 * 2 ^ 59
def prefixEnd_505975 : Nat := 4983230072969 + 3 ^ 40 * 505975 * 2
def baseEnd_505975 : Nat := 173205582772508736123713

theorem tailTrace_505975 : CollatzResearch.WordTrace tailWord_505975 prefixEnd_505975 173205582772508736123713 := by
  unfold tailWord_505975
  simp only [CollatzResearch.WordTrace]
  refine ⟨18454424341946463495367379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12302949561297642330244919 18454424341946463495367379)
  ·
    refine ⟨27681636512919695243051069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18454424341946463495367379 27681636512919695243051069)
    ·
      refine ⟨10380613692344885716144151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27681636512919695243051069 10380613692344885716144151)
      ·
        refine ⟨15570920538517328574216227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10380613692344885716144151 15570920538517328574216227)
        ·
          refine ⟨23356380807775992861324341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15570920538517328574216227 23356380807775992861324341)
          ·
            refine ⟨2189660700728999330749157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 23356380807775992861324341 2189660700728999330749157)
            ·
              refine ⟨410561381386687374515467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2189660700728999330749157 410561381386687374515467)
              ·
                refine ⟨615842072080031061773201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 410561381386687374515467 615842072080031061773201)
                ·
                  refine ⟨461881554060023296329901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 615842072080031061773201 461881554060023296329901)
                  ·
                    refine ⟨173205582772508736123713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 461881554060023296329901 173205582772508736123713)
                    ·
                      rfl

theorem cell22_505975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 4, 1, 2, 3].length) (baseStart_505975 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_505975 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_505975 prefixEnd_505975 := by exact prefixLift 505975
  have htrace : WordTrace (prefixWord ++ tailWord_505975) baseStart_505975 baseEnd_505975 := by
    simpa [prefixWord, tailWord_505975, baseEnd_505975] using wordTrace_append hprefix tailTrace_505975
  have hstable : (prefixWord ++ tailWord_505975).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_505975).length < 2 ^ (prefixWord ++ tailWord_505975).sum := by decide
  have hdescent : baseEnd_505975 < baseStart_505975 := by decide
  rcases family_descends (prefixWord ++ tailWord_505975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_506018 : List Nat := [3, 3, 1, 3, 1, 1, 1, 1, 2, 6]
def baseStart_506018 : Nat := 118140960795 + 506018 * 2 ^ 59
def prefixEnd_506018 : Nat := 4983230072969 + 3 ^ 40 * 506018 * 2
def baseEnd_506018 : Nat := 173220302551270957298581

theorem tailTrace_506018 : CollatzResearch.WordTrace tailWord_506018 prefixEnd_506018 173220302551270957298581 := by
  unfold tailWord_506018
  simp only [CollatzResearch.WordTrace]
  refine ⟨4613998170197670459795677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12303995120527121226121805 4613998170197670459795677)
  ·
    refine ⟨1730249313824126422423379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4613998170197670459795677 1730249313824126422423379)
    ·
      refine ⟨2595373970736189633635069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1730249313824126422423379 2595373970736189633635069)
      ·
        refine ⟨973265239026071112613151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2595373970736189633635069 973265239026071112613151)
        ·
          refine ⟨1459897858539106668919727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 973265239026071112613151 1459897858539106668919727)
          ·
            refine ⟨2189846787808660003379591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1459897858539106668919727 2189846787808660003379591)
            ·
              refine ⟨3284770181712990005069387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2189846787808660003379591 3284770181712990005069387)
              ·
                refine ⟨4927155272569485007604081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3284770181712990005069387 4927155272569485007604081)
                ·
                  refine ⟨3695366454427113755703061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4927155272569485007604081 3695366454427113755703061)
                  ·
                    refine ⟨173220302551270957298581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3695366454427113755703061 173220302551270957298581)
                    ·
                      rfl

theorem cell22_506018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 1, 1, 2, 6].length) (baseStart_506018 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_506018 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_506018 prefixEnd_506018 := by exact prefixLift 506018
  have htrace : WordTrace (prefixWord ++ tailWord_506018) baseStart_506018 baseEnd_506018 := by
    simpa [prefixWord, tailWord_506018, baseEnd_506018] using wordTrace_append hprefix tailTrace_506018
  have hstable : (prefixWord ++ tailWord_506018).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_506018).length < 2 ^ (prefixWord ++ tailWord_506018).sum := by decide
  have hdescent : baseEnd_506018 < baseStart_506018 := by decide
  rcases family_descends (prefixWord ++ tailWord_506018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_506037 : List Nat := [1, 3, 3, 4, 1, 1, 1, 2, 3, 3]
def baseStart_506037 : Nat := 118140960795 + 506037 * 2 ^ 59
def prefixEnd_506037 : Nat := 4983230072969 + 3 ^ 40 * 506037 * 2
def baseEnd_506037 : Nat := 173226806639561241073523

theorem tailTrace_506037 : CollatzResearch.WordTrace tailWord_506037 prefixEnd_506037 173226806639561241073523 := by
  unfold tailWord_506037
  simp only [CollatzResearch.WordTrace]
  refine ⟨18456685667721848084124365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12304457111814565389416243 18456685667721848084124365)
  ·
    refine ⟨6921257125395693031546637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18456685667721848084124365 6921257125395693031546637)
    ·
      refine ⟨2595471422023384886829989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6921257125395693031546637 2595471422023384886829989)
      ·
        refine ⟨486650891629384666280623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2595471422023384886829989 486650891629384666280623)
        ·
          refine ⟨729976337444076999420935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 486650891629384666280623 729976337444076999420935)
          ·
            refine ⟨1094964506166115499131403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 729976337444076999420935 1094964506166115499131403)
            ·
              refine ⟨1642446759249173248697105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1094964506166115499131403 1642446759249173248697105)
              ·
                refine ⟨1231835069436879936522829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1642446759249173248697105 1231835069436879936522829)
                ·
                  refine ⟨461938151038829976196061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1231835069436879936522829 461938151038829976196061)
                  ·
                    refine ⟨173226806639561241073523, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 461938151038829976196061 173226806639561241073523)
                    ·
                      rfl

theorem cell22_506037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 1, 1, 2, 3, 3].length) (baseStart_506037 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_506037 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_506037 prefixEnd_506037 := by exact prefixLift 506037
  have htrace : WordTrace (prefixWord ++ tailWord_506037) baseStart_506037 baseEnd_506037 := by
    simpa [prefixWord, tailWord_506037, baseEnd_506037] using wordTrace_append hprefix tailTrace_506037
  have hstable : (prefixWord ++ tailWord_506037).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_506037).length < 2 ^ (prefixWord ++ tailWord_506037).sum := by decide
  have hdescent : baseEnd_506037 < baseStart_506037 := by decide
  rcases family_descends (prefixWord ++ tailWord_506037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_506063 : List Nat := [1, 1, 2, 1, 1, 3, 5, 3, 1, 4]
def baseStart_506063 : Nat := 118140960795 + 506063 * 2 ^ 59
def prefixEnd_506063 : Nat := 4983230072969 + 3 ^ 40 * 506063 * 2
def baseEnd_506063 : Nat := 173235706970905839923443

theorem tailTrace_506063 : CollatzResearch.WordTrace tailWord_506063 prefixEnd_506063 173235706970905839923443 := by
  unfold tailWord_506063
  simp only [CollatzResearch.WordTrace]
  refine ⟨18457633965627654524570843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12305089310418436349713895 18457633965627654524570843)
  ·
    refine ⟨27686450948441481786856265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18457633965627654524570843 27686450948441481786856265)
    ·
      refine ⟨20764838211331111340142199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27686450948441481786856265 20764838211331111340142199)
      ·
        refine ⟨31147257316996667010213299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20764838211331111340142199 31147257316996667010213299)
        ·
          refine ⟨46720885975495000515319949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31147257316996667010213299 46720885975495000515319949)
          ·
            refine ⟨17520332240810625193244981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46720885975495000515319949 17520332240810625193244981)
            ·
              refine ⟨1642531147575996111866717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 17520332240810625193244981 1642531147575996111866717)
              ·
                refine ⟨615949180340998541950019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1642531147575996111866717 615949180340998541950019)
                ·
                  refine ⟨923923770511497812925029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 615949180340998541950019 923923770511497812925029)
                  ·
                    refine ⟨173235706970905839923443, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 923923770511497812925029 173235706970905839923443)
                    ·
                      rfl

theorem cell22_506063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 5, 3, 1, 4].length) (baseStart_506063 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_506063 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_506063 prefixEnd_506063 := by exact prefixLift 506063
  have htrace : WordTrace (prefixWord ++ tailWord_506063) baseStart_506063 baseEnd_506063 := by
    simpa [prefixWord, tailWord_506063, baseEnd_506063] using wordTrace_append hprefix tailTrace_506063
  have hstable : (prefixWord ++ tailWord_506063).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_506063).length < 2 ^ (prefixWord ++ tailWord_506063).sum := by decide
  have hdescent : baseEnd_506063 < baseStart_506063 := by decide
  rcases family_descends (prefixWord ++ tailWord_506063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_506091 : List Nat := [1, 1, 1, 1, 2, 5, 1, 1, 3, 6]
def baseStart_506091 : Nat := 118140960795 + 506091 * 2 ^ 59
def prefixEnd_506091 : Nat := 4983230072969 + 3 ^ 40 * 506091 * 2
def baseEnd_506091 : Nat := 173245291943123100223357

theorem tailTrace_506091 : CollatzResearch.WordTrace tailWord_506091 prefixEnd_506091 173245291943123100223357 := by
  unfold tailWord_506091
  simp only [CollatzResearch.WordTrace]
  refine ⟨18458655209526215306590127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12305770139684143537726751 18458655209526215306590127)
  ·
    refine ⟨27687982814289322959885191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18458655209526215306590127 27687982814289322959885191)
    ·
      refine ⟨41531974221433984439827787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27687982814289322959885191 41531974221433984439827787)
      ·
        refine ⟨62297961332150976659741681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41531974221433984439827787 62297961332150976659741681)
        ·
          refine ⟨46723470999113232494806261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62297961332150976659741681 46723470999113232494806261)
          ·
            refine ⟨4380325406166865546388087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 46723470999113232494806261 4380325406166865546388087)
            ·
              refine ⟨6570488109250298319582131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4380325406166865546388087 6570488109250298319582131)
              ·
                refine ⟨9855732163875447479373197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6570488109250298319582131 9855732163875447479373197)
                ·
                  refine ⟨3695899561453292804764949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9855732163875447479373197 3695899561453292804764949)
                  ·
                    refine ⟨173245291943123100223357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3695899561453292804764949 173245291943123100223357)
                    ·
                      rfl

theorem cell22_506091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 1, 1, 3, 6].length) (baseStart_506091 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_506091 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_506091 prefixEnd_506091 := by exact prefixLift 506091
  have htrace : WordTrace (prefixWord ++ tailWord_506091) baseStart_506091 baseEnd_506091 := by
    simpa [prefixWord, tailWord_506091, baseEnd_506091] using wordTrace_append hprefix tailTrace_506091
  have hstable : (prefixWord ++ tailWord_506091).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_506091).length < 2 ^ (prefixWord ++ tailWord_506091).sum := by decide
  have hdescent : baseEnd_506091 < baseStart_506091 := by decide
  rcases family_descends (prefixWord ++ tailWord_506091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_506108 : List Nat := [2, 2, 2, 1, 4, 1, 2, 1, 1, 6]
def baseStart_506108 : Nat := 118140960795 + 506108 * 2 ^ 59
def prefixEnd_506108 : Nat := 4983230072969 + 3 ^ 40 * 506108 * 2
def baseEnd_506108 : Nat := 173251111390540722548305

theorem tailTrace_506108 : CollatzResearch.WordTrace tailWord_506108 prefixEnd_506108 173251111390540722548305 := by
  unfold tailWord_506108
  simp only [CollatzResearch.WordTrace]
  refine ⟨9229637625232313604979489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12306183500309751473305985 9229637625232313604979489)
  ·
    refine ⟨6922228218924235203734617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9229637625232313604979489 6922228218924235203734617)
    ·
      refine ⟨5191671164193176402800963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6922228218924235203734617 5191671164193176402800963)
      ·
        refine ⟨7787506746289764604201445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5191671164193176402800963 7787506746289764604201445)
        ·
          refine ⟨1460157514929330863287771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7787506746289764604201445 1460157514929330863287771)
          ·
            refine ⟨2190236272393996294931657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1460157514929330863287771 2190236272393996294931657)
            ·
              refine ⟨1642677204295497221198743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2190236272393996294931657 1642677204295497221198743)
              ·
                refine ⟨2464015806443245831798115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1642677204295497221198743 2464015806443245831798115)
                ·
                  refine ⟨3696023709664868747697173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2464015806443245831798115 3696023709664868747697173)
                  ·
                    refine ⟨173251111390540722548305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3696023709664868747697173 173251111390540722548305)
                    ·
                      rfl

theorem cell22_506108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 2, 1, 1, 6].length) (baseStart_506108 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_506108 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_506108 prefixEnd_506108 := by exact prefixLift 506108
  have htrace : WordTrace (prefixWord ++ tailWord_506108) baseStart_506108 baseEnd_506108 := by
    simpa [prefixWord, tailWord_506108, baseEnd_506108] using wordTrace_append hprefix tailTrace_506108
  have hstable : (prefixWord ++ tailWord_506108).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_506108).length < 2 ^ (prefixWord ++ tailWord_506108).sum := by decide
  have hdescent : baseEnd_506108 < baseStart_506108 := by decide
  rcases family_descends (prefixWord ++ tailWord_506108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_506110 : List Nat := [4, 2, 2, 1, 1, 1, 1, 1, 6, 3]
def baseStart_506110 : Nat := 118140960795 + 506110 * 2 ^ 59
def prefixEnd_506110 : Nat := 4983230072969 + 3 ^ 40 * 506110 * 2
def baseEnd_506110 : Nat := 173251796031413383998299

theorem tailTrace_506110 : CollatzResearch.WordTrace tailWord_506110 prefixEnd_506110 173251796031413383998299 := by
  unfold tailWord_506110
  simp only [CollatzResearch.WordTrace]
  refine ⟨2307418524557172693941473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12306232130971587701021189 2307418524557172693941473)
  ·
    refine ⟨1730563893417879520456105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2307418524557172693941473 1730563893417879520456105)
    ·
      refine ⟨1297922920063409640342079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1730563893417879520456105 1297922920063409640342079)
      ·
        refine ⟨1946884380095114460513119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1297922920063409640342079 1946884380095114460513119)
        ·
          refine ⟨2920326570142671690769679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1946884380095114460513119 2920326570142671690769679)
          ·
            refine ⟨4380489855214007536154519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2920326570142671690769679 4380489855214007536154519)
            ·
              refine ⟨6570734782821011304231779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4380489855214007536154519 6570734782821011304231779)
              ·
                refine ⟨9856102174231516956347669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6570734782821011304231779 9856102174231516956347669)
                ·
                  refine ⟨462004789417102357328797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9856102174231516956347669 462004789417102357328797)
                  ·
                    refine ⟨173251796031413383998299, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 462004789417102357328797 173251796031413383998299)
                    ·
                      rfl

theorem cell22_506110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 1, 1, 6, 3].length) (baseStart_506110 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_506110 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_506110 prefixEnd_506110 := by exact prefixLift 506110
  have htrace : WordTrace (prefixWord ++ tailWord_506110) baseStart_506110 baseEnd_506110 := by
    simpa [prefixWord, tailWord_506110, baseEnd_506110] using wordTrace_append hprefix tailTrace_506110
  have hstable : (prefixWord ++ tailWord_506110).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_506110).length < 2 ^ (prefixWord ++ tailWord_506110).sum := by decide
  have hdescent : baseEnd_506110 < baseStart_506110 := by decide
  rcases family_descends (prefixWord ++ tailWord_506110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_506144 : List Nat := [2, 1, 1, 5, 2, 3, 2, 1, 2, 3]
def baseStart_506144 : Nat := 118140960795 + 506144 * 2 ^ 59
def prefixEnd_506144 : Nat := 4983230072969 + 3 ^ 40 * 506144 * 2
def baseEnd_506144 : Nat := 173263434926248628648195

theorem tailTrace_506144 : CollatzResearch.WordTrace tailWord_506144 prefixEnd_506144 173263434926248628648195 := by
  unfold tailWord_506144
  simp only [CollatzResearch.WordTrace]
  refine ⟨9230294139167102679134743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12307058852222803572179657 9230294139167102679134743)
  ·
    refine ⟨13845441208750654018702115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9230294139167102679134743 13845441208750654018702115)
    ·
      refine ⟨20768161813125981028053173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13845441208750654018702115 20768161813125981028053173)
      ·
        refine ⟨1947015169980560721379985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 20768161813125981028053173 1947015169980560721379985)
        ·
          refine ⟨1460261377485420541034989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1947015169980560721379985 1460261377485420541034989)
          ·
            refine ⟨547598016557032702888121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1460261377485420541034989 547598016557032702888121)
            ·
              refine ⟨410698512417774527166091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 547598016557032702888121 410698512417774527166091)
              ·
                refine ⟨616047768626661790749137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 410698512417774527166091 616047768626661790749137)
                ·
                  refine ⟨462035826469996343061853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 616047768626661790749137 462035826469996343061853)
                  ·
                    refine ⟨173263434926248628648195, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 462035826469996343061853 173263434926248628648195)
                    ·
                      rfl

theorem cell22_506144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 3, 2, 1, 2, 3].length) (baseStart_506144 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_506144 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_506144 prefixEnd_506144 := by exact prefixLift 506144
  have htrace : WordTrace (prefixWord ++ tailWord_506144) baseStart_506144 baseEnd_506144 := by
    simpa [prefixWord, tailWord_506144, baseEnd_506144] using wordTrace_append hprefix tailTrace_506144
  have hstable : (prefixWord ++ tailWord_506144).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_506144).length < 2 ^ (prefixWord ++ tailWord_506144).sum := by decide
  have hdescent : baseEnd_506144 < baseStart_506144 := by decide
  rcases family_descends (prefixWord ++ tailWord_506144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_506172 : List Nat := [2, 2, 2, 2, 1, 2, 2, 5, 1, 3]
def baseStart_506172 : Nat := 118140960795 + 506172 * 2 ^ 59
def prefixEnd_506172 : Nat := 4983230072969 + 3 ^ 40 * 506172 * 2
def baseEnd_506172 : Nat := 173273019898465888948109

theorem tailTrace_506172 : CollatzResearch.WordTrace tailWord_506172 prefixEnd_506172 173273019898465888948109 := by
  unfold tailWord_506172
  simp only [CollatzResearch.WordTrace]
  refine ⟨9230804761116383070144385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12307739681488510760192513 9230804761116383070144385)
  ·
    refine ⟨6923103570837287302608289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9230804761116383070144385 6923103570837287302608289)
    ·
      refine ⟨5192327678127965476956217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6923103570837287302608289 5192327678127965476956217)
      ·
        refine ⟨3894245758595974107717163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5192327678127965476956217 3894245758595974107717163)
        ·
          refine ⟨5841368637893961161575745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3894245758595974107717163 5841368637893961161575745)
          ·
            refine ⟨4381026478420470871181809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5841368637893961161575745 4381026478420470871181809)
            ·
              refine ⟨3285769858815353153386357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4381026478420470871181809 3285769858815353153386357)
              ·
                refine ⟨308040924263939358129971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3285769858815353153386357 308040924263939358129971)
                ·
                  refine ⟨462061386395909037194957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 308040924263939358129971 462061386395909037194957)
                  ·
                    refine ⟨173273019898465888948109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 462061386395909037194957 173273019898465888948109)
                    ·
                      rfl

theorem cell22_506172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 2, 5, 1, 3].length) (baseStart_506172 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_506172 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_506172 prefixEnd_506172 := by exact prefixLift 506172
  have htrace : WordTrace (prefixWord ++ tailWord_506172) baseStart_506172 baseEnd_506172 := by
    simpa [prefixWord, tailWord_506172, baseEnd_506172] using wordTrace_append hprefix tailTrace_506172
  have hstable : (prefixWord ++ tailWord_506172).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_506172).length < 2 ^ (prefixWord ++ tailWord_506172).sum := by decide
  have hdescent : baseEnd_506172 < baseStart_506172 := by decide
  rcases family_descends (prefixWord ++ tailWord_506172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_506183 : List Nat := [1, 1, 4, 1, 2, 2, 2, 2, 2, 5]
def baseStart_506183 : Nat := 118140960795 + 506183 * 2 ^ 59
def prefixEnd_506183 : Nat := 4983230072969 + 3 ^ 40 * 506183 * 2
def baseEnd_506183 : Nat := 173276785423265526923075

theorem tailTrace_506183 : CollatzResearch.WordTrace tailWord_506183 prefixEnd_506183 173276785423265526923075 := by
  unfold tailWord_506183
  simp only [CollatzResearch.WordTrace]
  refine ⟨18462010725192915018939203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12308007150128610012626135 18462010725192915018939203)
  ·
    refine ⟨27693016087789372528408805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18462010725192915018939203 27693016087789372528408805)
    ·
      refine ⟨5192440516460507349076651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27693016087789372528408805 5192440516460507349076651)
      ·
        refine ⟨7788660774690761023614977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5192440516460507349076651 7788660774690761023614977)
        ·
          refine ⟨5841495581018070767711233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7788660774690761023614977 5841495581018070767711233)
          ·
            refine ⟨4381121685763553075783425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5841495581018070767711233 4381121685763553075783425)
            ·
              refine ⟨3285841264322664806837569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4381121685763553075783425 3285841264322664806837569)
              ·
                refine ⟨2464380948241998605128177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3285841264322664806837569 2464380948241998605128177)
                ·
                  refine ⟨1848285711181498953846133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2464380948241998605128177 1848285711181498953846133)
                  ·
                    refine ⟨173276785423265526923075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1848285711181498953846133 173276785423265526923075)
                    ·
                      rfl

theorem cell22_506183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 2, 2, 2, 5].length) (baseStart_506183 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_506183 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_506183 prefixEnd_506183 := by exact prefixLift 506183
  have htrace : WordTrace (prefixWord ++ tailWord_506183) baseStart_506183 baseEnd_506183 := by
    simpa [prefixWord, tailWord_506183, baseEnd_506183] using wordTrace_append hprefix tailTrace_506183
  have hstable : (prefixWord ++ tailWord_506183).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_506183).length < 2 ^ (prefixWord ++ tailWord_506183).sum := by decide
  have hdescent : baseEnd_506183 < baseStart_506183 := by decide
  rcases family_descends (prefixWord ++ tailWord_506183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_506213 : List Nat := [1, 3, 1, 3, 1, 3, 1, 1, 8]
def baseStart_506213 : Nat := 118140960795 + 506213 * 2 ^ 59
def prefixEnd_506213 : Nat := 4983230072969 + 3 ^ 40 * 506213 * 2
def baseEnd_506213 : Nat := 57762351678785149557661

theorem tailTrace_506213 : CollatzResearch.WordTrace tailWord_506213 prefixEnd_506213 57762351678785149557661 := by
  unfold tailWord_506213
  simp only [CollatzResearch.WordTrace]
  refine ⟨18463104915084230142531293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12308736610056153428354195 18463104915084230142531293)
  ·
    refine ⟨6923664343156586303449235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18463104915084230142531293 6923664343156586303449235)
    ·
      refine ⟨10385496514734879455173853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6923664343156586303449235 10385496514734879455173853)
      ·
        refine ⟨3894561193025579795690195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10385496514734879455173853 3894561193025579795690195)
        ·
          refine ⟨5841841789538369693535293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3894561193025579795690195 5841841789538369693535293)
          ·
            refine ⟨2190690671076888635075735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5841841789538369693535293 2190690671076888635075735)
            ·
              refine ⟨3286036006615332952613603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2190690671076888635075735 3286036006615332952613603)
              ·
                refine ⟨4929054009922999428920405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3286036006615332952613603 4929054009922999428920405)
                ·
                  refine ⟨57762351678785149557661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 4929054009922999428920405 57762351678785149557661)
                  ·
                    rfl

theorem cell22_506213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 1, 1, 8].length) (baseStart_506213 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_506213 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_506213 prefixEnd_506213 := by exact prefixLift 506213
  have htrace : WordTrace (prefixWord ++ tailWord_506213) baseStart_506213 baseEnd_506213 := by
    simpa [prefixWord, tailWord_506213, baseEnd_506213] using wordTrace_append hprefix tailTrace_506213
  have hstable : (prefixWord ++ tailWord_506213).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_506213).length < 2 ^ (prefixWord ++ tailWord_506213).sum := by decide
  have hdescent : baseEnd_506213 < baseStart_506213 := by decide
  rcases family_descends (prefixWord ++ tailWord_506213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_506215 : List Nat := [1, 1, 5, 1, 3, 1, 2, 1, 3, 4]
def baseStart_506215 : Nat := 118140960795 + 506215 * 2 ^ 59
def prefixEnd_506215 : Nat := 4983230072969 + 3 ^ 40 * 506215 * 2
def baseEnd_506215 : Nat := 173287739677228110122977

theorem tailTrace_506215 : CollatzResearch.WordTrace tailWord_506215 prefixEnd_506215 173287739677228110122977 := by
  unfold tailWord_506215
  simp only [CollatzResearch.WordTrace]
  refine ⟨18463177861076984484104099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12308785240717989656069399 18463177861076984484104099)
  ·
    refine ⟨27694766791615476726156149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18463177861076984484104099 27694766791615476726156149)
    ·
      refine ⟨2596384386713950943077139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 27694766791615476726156149 2596384386713950943077139)
      ·
        refine ⟨3894576580070926414615709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2596384386713950943077139 3894576580070926414615709)
        ·
          refine ⟨1460466217526597405480891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3894576580070926414615709 1460466217526597405480891)
          ·
            refine ⟨2190699326289896108221337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1460466217526597405480891 2190699326289896108221337)
            ·
              refine ⟨1643024494717422081166003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2190699326289896108221337 1643024494717422081166003)
              ·
                refine ⟨2464536742076133121749005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1643024494717422081166003 2464536742076133121749005)
                ·
                  refine ⟨924201278278549920655877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2464536742076133121749005 924201278278549920655877)
                  ·
                    refine ⟨173287739677228110122977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 924201278278549920655877 173287739677228110122977)
                    ·
                      rfl

theorem cell22_506215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 2, 1, 3, 4].length) (baseStart_506215 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_506215 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_506215 prefixEnd_506215 := by exact prefixLift 506215
  have htrace : WordTrace (prefixWord ++ tailWord_506215) baseStart_506215 baseEnd_506215 := by
    simpa [prefixWord, tailWord_506215, baseEnd_506215] using wordTrace_append hprefix tailTrace_506215
  have hstable : (prefixWord ++ tailWord_506215).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_506215).length < 2 ^ (prefixWord ++ tailWord_506215).sum := by decide
  have hdescent : baseEnd_506215 < baseStart_506215 := by decide
  rcases family_descends (prefixWord ++ tailWord_506215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_506275 : List Nat := [1, 1, 1, 4, 1, 4, 4, 6]
def baseStart_506275 : Nat := 118140960795 + 506275 * 2 ^ 59
def prefixEnd_506275 : Nat := 4983230072969 + 3 ^ 40 * 506275 * 2
def baseEnd_506275 : Nat := 19256475433711994846977

theorem tailTrace_506275 : CollatzResearch.WordTrace tailWord_506275 prefixEnd_506275 19256475433711994846977 := by
  unfold tailWord_506275
  simp only [CollatzResearch.WordTrace]
  refine ⟨18465366240859614731288279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12310244160573076487525519 18465366240859614731288279)
  ·
    refine ⟨27698049361289422096932419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18465366240859614731288279 27698049361289422096932419)
    ·
      refine ⟨41547074041934133145398629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27698049361289422096932419 41547074041934133145398629)
      ·
        refine ⟨7790076382862649964762243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41547074041934133145398629 7790076382862649964762243)
        ·
          refine ⟨11685114574293974947143365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7790076382862649964762243 11685114574293974947143365)
          ·
            refine ⟨2190958982680120302589381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11685114574293974947143365 2190958982680120302589381)
            ·
              refine ⟨410804809252522556735509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2190958982680120302589381 410804809252522556735509)
              ·
                refine ⟨19256475433711994846977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 410804809252522556735509 19256475433711994846977)
                ·
                  rfl

theorem cell22_506275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 4, 6].length) (baseStart_506275 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_506275 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_506275 prefixEnd_506275 := by exact prefixLift 506275
  have htrace : WordTrace (prefixWord ++ tailWord_506275) baseStart_506275 baseEnd_506275 := by
    simpa [prefixWord, tailWord_506275, baseEnd_506275] using wordTrace_append hprefix tailTrace_506275
  have hstable : (prefixWord ++ tailWord_506275).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_506275).length < 2 ^ (prefixWord ++ tailWord_506275).sum := by decide
  have hdescent : baseEnd_506275 < baseStart_506275 := by decide
  rcases family_descends (prefixWord ++ tailWord_506275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_506354 : List Nat := [3, 2, 1, 4, 2, 1, 2, 2, 5]
def baseStart_506354 : Nat := 118140960795 + 506354 * 2 ^ 59
def prefixEnd_506354 : Nat := 4983230072969 + 3 ^ 40 * 506354 * 2
def baseEnd_506354 : Nat := 57778440739292693632517

theorem tailTrace_506354 : CollatzResearch.WordTrace tailWord_506354 prefixEnd_506354 57778440739292693632517 := by
  unfold tailWord_506354
  simp only [CollatzResearch.WordTrace]
  refine ⟨4617061901893352805853529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12312165071715607482276077 4617061901893352805853529)
  ·
    refine ⟨3462796426420014604390147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4617061901893352805853529 3462796426420014604390147)
    ·
      refine ⟨5194194639630021906585221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3462796426420014604390147 5194194639630021906585221)
      ·
        refine ⟨973911494930629107484729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5194194639630021906585221 973911494930629107484729)
        ·
          refine ⟨730433621197971830613547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 973911494930629107484729 730433621197971830613547)
          ·
            refine ⟨1095650431796957745920321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 730433621197971830613547 1095650431796957745920321)
            ·
              refine ⟨821737823847718309440241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1095650431796957745920321 821737823847718309440241)
              ·
                refine ⟨616303367885788732080181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 821737823847718309440241 616303367885788732080181)
                ·
                  refine ⟨57778440739292693632517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 616303367885788732080181 57778440739292693632517)
                  ·
                    rfl

theorem cell22_506354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 1, 2, 2, 5].length) (baseStart_506354 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_506354 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_506354 prefixEnd_506354 := by exact prefixLift 506354
  have htrace : WordTrace (prefixWord ++ tailWord_506354) baseStart_506354 baseEnd_506354 := by
    simpa [prefixWord, tailWord_506354, baseEnd_506354] using wordTrace_append hprefix tailTrace_506354
  have hstable : (prefixWord ++ tailWord_506354).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_506354).length < 2 ^ (prefixWord ++ tailWord_506354).sum := by decide
  have hdescent : baseEnd_506354 < baseStart_506354 := by decide
  rcases family_descends (prefixWord ++ tailWord_506354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_506365 : List Nat := [1, 4, 1, 1, 1, 3, 2, 3, 6]
def baseStart_506365 : Nat := 118140960795 + 506365 * 2 ^ 59
def prefixEnd_506365 : Nat := 4983230072969 + 3 ^ 40 * 506365 * 2
def baseEnd_506365 : Nat := 57779695914225906290839

theorem tailTrace_506365 : CollatzResearch.WordTrace tailWord_506365 prefixEnd_506365 57779695914225906290839 := by
  unfold tailWord_506365
  simp only [CollatzResearch.WordTrace]
  refine ⟨18468648810533560102064549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12312432540355706734709699 18468648810533560102064549)
  ·
    refine ⟨3462871651975042519137103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18468648810533560102064549 3462871651975042519137103)
    ·
      refine ⟨5194307477962563778705655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3462871651975042519137103 5194307477962563778705655)
      ·
        refine ⟨7791461216943845668058483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5194307477962563778705655 7791461216943845668058483)
        ·
          refine ⟨11687191825415768502087725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7791461216943845668058483 11687191825415768502087725)
          ·
            refine ⟨4382696934530913188282897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11687191825415768502087725 4382696934530913188282897)
            ·
              refine ⟨3287022700898184891212173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4382696934530913188282897 3287022700898184891212173)
              ·
                refine ⟨1232633512836819334204565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3287022700898184891212173 1232633512836819334204565)
                ·
                  refine ⟨57779695914225906290839, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1232633512836819334204565 57779695914225906290839)
                  ·
                    rfl

theorem cell22_506365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 2, 3, 6].length) (baseStart_506365 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_506365 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_506365 prefixEnd_506365 := by exact prefixLift 506365
  have htrace : WordTrace (prefixWord ++ tailWord_506365) baseStart_506365 baseEnd_506365 := by
    simpa [prefixWord, tailWord_506365, baseEnd_506365] using wordTrace_append hprefix tailTrace_506365
  have hstable : (prefixWord ++ tailWord_506365).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_506365).length < 2 ^ (prefixWord ++ tailWord_506365).sum := by decide
  have hdescent : baseEnd_506365 < baseStart_506365 := by decide
  rcases family_descends (prefixWord ++ tailWord_506365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_506382 : List Nat := [4, 1, 1, 2, 3, 2, 1, 2, 6]
def baseStart_506382 : Nat := 118140960795 + 506382 * 2 ^ 59
def prefixEnd_506382 : Nat := 4983230072969 + 3 ^ 40 * 506382 * 2
def baseEnd_506382 : Nat := 57781635730031780399155

theorem tailTrace_506382 : CollatzResearch.WordTrace tailWord_506382 prefixEnd_506382 57781635730031780399155 := by
  unfold tailWord_506382
  simp only [CollatzResearch.WordTrace]
  refine ⟨2308658606433996500679175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12312845900981314670288933 2308658606433996500679175)
  ·
    refine ⟨3462987909650994751018763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2308658606433996500679175 3462987909650994751018763)
    ·
      refine ⟨5194481864476492126528145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3462987909650994751018763 5194481864476492126528145)
      ·
        refine ⟨3895861398357369094896109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5194481864476492126528145 3895861398357369094896109)
        ·
          refine ⟨1460948024384013410586041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3895861398357369094896109 1460948024384013410586041)
          ·
            refine ⟨1095711018288010057939531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1460948024384013410586041 1095711018288010057939531)
            ·
              refine ⟨1643566527432015086909297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1095711018288010057939531 1643566527432015086909297)
              ·
                refine ⟨1232674895574011315181973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1643566527432015086909297 1232674895574011315181973)
                ·
                  refine ⟨57781635730031780399155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1232674895574011315181973 57781635730031780399155)
                  ·
                    rfl

theorem cell22_506382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 2, 1, 2, 6].length) (baseStart_506382 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_506382 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_506382 prefixEnd_506382 := by exact prefixLift 506382
  have htrace : WordTrace (prefixWord ++ tailWord_506382) baseStart_506382 baseEnd_506382 := by
    simpa [prefixWord, tailWord_506382, baseEnd_506382] using wordTrace_append hprefix tailTrace_506382
  have hstable : (prefixWord ++ tailWord_506382).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_506382).length < 2 ^ (prefixWord ++ tailWord_506382).sum := by decide
  have hdescent : baseEnd_506382 < baseStart_506382 := by decide
  rcases family_descends (prefixWord ++ tailWord_506382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_506397 : List Nat := [1, 4, 2, 2, 1, 2, 2, 2, 1, 5]
def baseStart_506397 : Nat := 118140960795 + 506397 * 2 ^ 59
def prefixEnd_506397 : Nat := 4983230072969 + 3 ^ 40 * 506397 * 2
def baseEnd_506397 : Nat := 173350041996640302072419

theorem tailTrace_506397 : CollatzResearch.WordTrace tailWord_506397 prefixEnd_506397 173350041996640302072419 := by
  unfold tailWord_506397
  simp only [CollatzResearch.WordTrace]
  refine ⟨18469815946417629567229445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12313210630945086378152963 18469815946417629567229445)
  ·
    refine ⟨3463090489953305543855521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18469815946417629567229445 3463090489953305543855521)
    ·
      refine ⟨2597317867464979157891641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3463090489953305543855521 2597317867464979157891641)
      ·
        refine ⟨1947988400598734368418731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2597317867464979157891641 1947988400598734368418731)
        ·
          refine ⟨2921982600898101552628097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1947988400598734368418731 2921982600898101552628097)
          ·
            refine ⟨2191486950673576164471073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2921982600898101552628097 2191486950673576164471073)
            ·
              refine ⟨1643615213005182123353305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2191486950673576164471073 1643615213005182123353305)
              ·
                refine ⟨1232711409753886592514979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1643615213005182123353305 1232711409753886592514979)
                ·
                  refine ⟨1849067114630829888772469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1232711409753886592514979 1849067114630829888772469)
                  ·
                    refine ⟨173350041996640302072419, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1849067114630829888772469 173350041996640302072419)
                    ·
                      rfl

theorem cell22_506397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 2, 2, 1, 5].length) (baseStart_506397 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_506397 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_506397 prefixEnd_506397 := by exact prefixLift 506397
  have htrace : WordTrace (prefixWord ++ tailWord_506397) baseStart_506397 baseEnd_506397 := by
    simpa [prefixWord, tailWord_506397, baseEnd_506397] using wordTrace_append hprefix tailTrace_506397
  have hstable : (prefixWord ++ tailWord_506397).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_506397).length < 2 ^ (prefixWord ++ tailWord_506397).sum := by decide
  have hdescent : baseEnd_506397 < baseStart_506397 := by decide
  rcases family_descends (prefixWord ++ tailWord_506397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_506440 : List Nat := [2, 1, 3, 1, 1, 1, 1, 4, 2, 6]
def baseStart_506440 : Nat := 118140960795 + 506440 * 2 ^ 59
def prefixEnd_506440 : Nat := 4983230072969 + 3 ^ 40 * 506440 * 2
def baseEnd_506440 : Nat := 173364761775402523247287

theorem tailTrace_506440 : CollatzResearch.WordTrace tailWord_506440 prefixEnd_506440 173364761775402523247287 := by
  unfold tailWord_506440
  simp only [CollatzResearch.WordTrace]
  refine ⟨9235692142630923955522387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12314256190174565274029849 9235692142630923955522387)
  ·
    refine ⟨13853538213946385933283581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9235692142630923955522387 13853538213946385933283581)
    ·
      refine ⟨5195076830229894724981343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13853538213946385933283581 5195076830229894724981343)
      ·
        refine ⟨7792615245344842087472015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5195076830229894724981343 7792615245344842087472015)
        ·
          refine ⟨11688922868017263131208023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7792615245344842087472015 11688922868017263131208023)
          ·
            refine ⟨17533384302025894696812035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11688922868017263131208023 17533384302025894696812035)
            ·
              refine ⟨26300076453038842045218053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17533384302025894696812035 26300076453038842045218053)
              ·
                refine ⟨4931264334944782883478385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26300076453038842045218053 4931264334944782883478385)
                ·
                  refine ⟨3698448251208587162608789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4931264334944782883478385 3698448251208587162608789)
                  ·
                    refine ⟨173364761775402523247287, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3698448251208587162608789 173364761775402523247287)
                    ·
                      rfl

theorem cell22_506440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 4, 2, 6].length) (baseStart_506440 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_506440 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_506440 prefixEnd_506440 := by exact prefixLift 506440
  have htrace : WordTrace (prefixWord ++ tailWord_506440) baseStart_506440 baseEnd_506440 := by
    simpa [prefixWord, tailWord_506440, baseEnd_506440] using wordTrace_append hprefix tailTrace_506440
  have hstable : (prefixWord ++ tailWord_506440).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_506440).length < 2 ^ (prefixWord ++ tailWord_506440).sum := by decide
  have hdescent : baseEnd_506440 < baseStart_506440 := by decide
  rcases family_descends (prefixWord ++ tailWord_506440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_506455 : List Nat := [1, 1, 3, 2, 2, 2, 1, 1, 9]
def baseStart_506455 : Nat := 118140960795 + 506455 * 2 ^ 59
def prefixEnd_506455 : Nat := 4983230072969 + 3 ^ 40 * 506455 * 2
def baseEnd_506455 : Nat := 57789965527315828040747

theorem tailTrace_506455 : CollatzResearch.WordTrace tailWord_506455 prefixEnd_506455 57789965527315828040747 := by
  unfold tailWord_506455
  simp only [CollatzResearch.WordTrace]
  refine ⟨18471931380207505472840819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12314620920138336981893879 18471931380207505472840819)
  ·
    refine ⟨27707897070311258209261229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18471931380207505472840819 27707897070311258209261229)
    ·
      refine ⟨10390461401366721828472961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27707897070311258209261229 10390461401366721828472961)
      ·
        refine ⟨7792846051025041371354721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10390461401366721828472961 7792846051025041371354721)
        ·
          refine ⟨5844634538268781028516041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7792846051025041371354721 5844634538268781028516041)
          ·
            refine ⟨4383475903701585771387031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5844634538268781028516041 4383475903701585771387031)
            ·
              refine ⟨6575213855552378657080547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4383475903701585771387031 6575213855552378657080547)
              ·
                refine ⟨9862820783328567985620821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6575213855552378657080547 9862820783328567985620821)
                ·
                  refine ⟨57789965527315828040747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 9862820783328567985620821 57789965527315828040747)
                  ·
                    rfl

theorem cell22_506455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 1, 1, 9].length) (baseStart_506455 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_506455 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_506455 prefixEnd_506455 := by exact prefixLift 506455
  have htrace : WordTrace (prefixWord ++ tailWord_506455) baseStart_506455 baseEnd_506455 := by
    simpa [prefixWord, tailWord_506455, baseEnd_506455] using wordTrace_append hprefix tailTrace_506455
  have hstable : (prefixWord ++ tailWord_506455).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_506455).length < 2 ^ (prefixWord ++ tailWord_506455).sum := by decide
  have hdescent : baseEnd_506455 < baseStart_506455 := by decide
  rcases family_descends (prefixWord ++ tailWord_506455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_506489 : List Nat := [1, 2, 1, 3, 3, 2, 4, 1, 5]
def baseStart_506489 : Nat := 118140960795 + 506489 * 2 ^ 59
def prefixEnd_506489 : Nat := 4983230072969 + 3 ^ 40 * 506489 * 2
def baseEnd_506489 : Nat := 57793845158927576257379

theorem tailTrace_506489 : CollatzResearch.WordTrace tailWord_506489 prefixEnd_506489 57793845158927576257379 := by
  unfold tailWord_506489
  simp only [CollatzResearch.WordTrace]
  refine ⟨18473171462084329279578521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12315447641389552853052347 18473171462084329279578521)
  ·
    refine ⟨13854878596563246959683891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18473171462084329279578521 13854878596563246959683891)
    ·
      refine ⟨20782317894844870439525837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13854878596563246959683891 20782317894844870439525837)
      ·
        refine ⟨7793369210566826414822189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20782317894844870439525837 7793369210566826414822189)
        ·
          refine ⟨2922513453962559905558321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7793369210566826414822189 2922513453962559905558321)
          ·
            refine ⟨2191885090471919929168741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2922513453962559905558321 2191885090471919929168741)
            ·
              refine ⟨410978454463484986719139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2191885090471919929168741 410978454463484986719139)
              ·
                refine ⟨616467681695227480078709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 410978454463484986719139 616467681695227480078709)
                ·
                  refine ⟨57793845158927576257379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 616467681695227480078709 57793845158927576257379)
                  ·
                    rfl

theorem cell22_506489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 4, 1, 5].length) (baseStart_506489 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_506489 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_506489 prefixEnd_506489 := by exact prefixLift 506489
  have htrace : WordTrace (prefixWord ++ tailWord_506489) baseStart_506489 baseEnd_506489 := by
    simpa [prefixWord, tailWord_506489, baseEnd_506489] using wordTrace_append hprefix tailTrace_506489
  have hstable : (prefixWord ++ tailWord_506489).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_506489).length < 2 ^ (prefixWord ++ tailWord_506489).sum := by decide
  have hdescent : baseEnd_506489 < baseStart_506489 := by decide
  rcases family_descends (prefixWord ++ tailWord_506489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_506532 : List Nat := [2, 3, 1, 2, 2, 1, 1, 2, 3, 5]
def baseStart_506532 : Nat := 118140960795 + 506532 * 2 ^ 59
def prefixEnd_506532 : Nat := 4983230072969 + 3 ^ 40 * 506532 * 2
def baseEnd_506532 : Nat := 173396255255544949947005

theorem tailTrace_506532 : CollatzResearch.WordTrace tailWord_506532 prefixEnd_506532 173396255255544949947005 := by
  unfold tailWord_506532
  simp only [CollatzResearch.WordTrace]
  refine ⟨9237369900464273811696925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12316493200619031748929233 9237369900464273811696925)
  ·
    refine ⟨3464013712674102679386347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9237369900464273811696925 3464013712674102679386347)
    ·
      refine ⟨5196020569011154019079521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3464013712674102679386347 5196020569011154019079521)
      ·
        refine ⟨3897015426758365514309641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5196020569011154019079521 3897015426758365514309641)
        ·
          refine ⟨2922761570068774135732231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3897015426758365514309641 2922761570068774135732231)
          ·
            refine ⟨4384142355103161203598347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2922761570068774135732231 4384142355103161203598347)
            ·
              refine ⟨6576213532654741805397521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4384142355103161203598347 6576213532654741805397521)
              ·
                refine ⟨4932160149491056354048141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6576213532654741805397521 4932160149491056354048141)
                ·
                  refine ⟨1849560056059146132768053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4932160149491056354048141 1849560056059146132768053)
                  ·
                    refine ⟨173396255255544949947005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1849560056059146132768053 173396255255544949947005)
                    ·
                      rfl

theorem cell22_506532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 1, 2, 3, 5].length) (baseStart_506532 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_506532 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_506532 prefixEnd_506532 := by exact prefixLift 506532
  have htrace : WordTrace (prefixWord ++ tailWord_506532) baseStart_506532 baseEnd_506532 := by
    simpa [prefixWord, tailWord_506532, baseEnd_506532] using wordTrace_append hprefix tailTrace_506532
  have hstable : (prefixWord ++ tailWord_506532).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_506532).length < 2 ^ (prefixWord ++ tailWord_506532).sum := by decide
  have hdescent : baseEnd_506532 < baseStart_506532 := by decide
  rcases family_descends (prefixWord ++ tailWord_506532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_506549 : List Nat := [1, 3, 3, 3, 1, 1, 1, 3, 1, 5]
def baseStart_506549 : Nat := 118140960795 + 506549 * 2 ^ 59
def prefixEnd_506549 : Nat := 4983230072969 + 3 ^ 40 * 506549 * 2
def baseEnd_506549 : Nat := 173402074702962572271953

theorem tailTrace_506549 : CollatzResearch.WordTrace tailWord_506549 prefixEnd_506549 173402074702962572271953 := by
  unfold tailWord_506549
  simp only [CollatzResearch.WordTrace]
  refine ⟨18475359841866959526762701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12316906561244639684508467 18475359841866959526762701)
  ·
    refine ⟨6928259940700109822536013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18475359841866959526762701 6928259940700109822536013)
    ·
      refine ⟨2598097477762541183451005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6928259940700109822536013 2598097477762541183451005)
      ·
        refine ⟨974286554160952943794127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2598097477762541183451005 974286554160952943794127)
        ·
          refine ⟨1461429831241429415691191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 974286554160952943794127 1461429831241429415691191)
          ·
            refine ⟨2192144746862144123536787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1461429831241429415691191 2192144746862144123536787)
            ·
              refine ⟨3288217120293216185305181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2192144746862144123536787 3288217120293216185305181)
              ·
                refine ⟨1233081420109956069489443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3288217120293216185305181 1233081420109956069489443)
                ·
                  refine ⟨1849622130164934104234165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1233081420109956069489443 1849622130164934104234165)
                  ·
                    refine ⟨173402074702962572271953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1849622130164934104234165 173402074702962572271953)
                    ·
                      rfl

theorem cell22_506549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 1, 3, 1, 5].length) (baseStart_506549 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_506549 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_506549 prefixEnd_506549 := by exact prefixLift 506549
  have htrace : WordTrace (prefixWord ++ tailWord_506549) baseStart_506549 baseEnd_506549 := by
    simpa [prefixWord, tailWord_506549, baseEnd_506549] using wordTrace_append hprefix tailTrace_506549
  have hstable : (prefixWord ++ tailWord_506549).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_506549).length < 2 ^ (prefixWord ++ tailWord_506549).sum := by decide
  have hdescent : baseEnd_506549 < baseStart_506549 := by decide
  rcases family_descends (prefixWord ++ tailWord_506549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_506564 : List Nat := [2, 3, 3, 1, 1, 3, 1, 1, 1, 6]
def baseStart_506564 : Nat := 118140960795 + 506564 * 2 ^ 59
def prefixEnd_506564 : Nat := 4983230072969 + 3 ^ 40 * 506564 * 2
def baseEnd_506564 : Nat := 173407209509507533146907

theorem tailTrace_506564 : CollatzResearch.WordTrace tailWord_506564 prefixEnd_506564 173407209509507533146907 := by
  unfold tailWord_506564
  simp only [CollatzResearch.WordTrace]
  refine ⟨9237953468406308544279373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12317271291208411392372497 9237953468406308544279373)
  ·
    refine ⟨3464232550652365704104765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9237953468406308544279373 3464232550652365704104765)
    ·
      refine ⟨1299087206494637139039287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3464232550652365704104765 1299087206494637139039287)
      ·
        refine ⟨1948630809741955708558931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1299087206494637139039287 1948630809741955708558931)
        ·
          refine ⟨2922946214612933562838397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1948630809741955708558931 2922946214612933562838397)
          ·
            refine ⟨1096104830479850086064399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2922946214612933562838397 1096104830479850086064399)
            ·
              refine ⟨1644157245719775129096599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1096104830479850086064399 1644157245719775129096599)
              ·
                refine ⟨2466235868579662693644899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1644157245719775129096599 2466235868579662693644899)
                ·
                  refine ⟨3699353802869494040467349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2466235868579662693644899 3699353802869494040467349)
                  ·
                    refine ⟨173407209509507533146907, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3699353802869494040467349 173407209509507533146907)
                    ·
                      rfl

theorem cell22_506564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 3, 1, 1, 1, 6].length) (baseStart_506564 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_506564 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_506564 prefixEnd_506564 := by exact prefixLift 506564
  have htrace : WordTrace (prefixWord ++ tailWord_506564) baseStart_506564 baseEnd_506564 := by
    simpa [prefixWord, tailWord_506564, baseEnd_506564] using wordTrace_append hprefix tailTrace_506564
  have hstable : (prefixWord ++ tailWord_506564).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_506564).length < 2 ^ (prefixWord ++ tailWord_506564).sum := by decide
  have hdescent : baseEnd_506564 < baseStart_506564 := by decide
  rcases family_descends (prefixWord ++ tailWord_506564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_506613 : List Nat := [1, 3, 6, 1, 1, 1, 1, 8]
def baseStart_506613 : Nat := 118140960795 + 506613 * 2 ^ 59
def prefixEnd_506613 : Nat := 4983230072969 + 3 ^ 40 * 506613 * 2
def baseEnd_506613 : Nat := 19269331467876415407973

theorem tailTrace_506613 : CollatzResearch.WordTrace tailWord_506613 prefixEnd_506613 19269331467876415407973 := by
  unfold tailWord_506613
  simp only [CollatzResearch.WordTrace]
  refine ⟨18477694113635098457092493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12318462742423398971394995 18477694113635098457092493)
  ·
    refine ⟨6929135292613161921409685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18477694113635098457092493 6929135292613161921409685)
    ·
      refine ⟨324803216841241965066079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 6929135292613161921409685 324803216841241965066079)
      ·
        refine ⟨487204825261862947599119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 324803216841241965066079 487204825261862947599119)
        ·
          refine ⟨730807237892794421398679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 487204825261862947599119 730807237892794421398679)
          ·
            refine ⟨1096210856839191632098019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 730807237892794421398679 1096210856839191632098019)
            ·
              refine ⟨1644316285258787448147029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1096210856839191632098019 1644316285258787448147029)
              ·
                refine ⟨19269331467876415407973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1644316285258787448147029 19269331467876415407973)
                ·
                  rfl

theorem cell22_506613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 1, 1, 8].length) (baseStart_506613 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_506613 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_506613 prefixEnd_506613 := by exact prefixLift 506613
  have htrace : WordTrace (prefixWord ++ tailWord_506613) baseStart_506613 baseEnd_506613 := by
    simpa [prefixWord, tailWord_506613, baseEnd_506613] using wordTrace_append hprefix tailTrace_506613
  have hstable : (prefixWord ++ tailWord_506613).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_506613).length < 2 ^ (prefixWord ++ tailWord_506613).sum := by decide
  have hdescent : baseEnd_506613 < baseStart_506613 := by decide
  rcases family_descends (prefixWord ++ tailWord_506613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_506658 : List Nat := [3, 3, 1, 1, 2, 4, 2, 1, 5]
def baseStart_506658 : Nat := 118140960795 + 506658 * 2 ^ 59
def prefixEnd_506658 : Nat := 4983230072969 + 3 ^ 40 * 506658 * 2
def baseEnd_506658 : Nat := 57813129210174207098873

theorem tailTrace_506658 : CollatzResearch.WordTrace tailWord_506658 prefixEnd_506658 57813129210174207098873 := by
  unfold tailWord_506658
  simp only [CollatzResearch.WordTrace]
  refine ⟨4619833849618017785620157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12319556932314714094987085 4619833849618017785620157)
  ·
    refine ⟨1732437693606756669607559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4619833849618017785620157 1732437693606756669607559)
    ·
      refine ⟨2598656540410135004411339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1732437693606756669607559 2598656540410135004411339)
      ·
        refine ⟨3897984810615202506617009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2598656540410135004411339 3897984810615202506617009)
        ·
          refine ⟨2923488607961401879962757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3897984810615202506617009 2923488607961401879962757)
          ·
            refine ⟨548154113992762852493017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2923488607961401879962757 548154113992762852493017)
            ·
              refine ⟨411115585494572139369763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 548154113992762852493017 411115585494572139369763)
              ·
                refine ⟨616673378241858209054645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 411115585494572139369763 616673378241858209054645)
                ·
                  refine ⟨57813129210174207098873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 616673378241858209054645 57813129210174207098873)
                  ·
                    rfl

theorem cell22_506658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 4, 2, 1, 5].length) (baseStart_506658 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_506658 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_506658 prefixEnd_506658 := by exact prefixLift 506658
  have htrace : WordTrace (prefixWord ++ tailWord_506658) baseStart_506658 baseEnd_506658 := by
    simpa [prefixWord, tailWord_506658, baseEnd_506658] using wordTrace_append hprefix tailTrace_506658
  have hstable : (prefixWord ++ tailWord_506658).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_506658).length < 2 ^ (prefixWord ++ tailWord_506658).sum := by decide
  have hdescent : baseEnd_506658 < baseStart_506658 := by decide
  rcases family_descends (prefixWord ++ tailWord_506658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_506697 : List Nat := [1, 2, 1, 1, 2, 15]
def baseStart_506697 : Nat := 118140960795 + 506697 * 2 ^ 59
def prefixEnd_506697 : Nat := 4983230072969 + 3 ^ 40 * 506697 * 2
def baseEnd_506697 : Nat := 2141391828735055797179

theorem tailTrace_506697 : CollatzResearch.WordTrace tailWord_506697 prefixEnd_506697 2141391828735055797179 := by
  unfold tailWord_506697
  simp only [CollatzResearch.WordTrace]
  refine ⟨18480757845330780803150345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12320505230220520535433563 18480757845330780803150345)
  ·
    refine ⟨13860568383998085602362759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18480757845330780803150345 13860568383998085602362759)
    ·
      refine ⟨20790852575997128403544139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13860568383998085602362759 20790852575997128403544139)
      ·
        refine ⟨31186278863995692605316209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20790852575997128403544139 31186278863995692605316209)
        ·
          refine ⟨23389709147996769453987157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31186278863995692605316209 23389709147996769453987157)
          ·
            refine ⟨2141391828735055797179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 15 23389709147996769453987157 2141391828735055797179)
            ·
              rfl

theorem cell22_506697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 15].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 15].length) (baseStart_506697 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_506697 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_506697 prefixEnd_506697 := by exact prefixLift 506697
  have htrace : WordTrace (prefixWord ++ tailWord_506697) baseStart_506697 baseEnd_506697 := by
    simpa [prefixWord, tailWord_506697, baseEnd_506697] using wordTrace_append hprefix tailTrace_506697
  have hstable : (prefixWord ++ tailWord_506697).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_506697).length < 2 ^ (prefixWord ++ tailWord_506697).sum := by decide
  have hdescent : baseEnd_506697 < baseStart_506697 := by decide
  rcases family_descends (prefixWord ++ tailWord_506697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_506714 : List Nat := [3, 1, 1, 2, 1, 4, 3, 7]
def baseStart_506714 : Nat := 118140960795 + 506714 * 2 ^ 59
def prefixEnd_506714 : Nat := 4983230072969 + 3 ^ 40 * 506714 * 2
def baseEnd_506714 : Nat := 19273173063884126877383

theorem tailTrace_506714 : CollatzResearch.WordTrace tailWord_506714 prefixEnd_506714 19273173063884126877383 := by
  unfold tailWord_506714
  simp only [CollatzResearch.WordTrace]
  refine ⟨4620344471567298176629799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12320918590846128471012797 4620344471567298176629799)
  ·
    refine ⟨6930516707350947264944699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4620344471567298176629799 6930516707350947264944699)
    ·
      refine ⟨10395775061026420897417049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6930516707350947264944699 10395775061026420897417049)
      ·
        refine ⟨7796831295769815673062787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10395775061026420897417049 7796831295769815673062787)
        ·
          refine ⟨11695246943654723509594181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7796831295769815673062787 11695246943654723509594181)
          ·
            refine ⟨2192858801935260658048909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11695246943654723509594181 2192858801935260658048909)
            ·
              refine ⟨822322050725722746768341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2192858801935260658048909 822322050725722746768341)
              ·
                refine ⟨19273173063884126877383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 822322050725722746768341 19273173063884126877383)
                ·
                  rfl

theorem cell22_506714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 3, 7].length) (baseStart_506714 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_506714 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_506714 prefixEnd_506714 := by exact prefixLift 506714
  have htrace : WordTrace (prefixWord ++ tailWord_506714) baseStart_506714 baseEnd_506714 := by
    simpa [prefixWord, tailWord_506714, baseEnd_506714] using wordTrace_append hprefix tailTrace_506714
  have hstable : (prefixWord ++ tailWord_506714).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_506714).length < 2 ^ (prefixWord ++ tailWord_506714).sum := by decide
  have hdescent : baseEnd_506714 < baseStart_506714 := by decide
  rcases family_descends (prefixWord ++ tailWord_506714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_506763 : List Nat := [1, 1, 1, 1, 4, 2, 4, 4, 1, 3]
def baseStart_506763 : Nat := 118140960795 + 506763 * 2 ^ 59
def prefixEnd_506763 : Nat := 4983230072969 + 3 ^ 40 * 506763 * 2
def baseEnd_506763 : Nat := 173475331276337347421297

theorem tailTrace_506763 : CollatzResearch.WordTrace tailWord_506763 prefixEnd_506763 173475331276337347421297 := by
  unfold tailWord_506763
  simp only [CollatzResearch.WordTrace]
  refine ⟨18483165063091674075052943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12322110042061116050035295 18483165063091674075052943)
  ·
    refine ⟨27724747594637511112579415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18483165063091674075052943 27724747594637511112579415)
    ·
      refine ⟨41587121391956266668869123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27724747594637511112579415 41587121391956266668869123)
      ·
        refine ⟨62380682087934400003303685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41587121391956266668869123 62380682087934400003303685)
        ·
          refine ⟨11696377891487700000619441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 62380682087934400003303685 11696377891487700000619441)
          ·
            refine ⟨8772283418615775000464581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11696377891487700000619441 8772283418615775000464581)
            ·
              refine ⟨1644803140990457812587109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8772283418615775000464581 1644803140990457812587109)
              ·
                refine ⟨308400588935710839860083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1644803140990457812587109 308400588935710839860083)
                ·
                  refine ⟨462600883403566259790125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 308400588935710839860083 462600883403566259790125)
                  ·
                    refine ⟨173475331276337347421297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 462600883403566259790125 173475331276337347421297)
                    ·
                      rfl

theorem cell22_506763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 4, 4, 1, 3].length) (baseStart_506763 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_506763 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_506763 prefixEnd_506763 := by exact prefixLift 506763
  have htrace : WordTrace (prefixWord ++ tailWord_506763) baseStart_506763 baseEnd_506763 := by
    simpa [prefixWord, tailWord_506763, baseEnd_506763] using wordTrace_append hprefix tailTrace_506763
  have hstable : (prefixWord ++ tailWord_506763).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_506763).length < 2 ^ (prefixWord ++ tailWord_506763).sum := by decide
  have hdescent : baseEnd_506763 < baseStart_506763 := by decide
  rcases family_descends (prefixWord ++ tailWord_506763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_506819 : List Nat := [1, 1, 1, 3, 1, 1, 2, 4, 3, 5]
def baseStart_506819 : Nat := 118140960795 + 506819 * 2 ^ 59
def prefixEnd_506819 : Nat := 4983230072969 + 3 ^ 40 * 506819 * 2
def baseEnd_506819 : Nat := 173494501220771868021125

theorem tailTrace_506819 : CollatzResearch.WordTrace tailWord_506819 prefixEnd_506819 173494501220771868021125 := by
  unfold tailWord_506819
  simp only [CollatzResearch.WordTrace]
  refine ⟨18485207550888795639091511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12323471700592530426061007 18485207550888795639091511)
  ·
    refine ⟨27727811326333193458637267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18485207550888795639091511 27727811326333193458637267)
    ·
      refine ⟨41591716989499790187955901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27727811326333193458637267 41591716989499790187955901)
      ·
        refine ⟨15596893871062421320483463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41591716989499790187955901 15596893871062421320483463)
        ·
          refine ⟨23395340806593631980725195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15596893871062421320483463 23395340806593631980725195)
          ·
            refine ⟨35093011209890447971087793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23395340806593631980725195 35093011209890447971087793)
            ·
              refine ⟨26319758407417835978315845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35093011209890447971087793 26319758407417835978315845)
              ·
                refine ⟨4934954701390844245934221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26319758407417835978315845 4934954701390844245934221)
                ·
                  refine ⟨1850608013021566592225333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4934954701390844245934221 1850608013021566592225333)
                  ·
                    refine ⟨173494501220771868021125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1850608013021566592225333 173494501220771868021125)
                    ·
                      rfl

theorem cell22_506819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 5].length) (baseStart_506819 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_506819 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_506819 prefixEnd_506819 := by exact prefixLift 506819
  have htrace : WordTrace (prefixWord ++ tailWord_506819) baseStart_506819 baseEnd_506819 := by
    simpa [prefixWord, tailWord_506819, baseEnd_506819] using wordTrace_append hprefix tailTrace_506819
  have hstable : (prefixWord ++ tailWord_506819).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_506819).length < 2 ^ (prefixWord ++ tailWord_506819).sum := by decide
  have hdescent : baseEnd_506819 < baseStart_506819 := by decide
  rcases family_descends (prefixWord ++ tailWord_506819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_506866 : List Nat := [3, 2, 1, 5, 11]
def baseStart_506866 : Nat := 118140960795 + 506866 * 2 ^ 59
def prefixEnd_506866 : Nat := 4983230072969 + 3 ^ 40 * 506866 * 2
def baseEnd_506866 : Nat := 714035350951767127967

theorem tailTrace_506866 : CollatzResearch.WordTrace tailWord_506866 prefixEnd_506866 714035350951767127967 := by
  unfold tailWord_506866
  simp only [CollatzResearch.WordTrace]
  refine ⟨4621730445429630666513113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12324614521145681777368301 4621730445429630666513113)
  ·
    refine ⟨3466297834072222999884835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4621730445429630666513113 3466297834072222999884835)
    ·
      refine ⟨5199446751108334499827253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3466297834072222999884835 5199446751108334499827253)
      ·
        refine ⟨487448132916406359358805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 5199446751108334499827253 487448132916406359358805)
        ·
          refine ⟨714035350951767127967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 11 487448132916406359358805 714035350951767127967)
          ·
            rfl

theorem cell22_506866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 11].length) (baseStart_506866 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_506866 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_506866 prefixEnd_506866 := by exact prefixLift 506866
  have htrace : WordTrace (prefixWord ++ tailWord_506866) baseStart_506866 baseEnd_506866 := by
    simpa [prefixWord, tailWord_506866, baseEnd_506866] using wordTrace_append hprefix tailTrace_506866
  have hstable : (prefixWord ++ tailWord_506866).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_506866).length < 2 ^ (prefixWord ++ tailWord_506866).sum := by decide
  have hdescent : baseEnd_506866 < baseStart_506866 := by decide
  rcases family_descends (prefixWord ++ tailWord_506866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_506870 : List Nat := [5, 1, 1, 1, 3, 1, 1, 4, 2, 3]
def baseStart_506870 : Nat := 118140960795 + 506870 * 2 ^ 59
def prefixEnd_506870 : Nat := 4983230072969 + 3 ^ 40 * 506870 * 2
def baseEnd_506870 : Nat := 173511959563024734995969

theorem tailTrace_506870 : CollatzResearch.WordTrace tailWord_506870 prefixEnd_506870 173511959563024734995969 := by
  unfold tailWord_506870
  simp only [CollatzResearch.WordTrace]
  refine ⟨1155441729606501959324879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 12324711782469354232798709 1155441729606501959324879)
  ·
    refine ⟨1733162594409752938987319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1155441729606501959324879 1733162594409752938987319)
    ·
      refine ⟨2599743891614629408480979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1733162594409752938987319 2599743891614629408480979)
      ·
        refine ⟨3899615837421944112721469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2599743891614629408480979 3899615837421944112721469)
        ·
          refine ⟨1462355939033229042270551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3899615837421944112721469 1462355939033229042270551)
          ·
            refine ⟨2193533908549843563405827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1462355939033229042270551 2193533908549843563405827)
            ·
              refine ⟨3290300862824765345108741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2193533908549843563405827 3290300862824765345108741)
              ·
                refine ⟨616931411779643502207889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3290300862824765345108741 616931411779643502207889)
                ·
                  refine ⟨462698558834732626655917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 616931411779643502207889 462698558834732626655917)
                  ·
                    refine ⟨173511959563024734995969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 462698558834732626655917 173511959563024734995969)
                    ·
                      rfl

theorem cell22_506870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 1, 4, 2, 3].length) (baseStart_506870 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_506870 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_506870 prefixEnd_506870 := by exact prefixLift 506870
  have htrace : WordTrace (prefixWord ++ tailWord_506870) baseStart_506870 baseEnd_506870 := by
    simpa [prefixWord, tailWord_506870, baseEnd_506870] using wordTrace_append hprefix tailTrace_506870
  have hstable : (prefixWord ++ tailWord_506870).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_506870).length < 2 ^ (prefixWord ++ tailWord_506870).sum := by decide
  have hdescent : baseEnd_506870 < baseStart_506870 := by decide
  rcases family_descends (prefixWord ++ tailWord_506870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_506915 : List Nat := [1, 1, 1, 4, 3, 2, 1, 5, 1, 3]
def baseStart_506915 : Nat := 118140960795 + 506915 * 2 ^ 59
def prefixEnd_506915 : Nat := 4983230072969 + 3 ^ 40 * 506915 * 2
def baseEnd_506915 : Nat := 173527363982659617620831

theorem tailTrace_506915 : CollatzResearch.WordTrace tailWord_506915 prefixEnd_506915 173527363982659617620831 := by
  unfold tailWord_506915
  simp only [CollatzResearch.WordTrace]
  refine ⟨18488708958541004034586199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12325805972360669356390799 18488708958541004034586199)
  ·
    refine ⟨27733063437811506051879299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18488708958541004034586199 27733063437811506051879299)
    ·
      refine ⟨41599595156717259077818949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27733063437811506051879299 41599595156717259077818949)
      ·
        refine ⟨7799924091884486077091053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41599595156717259077818949 7799924091884486077091053)
        ·
          refine ⟨2924971534456682278909145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7799924091884486077091053 2924971534456682278909145)
          ·
            refine ⟨2193728650842511709181859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2924971534456682278909145 2193728650842511709181859)
            ·
              refine ⟨3290592976263767563772789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2193728650842511709181859 3290592976263767563772789)
              ·
                refine ⟨308493091524728209103699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3290592976263767563772789 308493091524728209103699)
                ·
                  refine ⟨462739637287092313655549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 308493091524728209103699 462739637287092313655549)
                  ·
                    refine ⟨173527363982659617620831, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 462739637287092313655549 173527363982659617620831)
                    ·
                      rfl

theorem cell22_506915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 1, 5, 1, 3].length) (baseStart_506915 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_506915 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_506915 prefixEnd_506915 := by exact prefixLift 506915
  have htrace : WordTrace (prefixWord ++ tailWord_506915) baseStart_506915 baseEnd_506915 := by
    simpa [prefixWord, tailWord_506915, baseEnd_506915] using wordTrace_append hprefix tailTrace_506915
  have hstable : (prefixWord ++ tailWord_506915).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_506915).length < 2 ^ (prefixWord ++ tailWord_506915).sum := by decide
  have hdescent : baseEnd_506915 < baseStart_506915 := by decide
  rcases family_descends (prefixWord ++ tailWord_506915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_506932 : List Nat := [2, 5, 1, 2, 1, 2, 2, 1, 3, 3]
def baseStart_506932 : Nat := 118140960795 + 506932 * 2 ^ 59
def prefixEnd_506932 : Nat := 4983230072969 + 3 ^ 40 * 506932 * 2
def baseEnd_506932 : Nat := 173533183430077239945779

theorem tailTrace_506932 : CollatzResearch.WordTrace tailWord_506932 prefixEnd_506932 173533183430077239945779 := by
  unfold tailWord_506932
  simp only [CollatzResearch.WordTrace]
  refine ⟨9244664499739707968977525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12326219332986277291970033 9244664499739707968977525)
  ·
    refine ⟨866687296850597622091643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 9244664499739707968977525 866687296850597622091643)
    ·
      refine ⟨1300030945275896433137465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 866687296850597622091643 1300030945275896433137465)
      ·
        refine ⟨975023208956922324853099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1300030945275896433137465 975023208956922324853099)
        ·
          refine ⟨1462534813435383487279649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 975023208956922324853099 1462534813435383487279649)
          ·
            refine ⟨1096901110076537615459737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1462534813435383487279649 1096901110076537615459737)
            ·
              refine ⟨822675832557403211594803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1096901110076537615459737 822675832557403211594803)
              ·
                refine ⟨1234013748836104817392205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 822675832557403211594803 1234013748836104817392205)
                ·
                  refine ⟨462755155813539306522077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1234013748836104817392205 462755155813539306522077)
                  ·
                    refine ⟨173533183430077239945779, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 462755155813539306522077 173533183430077239945779)
                    ·
                      rfl

theorem cell22_506932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 2, 2, 1, 3, 3].length) (baseStart_506932 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_506932 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_506932 prefixEnd_506932 := by exact prefixLift 506932
  have htrace : WordTrace (prefixWord ++ tailWord_506932) baseStart_506932 baseEnd_506932 := by
    simpa [prefixWord, tailWord_506932, baseEnd_506932] using wordTrace_append hprefix tailTrace_506932
  have hstable : (prefixWord ++ tailWord_506932).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_506932).length < 2 ^ (prefixWord ++ tailWord_506932).sum := by decide
  have hdescent : baseEnd_506932 < baseStart_506932 := by decide
  rcases family_descends (prefixWord ++ tailWord_506932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_506988 : List Nat := [2, 2, 1, 1, 3, 2, 1, 3, 4, 3]
def baseStart_506988 : Nat := 118140960795 + 506988 * 2 ^ 59
def prefixEnd_506988 : Nat := 4983230072969 + 3 ^ 40 * 506988 * 2
def baseEnd_506988 : Nat := 173552353374511760545607

theorem tailTrace_506988 : CollatzResearch.WordTrace tailWord_506988 prefixEnd_506988 173552353374511760545607 := by
  unfold tailWord_506988
  simp only [CollatzResearch.WordTrace]
  refine ⟨9245685743638268750996809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12327580991517691667995745 9245685743638268750996809)
  ·
    refine ⟨6934264307728701563247607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9245685743638268750996809 6934264307728701563247607)
    ·
      refine ⟨10401396461593052344871411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6934264307728701563247607 10401396461593052344871411)
      ·
        refine ⟨15602094692389578517307117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10401396461593052344871411 15602094692389578517307117)
        ·
          refine ⟨5850785509646091943990169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15602094692389578517307117 5850785509646091943990169)
          ·
            refine ⟨4388089132234568957992627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5850785509646091943990169 4388089132234568957992627)
            ·
              refine ⟨6582133698351853436988941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4388089132234568957992627 6582133698351853436988941)
              ·
                refine ⟨2468300136881945038870853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6582133698351853436988941 2468300136881945038870853)
                ·
                  refine ⟨462806275665364694788285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2468300136881945038870853 462806275665364694788285)
                  ·
                    refine ⟨173552353374511760545607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 462806275665364694788285 173552353374511760545607)
                    ·
                      rfl

theorem cell22_506988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 4, 3].length) (baseStart_506988 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_506988 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_506988 prefixEnd_506988 := by exact prefixLift 506988
  have htrace : WordTrace (prefixWord ++ tailWord_506988) baseStart_506988 baseEnd_506988 := by
    simpa [prefixWord, tailWord_506988, baseEnd_506988] using wordTrace_append hprefix tailTrace_506988
  have hstable : (prefixWord ++ tailWord_506988).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_506988).length < 2 ^ (prefixWord ++ tailWord_506988).sum := by decide
  have hdescent : baseEnd_506988 < baseStart_506988 := by decide
  rcases family_descends (prefixWord ++ tailWord_506988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_506990 : List Nat := [4, 1, 2, 2, 1, 4, 1, 1, 6]
def baseStart_506990 : Nat := 118140960795 + 506990 * 2 ^ 59
def prefixEnd_506990 : Nat := 4983230072969 + 3 ^ 40 * 506990 * 2
def baseEnd_506990 : Nat := 57851012671794807331867

theorem tailTrace_506990 : CollatzResearch.WordTrace tailWord_506990 prefixEnd_506990 57851012671794807331867 := by
  unfold tailWord_506990
  simp only [CollatzResearch.WordTrace]
  refine ⟨2311430554158661480445803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12327629622179527895710949 2311430554158661480445803)
  ·
    refine ⟨3467145831237992220668705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2311430554158661480445803 3467145831237992220668705)
    ·
      refine ⟨2600359373428494165501529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3467145831237992220668705 2600359373428494165501529)
      ·
        refine ⟨1950269530071370624126147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2600359373428494165501529 1950269530071370624126147)
        ·
          refine ⟨2925404295107055936189221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1950269530071370624126147 2925404295107055936189221)
          ·
            refine ⟨548513305332572988035479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2925404295107055936189221 548513305332572988035479)
            ·
              refine ⟨822769957998859482053219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 548513305332572988035479 822769957998859482053219)
              ·
                refine ⟨1234154936998289223079829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 822769957998859482053219 1234154936998289223079829)
                ·
                  refine ⟨57851012671794807331867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1234154936998289223079829 57851012671794807331867)
                  ·
                    rfl

theorem cell22_506990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 4, 1, 1, 6].length) (baseStart_506990 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_506990 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_506990 prefixEnd_506990 := by exact prefixLift 506990
  have htrace : WordTrace (prefixWord ++ tailWord_506990) baseStart_506990 baseEnd_506990 := by
    simpa [prefixWord, tailWord_506990, baseEnd_506990] using wordTrace_append hprefix tailTrace_506990
  have hstable : (prefixWord ++ tailWord_506990).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_506990).length < 2 ^ (prefixWord ++ tailWord_506990).sum := by decide
  have hdescent : baseEnd_506990 < baseStart_506990 := by decide
  rcases family_descends (prefixWord ++ tailWord_506990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_507005 : List Nat := [1, 4, 1, 1, 3, 1, 3, 3, 2, 3]
def baseStart_507005 : Nat := 118140960795 + 507005 * 2 ^ 59
def prefixEnd_507005 : Nat := 4983230072969 + 3 ^ 40 * 507005 * 2
def baseEnd_507005 : Nat := 173558172821929382870555

theorem tailTrace_507005 : CollatzResearch.WordTrace tailWord_507005 prefixEnd_507005 173558172821929382870555 := by
  unfold tailWord_507005
  simp only [CollatzResearch.WordTrace]
  refine ⟨18491991528214949405362469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12327994352143299603574979 18491991528214949405362469)
  ·
    refine ⟨3467248411540303013505463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18491991528214949405362469 3467248411540303013505463)
    ·
      refine ⟨5200872617310454520258195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3467248411540303013505463 5200872617310454520258195)
      ·
        refine ⟨7801308925965681780387293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5200872617310454520258195 7801308925965681780387293)
        ·
          refine ⟨2925490847237130667645235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7801308925965681780387293 2925490847237130667645235)
          ·
            refine ⟨4388236270855696001467853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2925490847237130667645235 4388236270855696001467853)
            ·
              refine ⟨1645588601570886000550445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4388236270855696001467853 1645588601570886000550445)
              ·
                refine ⟨617095725589082250206417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1645588601570886000550445 617095725589082250206417)
                ·
                  refine ⟨462821794191811687654813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 617095725589082250206417 462821794191811687654813)
                  ·
                    refine ⟨173558172821929382870555, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 462821794191811687654813 173558172821929382870555)
                    ·
                      rfl

theorem cell22_507005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 3, 3, 2, 3].length) (baseStart_507005 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_507005 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_507005 prefixEnd_507005 := by exact prefixLift 507005
  have htrace : WordTrace (prefixWord ++ tailWord_507005) baseStart_507005 baseEnd_507005 := by
    simpa [prefixWord, tailWord_507005, baseEnd_507005] using wordTrace_append hprefix tailTrace_507005
  have hstable : (prefixWord ++ tailWord_507005).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_507005).length < 2 ^ (prefixWord ++ tailWord_507005).sum := by decide
  have hdescent : baseEnd_507005 < baseStart_507005 := by decide
  rcases family_descends (prefixWord ++ tailWord_507005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_507063 : List Nat := [1, 1, 3, 1, 4, 1, 1, 5, 5]
def baseStart_507063 : Nat := 118140960795 + 507063 * 2 ^ 59
def prefixEnd_507063 : Nat := 4983230072969 + 3 ^ 40 * 507063 * 2
def baseEnd_507063 : Nat := 57859342469078854973459

theorem tailTrace_507063 : CollatzResearch.WordTrace tailWord_507063 prefixEnd_507063 57859342469078854973459 := by
  unfold tailWord_507063
  simp only [CollatzResearch.WordTrace]
  refine ⟨18494106962004825310973843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12329404641336550207315895 18494106962004825310973843)
  ·
    refine ⟨27741160443007237966460765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18494106962004825310973843 27741160443007237966460765)
    ·
      refine ⟨10402935166127714237422787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27741160443007237966460765 10402935166127714237422787)
      ·
        refine ⟨15604402749191571356134181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10402935166127714237422787 15604402749191571356134181)
        ·
          refine ⟨2925825515473419629275159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15604402749191571356134181 2925825515473419629275159)
          ·
            refine ⟨4388738273210129443912739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2925825515473419629275159 4388738273210129443912739)
            ·
              refine ⟨6583107409815194165869109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4388738273210129443912739 6583107409815194165869109)
              ·
                refine ⟨617166319670174453050229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6583107409815194165869109 617166319670174453050229)
                ·
                  refine ⟨57859342469078854973459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 617166319670174453050229 57859342469078854973459)
                  ·
                    rfl

theorem cell22_507063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 1, 5, 5].length) (baseStart_507063 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_507063 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_507063 prefixEnd_507063 := by exact prefixLift 507063
  have htrace : WordTrace (prefixWord ++ tailWord_507063) baseStart_507063 baseEnd_507063 := by
    simpa [prefixWord, tailWord_507063, baseEnd_507063] using wordTrace_append hprefix tailTrace_507063
  have hstable : (prefixWord ++ tailWord_507063).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_507063).length < 2 ^ (prefixWord ++ tailWord_507063).sum := by decide
  have hdescent : baseEnd_507063 < baseStart_507063 := by decide
  rcases family_descends (prefixWord ++ tailWord_507063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_507108 : List Nat := [2, 3, 1, 1, 1, 2, 3, 3, 6]
def baseStart_507108 : Nat := 118140960795 + 507108 * 2 ^ 59
def prefixEnd_507108 : Nat := 4983230072969 + 3 ^ 40 * 507108 * 2
def baseEnd_507108 : Nat := 57864477275623815848413

theorem tailTrace_507108 : CollatzResearch.WordTrace tailWord_507108 prefixEnd_507108 57864477275623815848413 := by
  unfold tailWord_507108
  simp only [CollatzResearch.WordTrace]
  refine ⟨9247874123420898998180989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12330498831227865330907985 9247874123420898998180989)
  ·
    refine ⟨3467952796282837124317871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9247874123420898998180989 3467952796282837124317871)
    ·
      refine ⟨5201929194424255686476807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3467952796282837124317871 5201929194424255686476807)
      ·
        refine ⟨7802893791636383529715211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5201929194424255686476807 7802893791636383529715211)
        ·
          refine ⟨11704340687454575294572817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7802893791636383529715211 11704340687454575294572817)
          ·
            refine ⟨8778255515590931470929613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11704340687454575294572817 8778255515590931470929613)
            ·
              refine ⟨3291845818346599301598605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8778255515590931470929613 3291845818346599301598605)
              ·
                refine ⟨1234442181879974738099477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3291845818346599301598605 1234442181879974738099477)
                ·
                  refine ⟨57864477275623815848413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1234442181879974738099477 57864477275623815848413)
                  ·
                    rfl

theorem cell22_507108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 3, 3, 6].length) (baseStart_507108 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_507108 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_507108 prefixEnd_507108 := by exact prefixLift 507108
  have htrace : WordTrace (prefixWord ++ tailWord_507108) baseStart_507108 baseEnd_507108 := by
    simpa [prefixWord, tailWord_507108, baseEnd_507108] using wordTrace_append hprefix tailTrace_507108
  have hstable : (prefixWord ++ tailWord_507108).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_507108).length < 2 ^ (prefixWord ++ tailWord_507108).sum := by decide
  have hdescent : baseEnd_507108 < baseStart_507108 := by decide
  rcases family_descends (prefixWord ++ tailWord_507108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_507266 : List Nat := [3, 4, 2, 1, 1, 3, 1, 2, 5]
def baseStart_507266 : Nat := 118140960795 + 507266 * 2 ^ 59
def prefixEnd_507266 : Nat := 4983230072969 + 3 ^ 40 * 507266 * 2
def baseEnd_507266 : Nat := 57882506151937234031585

theorem tailTrace_507266 : CollatzResearch.WordTrace tailWord_507266 prefixEnd_507266 57882506151937234031585 := by
  unfold tailWord_507266
  simp only [CollatzResearch.WordTrace]
  refine ⟨4625377745067347745153413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12334340653512927320409101 4625377745067347745153413)
  ·
    refine ⟨867258327200127702216265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4625377745067347745153413 867258327200127702216265)
    ·
      refine ⟨650443745400095776662199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 867258327200127702216265 650443745400095776662199)
      ·
        refine ⟨975665618100143664993299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 650443745400095776662199 975665618100143664993299)
        ·
          refine ⟨1463498427150215497489949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 975665618100143664993299 1463498427150215497489949)
          ·
            refine ⟨548811910181330811558731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1463498427150215497489949 548811910181330811558731)
            ·
              refine ⟨823217865271996217338097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 548811910181330811558731 823217865271996217338097)
              ·
                refine ⟨617413398953997163003573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 823217865271996217338097 617413398953997163003573)
                ·
                  refine ⟨57882506151937234031585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 617413398953997163003573 57882506151937234031585)
                  ·
                    rfl

theorem cell22_507266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 3, 1, 2, 5].length) (baseStart_507266 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_507266 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_507266 prefixEnd_507266 := by exact prefixLift 507266
  have htrace : WordTrace (prefixWord ++ tailWord_507266) baseStart_507266 baseEnd_507266 := by
    simpa [prefixWord, tailWord_507266, baseEnd_507266] using wordTrace_append hprefix tailTrace_507266
  have hstable : (prefixWord ++ tailWord_507266).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_507266).length < 2 ^ (prefixWord ++ tailWord_507266).sum := by decide
  have hdescent : baseEnd_507266 < baseStart_507266 := by decide
  rcases family_descends (prefixWord ++ tailWord_507266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_507290 : List Nat := [3, 1, 1, 4, 1, 1, 1, 1, 3, 6]
def baseStart_507290 : Nat := 118140960795 + 507290 * 2 ^ 59
def prefixEnd_507290 : Nat := 4983230072969 + 3 ^ 40 * 507290 * 2
def baseEnd_507290 : Nat := 173655734146283639494681

theorem tailTrace_507290 : CollatzResearch.WordTrace tailWord_507290 prefixEnd_507290 173655734146283639494681 := by
  unfold tailWord_507290
  simp only [CollatzResearch.WordTrace]
  refine ⟨4625596583045610769871831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12334924221454962052991549 4625596583045610769871831)
  ·
    refine ⟨6938394874568416154807747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4625596583045610769871831 6938394874568416154807747)
    ·
      refine ⟨10407592311852624232211621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6938394874568416154807747 10407592311852624232211621)
      ·
        refine ⟨1951423558472367043539679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10407592311852624232211621 1951423558472367043539679)
        ·
          refine ⟨2927135337708550565309519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1951423558472367043539679 2927135337708550565309519)
          ·
            refine ⟨4390703006562825847964279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2927135337708550565309519 4390703006562825847964279)
            ·
              refine ⟨6586054509844238771946419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4390703006562825847964279 6586054509844238771946419)
              ·
                refine ⟨9879081764766358157919629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6586054509844238771946419 9879081764766358157919629)
                ·
                  refine ⟨3704655661787384309219861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9879081764766358157919629 3704655661787384309219861)
                  ·
                    refine ⟨173655734146283639494681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3704655661787384309219861 173655734146283639494681)
                    ·
                      rfl

theorem cell22_507290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 1, 1, 3, 6].length) (baseStart_507290 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_507290 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_507290 prefixEnd_507290 := by exact prefixLift 507290
  have htrace : WordTrace (prefixWord ++ tailWord_507290) baseStart_507290 baseEnd_507290 := by
    simpa [prefixWord, tailWord_507290, baseEnd_507290] using wordTrace_append hprefix tailTrace_507290
  have hstable : (prefixWord ++ tailWord_507290).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_507290).length < 2 ^ (prefixWord ++ tailWord_507290).sum := by decide
  have hdescent : baseEnd_507290 < baseStart_507290 := by decide
  rcases family_descends (prefixWord ++ tailWord_507290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_507309 : List Nat := [1, 5, 2, 2, 1, 1, 1, 2, 4, 3]
def baseStart_507309 : Nat := 118140960795 + 507309 * 2 ^ 59
def prefixEnd_507309 : Nat := 4983230072969 + 3 ^ 40 * 507309 * 2
def baseEnd_507309 : Nat := 173662238234573923269623

theorem tailTrace_507309 : CollatzResearch.WordTrace tailWord_507309 prefixEnd_507309 173662238234573923269623 := by
  unfold tailWord_507309
  simp only [CollatzResearch.WordTrace]
  refine ⟨18503079319113609324428981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12335386212742406216285987 18503079319113609324428981)
  ·
    refine ⟨1734663686166900874165217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 18503079319113609324428981 1734663686166900874165217)
    ·
      refine ⟨1300997764625175655623913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1734663686166900874165217 1300997764625175655623913)
      ·
        refine ⟨975748323468881741717935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1300997764625175655623913 975748323468881741717935)
        ·
          refine ⟨1463622485203322612576903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 975748323468881741717935 1463622485203322612576903)
          ·
            refine ⟨2195433727804983918865355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1463622485203322612576903 2195433727804983918865355)
            ·
              refine ⟨3293150591707475878298033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2195433727804983918865355 3293150591707475878298033)
              ·
                refine ⟨2469862943780606908723525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3293150591707475878298033 2469862943780606908723525)
                ·
                  refine ⟨463099301958863795385661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2469862943780606908723525 463099301958863795385661)
                  ·
                    refine ⟨173662238234573923269623, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 463099301958863795385661 173662238234573923269623)
                    ·
                      rfl

theorem cell22_507309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 1, 2, 4, 3].length) (baseStart_507309 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_507309 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_507309 prefixEnd_507309 := by exact prefixLift 507309
  have htrace : WordTrace (prefixWord ++ tailWord_507309) baseStart_507309 baseEnd_507309 := by
    simpa [prefixWord, tailWord_507309, baseEnd_507309] using wordTrace_append hprefix tailTrace_507309
  have hstable : (prefixWord ++ tailWord_507309).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_507309).length < 2 ^ (prefixWord ++ tailWord_507309).sum := by decide
  have hdescent : baseEnd_507309 < baseStart_507309 := by decide
  rcases family_descends (prefixWord ++ tailWord_507309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_507324 : List Nat := [2, 2, 2, 4, 2, 1, 1, 2, 2, 4]
def baseStart_507324 : Nat := 118140960795 + 507324 * 2 ^ 59
def prefixEnd_507324 : Nat := 4983230072969 + 3 ^ 40 * 507324 * 2
def baseEnd_507324 : Nat := 173667373041118884144577

theorem tailTrace_507324 : CollatzResearch.WordTrace tailWord_507324 prefixEnd_507324 173667373041118884144577 := by
  unfold tailWord_507324
  simp only [CollatzResearch.WordTrace]
  refine ⟨9251813207029633443112513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12335750942706177924150017 9251813207029633443112513)
  ·
    refine ⟨6938859905272225082334385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9251813207029633443112513 6938859905272225082334385)
    ·
      refine ⟨5204144928954168811750789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6938859905272225082334385 5204144928954168811750789)
      ·
        refine ⟨975777174178906652203273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5204144928954168811750789 975777174178906652203273)
        ·
          refine ⟨731832880634179989152455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 975777174178906652203273 731832880634179989152455)
          ·
            refine ⟨1097749320951269983728683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 731832880634179989152455 1097749320951269983728683)
            ·
              refine ⟨1646623981426904975593025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1097749320951269983728683 1646623981426904975593025)
              ·
                refine ⟨1234967986070178731694769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1646623981426904975593025 1234967986070178731694769)
                ·
                  refine ⟨926225989552634048771077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1234967986070178731694769 926225989552634048771077)
                  ·
                    refine ⟨173667373041118884144577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 926225989552634048771077 173667373041118884144577)
                    ·
                      rfl

theorem cell22_507324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 1, 1, 2, 2, 4].length) (baseStart_507324 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_507324 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_507324 prefixEnd_507324 := by exact prefixLift 507324
  have htrace : WordTrace (prefixWord ++ tailWord_507324) baseStart_507324 baseEnd_507324 := by
    simpa [prefixWord, tailWord_507324, baseEnd_507324] using wordTrace_append hprefix tailTrace_507324
  have hstable : (prefixWord ++ tailWord_507324).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_507324).length < 2 ^ (prefixWord ++ tailWord_507324).sum := by decide
  have hdescent : baseEnd_507324 < baseStart_507324 := by decide
  rcases family_descends (prefixWord ++ tailWord_507324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_507335 : List Nat := [1, 1, 4, 1, 1, 3, 2, 1, 2, 6]
def baseStart_507335 : Nat := 118140960795 + 507335 * 2 ^ 59
def prefixEnd_507335 : Nat := 4983230072969 + 3 ^ 40 * 507335 * 2
def baseEnd_507335 : Nat := 173671138565918522119543

theorem tailTrace_507335 : CollatzResearch.WordTrace tailWord_507335 prefixEnd_507335 173671138565918522119543 := by
  unfold tailWord_507335
  simp only [CollatzResearch.WordTrace]
  refine ⟨18504027617019415764875459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12336018411346277176583639 18504027617019415764875459)
  ·
    refine ⟨27756041425529123647313189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18504027617019415764875459 27756041425529123647313189)
    ·
      refine ⟨5204257767286710683871223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27756041425529123647313189 5204257767286710683871223)
      ·
        refine ⟨7806386650930066025806835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5204257767286710683871223 7806386650930066025806835)
        ·
          refine ⟨11709579976395099038710253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7806386650930066025806835 11709579976395099038710253)
          ·
            refine ⟨4391092491148162139516345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11709579976395099038710253 4391092491148162139516345)
            ·
              refine ⟨3293319368361121604637259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4391092491148162139516345 3293319368361121604637259)
              ·
                refine ⟨4939979052541682406955889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3293319368361121604637259 4939979052541682406955889)
                ·
                  refine ⟨3704984289406261805216917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4939979052541682406955889 3704984289406261805216917)
                  ·
                    refine ⟨173671138565918522119543, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3704984289406261805216917 173671138565918522119543)
                    ·
                      rfl

theorem cell22_507335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 2, 1, 2, 6].length) (baseStart_507335 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_507335 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_507335 prefixEnd_507335 := by exact prefixLift 507335
  have htrace : WordTrace (prefixWord ++ tailWord_507335) baseStart_507335 baseEnd_507335 := by
    simpa [prefixWord, tailWord_507335, baseEnd_507335] using wordTrace_append hprefix tailTrace_507335
  have hstable : (prefixWord ++ tailWord_507335).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_507335).length < 2 ^ (prefixWord ++ tailWord_507335).sum := by decide
  have hdescent : baseEnd_507335 < baseStart_507335 := by decide
  rcases family_descends (prefixWord ++ tailWord_507335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_507442 : List Nat := [3, 2, 1, 1, 2, 1, 1, 3, 4, 4]
def baseStart_507442 : Nat := 118140960795 + 507442 * 2 ^ 59
def prefixEnd_507442 : Nat := 4983230072969 + 3 ^ 40 * 507442 * 2
def baseEnd_507442 : Nat := 173707766852605909694215

theorem tailTrace_507442 : CollatzResearch.WordTrace tailWord_507442 prefixEnd_507442 173707766852605909694215 := by
  unfold tailWord_507442
  simp only [CollatzResearch.WordTrace]
  refine ⟨4626982556907943259755145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12338620151754515359347053 4626982556907943259755145)
  ·
    refine ⟨3470236917680957444816359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4626982556907943259755145 3470236917680957444816359)
    ·
      refine ⟨5205355376521436167224539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3470236917680957444816359 5205355376521436167224539)
      ·
        refine ⟨7808033064782154250836809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5205355376521436167224539 7808033064782154250836809)
        ·
          refine ⟨5856024798586615688127607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7808033064782154250836809 5856024798586615688127607)
          ·
            refine ⟨8784037197879923532191411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5856024798586615688127607 8784037197879923532191411)
            ·
              refine ⟨13176055796819885298287117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8784037197879923532191411 13176055796819885298287117)
              ·
                refine ⟨4941020923807456986857669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13176055796819885298287117 4941020923807456986857669)
                ·
                  refine ⟨926441423213898185035813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4941020923807456986857669 926441423213898185035813)
                  ·
                    refine ⟨173707766852605909694215, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 926441423213898185035813 173707766852605909694215)
                    ·
                      rfl

theorem cell22_507442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 3, 4, 4].length) (baseStart_507442 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_507442 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_507442 prefixEnd_507442 := by exact prefixLift 507442
  have htrace : WordTrace (prefixWord ++ tailWord_507442) baseStart_507442 baseEnd_507442 := by
    simpa [prefixWord, tailWord_507442, baseEnd_507442] using wordTrace_append hprefix tailTrace_507442
  have hstable : (prefixWord ++ tailWord_507442).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_507442).length < 2 ^ (prefixWord ++ tailWord_507442).sum := by decide
  have hdescent : baseEnd_507442 < baseStart_507442 := by decide
  rcases family_descends (prefixWord ++ tailWord_507442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_507446 : List Nat := [5, 1, 2, 1, 3, 1, 2, 1, 6]
def baseStart_507446 : Nat := 118140960795 + 507446 * 2 ^ 59
def prefixEnd_507446 : Nat := 4983230072969 + 3 ^ 40 * 507446 * 2
def baseEnd_507446 : Nat := 57903045378117077531401

theorem tailTrace_507446 : CollatzResearch.WordTrace tailWord_507446 prefixEnd_507446 57903045378117077531401 := by
  unfold tailWord_507446
  simp only [CollatzResearch.WordTrace]
  refine ⟨1156754757476080107635387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 12338717413078187814777461 1156754757476080107635387)
  ·
    refine ⟨1735132136214120161453081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1156754757476080107635387 1735132136214120161453081)
    ·
      refine ⟨1301349102160590121089811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1735132136214120161453081 1301349102160590121089811)
      ·
        refine ⟨1952023653240885181634717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1301349102160590121089811 1952023653240885181634717)
        ·
          refine ⟨732008869965331943113019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1952023653240885181634717 732008869965331943113019)
          ·
            refine ⟨1098013304947997914669529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 732008869965331943113019 1098013304947997914669529)
            ·
              refine ⟨823509978710998436002147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1098013304947997914669529 823509978710998436002147)
              ·
                refine ⟨1235264968066497654003221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 823509978710998436002147 1235264968066497654003221)
                ·
                  refine ⟨57903045378117077531401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1235264968066497654003221 57903045378117077531401)
                  ·
                    rfl

theorem cell22_507446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 1, 2, 1, 6].length) (baseStart_507446 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_507446 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_507446 prefixEnd_507446 := by exact prefixLift 507446
  have htrace : WordTrace (prefixWord ++ tailWord_507446) baseStart_507446 baseEnd_507446 := by
    simpa [prefixWord, tailWord_507446, baseEnd_507446] using wordTrace_append hprefix tailTrace_507446
  have hstable : (prefixWord ++ tailWord_507446).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_507446).length < 2 ^ (prefixWord ++ tailWord_507446).sum := by decide
  have hdescent : baseEnd_507446 < baseStart_507446 := by decide
  rcases family_descends (prefixWord ++ tailWord_507446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_507457 : List Nat := [1, 2, 5, 1, 1, 1, 2, 9]
def baseStart_507457 : Nat := 118140960795 + 507457 * 2 ^ 59
def prefixEnd_507457 : Nat := 4983230072969 + 3 ^ 40 * 507457 * 2
def baseEnd_507457 : Nat := 19301433517683430063241

theorem tailTrace_507457 : CollatzResearch.WordTrace tailWord_507457 prefixEnd_507457 19301433517683430063241 := by
  unfold tailWord_507457
  simp only [CollatzResearch.WordTrace]
  refine ⟨18508477322577430600816625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12338984881718287067211083 18508477322577430600816625)
  ·
    refine ⟨13881357991933072950612469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18508477322577430600816625 13881357991933072950612469)
    ·
      refine ⟨1301377311743725589119919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 13881357991933072950612469 1301377311743725589119919)
      ·
        refine ⟨1952065967615588383679879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1301377311743725589119919 1952065967615588383679879)
        ·
          refine ⟨2928098951423382575519819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1952065967615588383679879 2928098951423382575519819)
          ·
            refine ⟨4392148427135073863279729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2928098951423382575519819 4392148427135073863279729)
            ·
              refine ⟨3294111320351305397459797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4392148427135073863279729 3294111320351305397459797)
              ·
                refine ⟨19301433517683430063241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 3294111320351305397459797 19301433517683430063241)
                ·
                  rfl

theorem cell22_507457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 2, 9].length) (baseStart_507457 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_507457 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_507457 prefixEnd_507457 := by exact prefixLift 507457
  have htrace : WordTrace (prefixWord ++ tailWord_507457) baseStart_507457 baseEnd_507457 := by
    simpa [prefixWord, tailWord_507457, baseEnd_507457] using wordTrace_append hprefix tailTrace_507457
  have hstable : (prefixWord ++ tailWord_507457).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_507457).length < 2 ^ (prefixWord ++ tailWord_507457).sum := by decide
  have hdescent : baseEnd_507457 < baseStart_507457 := by decide
  rcases family_descends (prefixWord ++ tailWord_507457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_507461 : List Nat := [1, 3, 1, 1, 1, 4, 5, 1, 2, 3]
def baseStart_507461 : Nat := 118140960795 + 507461 * 2 ^ 59
def prefixEnd_507461 : Nat := 4983230072969 + 3 ^ 40 * 507461 * 2
def baseEnd_507461 : Nat := 173714270940896193469157

theorem tailTrace_507461 : CollatzResearch.WordTrace tailWord_507461 prefixEnd_507461 173714270940896193469157 := by
  unfold tailWord_507461
  simp only [CollatzResearch.WordTrace]
  refine ⟨18508623214562939283962237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12339082143041959522641491 18508623214562939283962237)
  ·
    refine ⟨6940733705461102231485839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18508623214562939283962237 6940733705461102231485839)
    ·
      refine ⟨10411100558191653347228759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6940733705461102231485839 10411100558191653347228759)
      ·
        refine ⟨15616650837287480020843139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10411100558191653347228759 15616650837287480020843139)
        ·
          refine ⟨23424976255931220031264709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15616650837287480020843139 23424976255931220031264709)
          ·
            refine ⟨4392183047987103755862133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23424976255931220031264709 4392183047987103755862133)
            ·
              refine ⟨411767160748790977112075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4392183047987103755862133 411767160748790977112075)
              ·
                refine ⟨617650741123186465668113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 411767160748790977112075 617650741123186465668113)
                ·
                  refine ⟨463238055842389849251085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 617650741123186465668113 463238055842389849251085)
                  ·
                    refine ⟨173714270940896193469157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 463238055842389849251085 173714270940896193469157)
                    ·
                      rfl

theorem cell22_507461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 5, 1, 2, 3].length) (baseStart_507461 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_507461 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_507461 prefixEnd_507461 := by exact prefixLift 507461
  have htrace : WordTrace (prefixWord ++ tailWord_507461) baseStart_507461 baseEnd_507461 := by
    simpa [prefixWord, tailWord_507461, baseEnd_507461] using wordTrace_append hprefix tailTrace_507461
  have hstable : (prefixWord ++ tailWord_507461).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_507461).length < 2 ^ (prefixWord ++ tailWord_507461).sum := by decide
  have hdescent : baseEnd_507461 < baseStart_507461 := by decide
  rcases family_descends (prefixWord ++ tailWord_507461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_507474 : List Nat := [3, 2, 2, 1, 2, 2, 4, 6]
def baseStart_507474 : Nat := 118140960795 + 507474 * 2 ^ 59
def prefixEnd_507474 : Nat := 4983230072969 + 3 ^ 40 * 507474 * 2
def baseEnd_507474 : Nat := 19302080122952054766013

theorem tailTrace_507474 : CollatzResearch.WordTrace tailWord_507474 prefixEnd_507474 19302080122952054766013 := by
  unfold tailWord_507474
  simp only [CollatzResearch.WordTrace]
  refine ⟨4627274340878960626046369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12339398242343895002790317 4627274340878960626046369)
  ·
    refine ⟨3470455755659220469534777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4627274340878960626046369 3470455755659220469534777)
    ·
      refine ⟨2602841816744415352151083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3470455755659220469534777 2602841816744415352151083)
      ·
        refine ⟨3904262725116623028226625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2602841816744415352151083 3904262725116623028226625)
        ·
          refine ⟨2928197043837467271169969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3904262725116623028226625 2928197043837467271169969)
          ·
            refine ⟨2196147782878100453377477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2928197043837467271169969 2196147782878100453377477)
            ·
              refine ⟨411777709289643835008277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2196147782878100453377477 411777709289643835008277)
              ·
                refine ⟨19302080122952054766013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 411777709289643835008277 19302080122952054766013)
                ·
                  rfl

theorem cell22_507474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 4, 6].length) (baseStart_507474 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_507474 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_507474 prefixEnd_507474 := by exact prefixLift 507474
  have htrace : WordTrace (prefixWord ++ tailWord_507474) baseStart_507474 baseEnd_507474 := by
    simpa [prefixWord, tailWord_507474, baseEnd_507474] using wordTrace_append hprefix tailTrace_507474
  have hstable : (prefixWord ++ tailWord_507474).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_507474).length < 2 ^ (prefixWord ++ tailWord_507474).sum := by decide
  have hdescent : baseEnd_507474 < baseStart_507474 := by decide
  rcases family_descends (prefixWord ++ tailWord_507474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_507506 : List Nat := [3, 2, 1, 2, 3, 1, 3, 1, 3, 3]
def baseStart_507506 : Nat := 118140960795 + 507506 * 2 ^ 59
def prefixEnd_507506 : Nat := 4983230072969 + 3 ^ 40 * 507506 * 2
def baseEnd_507506 : Nat := 173729675360531076094019

theorem tailTrace_507506 : CollatzResearch.WordTrace tailWord_507506 prefixEnd_507506 173729675360531076094019 := by
  unfold tailWord_507506
  simp only [CollatzResearch.WordTrace]
  refine ⟨4627566124849977992337593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12340176332933274646233581 4627566124849977992337593)
  ·
    refine ⟨3470674593637483494253195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4627566124849977992337593 3470674593637483494253195)
    ·
      refine ⟨5206011890456225241379793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3470674593637483494253195 5206011890456225241379793)
      ·
        refine ⟨3904508917842168931034845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5206011890456225241379793 3904508917842168931034845)
        ·
          refine ⟨1464190844190813349138067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3904508917842168931034845 1464190844190813349138067)
          ·
            refine ⟨2196286266286220023707101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1464190844190813349138067 2196286266286220023707101)
            ·
              refine ⟨823607349857332508890163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2196286266286220023707101 823607349857332508890163)
              ·
                refine ⟨1235411024785998763335245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 823607349857332508890163 1235411024785998763335245)
                ·
                  refine ⟨463279134294749536250717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1235411024785998763335245 463279134294749536250717)
                  ·
                    refine ⟨173729675360531076094019, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 463279134294749536250717 173729675360531076094019)
                    ·
                      rfl

theorem cell22_507506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 3, 1, 3, 3].length) (baseStart_507506 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_507506 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_507506 prefixEnd_507506 := by exact prefixLift 507506
  have htrace : WordTrace (prefixWord ++ tailWord_507506) baseStart_507506 baseEnd_507506 := by
    simpa [prefixWord, tailWord_507506, baseEnd_507506] using wordTrace_append hprefix tailTrace_507506
  have hstable : (prefixWord ++ tailWord_507506).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_507506).length < 2 ^ (prefixWord ++ tailWord_507506).sum := by decide
  have hdescent : baseEnd_507506 < baseStart_507506 := by decide
  rcases family_descends (prefixWord ++ tailWord_507506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_507688 : List Nat := [2, 1, 5, 1, 1, 2, 4, 1, 5]
def baseStart_507688 : Nat := 118140960795 + 507688 * 2 ^ 59
def prefixEnd_507688 : Nat := 4983230072969 + 3 ^ 40 * 507688 * 2
def baseEnd_507688 : Nat := 57930659226647756014487

theorem tailTrace_507688 : CollatzResearch.WordTrace tailWord_507688 prefixEnd_507688 57930659226647756014487 := by
  unfold tailWord_507688
  simp only [CollatzResearch.WordTrace]
  refine ⟨9258451292370278526237859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12344601723160371368317145 9258451292370278526237859)
  ·
    refine ⟨13887676938555417789356789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9258451292370278526237859 13887676938555417789356789)
    ·
      refine ⟨1301969712989570417752199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 13887676938555417789356789 1301969712989570417752199)
      ·
        refine ⟨1952954569484355626628299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1301969712989570417752199 1952954569484355626628299)
        ·
          refine ⟨2929431854226533439942449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1952954569484355626628299 2929431854226533439942449)
          ·
            refine ⟨2197073890669900079956837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2929431854226533439942449 2197073890669900079956837)
            ·
              refine ⟨411951354500606264991907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2197073890669900079956837 411951354500606264991907)
              ·
                refine ⟨617927031750909397487861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 411951354500606264991907 617927031750909397487861)
                ·
                  refine ⟨57930659226647756014487, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 617927031750909397487861 57930659226647756014487)
                  ·
                    rfl

theorem cell22_507688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 4, 1, 5].length) (baseStart_507688 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_507688 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_507688 prefixEnd_507688 := by exact prefixLift 507688
  have htrace : WordTrace (prefixWord ++ tailWord_507688) baseStart_507688 baseEnd_507688 := by
    simpa [prefixWord, tailWord_507688, baseEnd_507688] using wordTrace_append hprefix tailTrace_507688
  have hstable : (prefixWord ++ tailWord_507688).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_507688).length < 2 ^ (prefixWord ++ tailWord_507688).sum := by decide
  have hdescent : baseEnd_507688 < baseStart_507688 := by decide
  rcases family_descends (prefixWord ++ tailWord_507688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_507733 : List Nat := [1, 3, 2, 2, 2, 3, 1, 4, 4]
def baseStart_507733 : Nat := 118140960795 + 507733 * 2 ^ 59
def prefixEnd_507733 : Nat := 4983230072969 + 3 ^ 40 * 507733 * 2
def baseEnd_507733 : Nat := 57935794033192716889441

theorem tailTrace_507733 : CollatzResearch.WordTrace tailWord_507733 prefixEnd_507733 57935794033192716889441 := by
  unfold tailWord_507733
  simp only [CollatzResearch.WordTrace]
  refine ⟨18518543869577529737863853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12345695913051686491909235 18518543869577529737863853)
  ·
    refine ⟨6944453951091573651698945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18518543869577529737863853 6944453951091573651698945)
    ·
      refine ⟨5208340463318680238774209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6944453951091573651698945 5208340463318680238774209)
      ·
        refine ⟨3906255347489010179080657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5208340463318680238774209 3906255347489010179080657)
        ·
          refine ⟨2929691510616757634310493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3906255347489010179080657 2929691510616757634310493)
          ·
            refine ⟨1098634316481284112866435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2929691510616757634310493 1098634316481284112866435)
            ·
              refine ⟨1647951474721926169299653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1098634316481284112866435 1647951474721926169299653)
              ·
                refine ⟨308990901510361156743685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1647951474721926169299653 308990901510361156743685)
                ·
                  refine ⟨57935794033192716889441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 308990901510361156743685 57935794033192716889441)
                  ·
                    rfl

theorem cell22_507733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 3, 1, 4, 4].length) (baseStart_507733 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_507733 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_507733 prefixEnd_507733 := by exact prefixLift 507733
  have htrace : WordTrace (prefixWord ++ tailWord_507733) baseStart_507733 baseEnd_507733 := by
    simpa [prefixWord, tailWord_507733, baseEnd_507733] using wordTrace_append hprefix tailTrace_507733
  have hstable : (prefixWord ++ tailWord_507733).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_507733).length < 2 ^ (prefixWord ++ tailWord_507733).sum := by decide
  have hdescent : baseEnd_507733 < baseStart_507733 := by decide
  rcases family_descends (prefixWord ++ tailWord_507733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_507748 : List Nat := [2, 3, 1, 1, 5, 1, 2, 1, 1, 5]
def baseStart_507748 : Nat := 118140960795 + 507748 * 2 ^ 59
def prefixEnd_507748 : Nat := 4983230072969 + 3 ^ 40 * 507748 * 2
def baseEnd_507748 : Nat := 173812516906123111543277

theorem tailTrace_507748 : CollatzResearch.WordTrace tailWord_507748 prefixEnd_507748 173812516906123111543277 := by
  unfold tailWord_507748
  simp only [CollatzResearch.WordTrace]
  refine ⟨9259545482261593649829949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12346060643015458199773265 9259545482261593649829949)
  ·
    refine ⟨3472329555848097618686231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9259545482261593649829949 3472329555848097618686231)
    ·
      refine ⟨5208494333772146428029347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3472329555848097618686231 5208494333772146428029347)
      ·
        refine ⟨7812741500658219642044021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5208494333772146428029347 7812741500658219642044021)
        ·
          refine ⟨732444515686708091441627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 7812741500658219642044021 732444515686708091441627)
          ·
            refine ⟨1098666773530062137162441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 732444515686708091441627 1098666773530062137162441)
            ·
              refine ⟨824000080147546602871831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1098666773530062137162441 824000080147546602871831)
              ·
                refine ⟨1236000120221319904307747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 824000080147546602871831 1236000120221319904307747)
                ·
                  refine ⟨1854000180331979856461621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1236000120221319904307747 1854000180331979856461621)
                  ·
                    refine ⟨173812516906123111543277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1854000180331979856461621 173812516906123111543277)
                    ·
                      rfl

theorem cell22_507748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 1, 2, 1, 1, 5].length) (baseStart_507748 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_507748 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_507748 prefixEnd_507748 := by exact prefixLift 507748
  have htrace : WordTrace (prefixWord ++ tailWord_507748) baseStart_507748 baseEnd_507748 := by
    simpa [prefixWord, tailWord_507748, baseEnd_507748] using wordTrace_append hprefix tailTrace_507748
  have hstable : (prefixWord ++ tailWord_507748).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_507748).length < 2 ^ (prefixWord ++ tailWord_507748).sum := by decide
  have hdescent : baseEnd_507748 < baseStart_507748 := by decide
  rcases family_descends (prefixWord ++ tailWord_507748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_507761 : List Nat := [1, 2, 2, 2, 1, 3, 5, 6]
def baseStart_507761 : Nat := 118140960795 + 507761 * 2 ^ 59
def prefixEnd_507761 : Nat := 4983230072969 + 3 ^ 40 * 507761 * 2
def baseEnd_507761 : Nat := 19312996341310601218693

theorem tailTrace_507761 : CollatzResearch.WordTrace tailWord_507761 prefixEnd_507761 19312996341310601218693 := by
  unfold tailWord_507761
  simp only [CollatzResearch.WordTrace]
  refine ⟨18519565113476090519883137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12346376742317393679922091 18519565113476090519883137)
  ·
    refine ⟨13889673835107067889912353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18519565113476090519883137 13889673835107067889912353)
    ·
      refine ⟨10417255376330300917434265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13889673835107067889912353 10417255376330300917434265)
      ·
        refine ⟨7812941532247725688075699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10417255376330300917434265 7812941532247725688075699)
        ·
          refine ⟨11719412298371588532113549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7812941532247725688075699 11719412298371588532113549)
          ·
            refine ⟨4394779611889345699542581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11719412298371588532113549 4394779611889345699542581)
            ·
              refine ⟨412010588614626159332117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4394779611889345699542581 412010588614626159332117)
              ·
                refine ⟨19312996341310601218693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 412010588614626159332117 19312996341310601218693)
                ·
                  rfl

theorem cell22_507761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 5, 6].length) (baseStart_507761 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_507761 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_507761 prefixEnd_507761 := by exact prefixLift 507761
  have htrace : WordTrace (prefixWord ++ tailWord_507761) baseStart_507761 baseEnd_507761 := by
    simpa [prefixWord, tailWord_507761, baseEnd_507761] using wordTrace_append hprefix tailTrace_507761
  have hstable : (prefixWord ++ tailWord_507761).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_507761).length < 2 ^ (prefixWord ++ tailWord_507761).sum := by decide
  have hdescent : baseEnd_507761 < baseStart_507761 := by decide
  rcases family_descends (prefixWord ++ tailWord_507761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_507776 : List Nat := [2, 1, 1, 2, 1, 2, 3, 2, 5, 3]
def baseStart_507776 : Nat := 118140960795 + 507776 * 2 ^ 59
def prefixEnd_507776 : Nat := 4983230072969 + 3 ^ 40 * 507776 * 2
def baseEnd_507776 : Nat := 173822101878340371843191

theorem tailTrace_507776 : CollatzResearch.WordTrace tailWord_507776 prefixEnd_507776 173822101878340371843191 := by
  unfold tailWord_507776
  simp only [CollatzResearch.WordTrace]
  refine ⟨9260056104210874040839591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12346741472281165387786121 9260056104210874040839591)
  ·
    refine ⟨13890084156316311061259387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9260056104210874040839591 13890084156316311061259387)
    ·
      refine ⟨20835126234474466591889081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13890084156316311061259387 20835126234474466591889081)
      ·
        refine ⟨15626344675855849943916811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20835126234474466591889081 15626344675855849943916811)
        ·
          refine ⟨23439517013783774915875217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15626344675855849943916811 23439517013783774915875217)
          ·
            refine ⟨17579637760337831186906413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23439517013783774915875217 17579637760337831186906413)
            ·
              refine ⟨6592364160126686695089905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17579637760337831186906413 6592364160126686695089905)
              ·
                refine ⟨4944273120095015021317429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6592364160126686695089905 4944273120095015021317429)
                ·
                  refine ⟨463525605008907658248509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4944273120095015021317429 463525605008907658248509)
                  ·
                    refine ⟨173822101878340371843191, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 463525605008907658248509 173822101878340371843191)
                    ·
                      rfl

theorem cell22_507776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 3, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 3, 2, 5, 3].length) (baseStart_507776 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_507776 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_507776 prefixEnd_507776 := by exact prefixLift 507776
  have htrace : WordTrace (prefixWord ++ tailWord_507776) baseStart_507776 baseEnd_507776 := by
    simpa [prefixWord, tailWord_507776, baseEnd_507776] using wordTrace_append hprefix tailTrace_507776
  have hstable : (prefixWord ++ tailWord_507776).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_507776).length < 2 ^ (prefixWord ++ tailWord_507776).sum := by decide
  have hdescent : baseEnd_507776 < baseStart_507776 := by decide
  rcases family_descends (prefixWord ++ tailWord_507776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_507900 : List Nat := [2, 2, 2, 1, 2, 2, 4, 2, 2, 3]
def baseStart_507900 : Nat := 118140960795 + 507900 * 2 ^ 59
def prefixEnd_507900 : Nat := 4983230072969 + 3 ^ 40 * 507900 * 2
def baseEnd_507900 : Nat := 173864549612445381742811

theorem tailTrace_507900 : CollatzResearch.WordTrace tailWord_507900 prefixEnd_507900 173864549612445381742811 := by
  unfold tailWord_507900
  simp only [CollatzResearch.WordTrace]
  refine ⟨9262317429986258629596577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12349756573315011506128769 9262317429986258629596577)
  ·
    refine ⟨6946738072489693972197433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9262317429986258629596577 6946738072489693972197433)
    ·
      refine ⟨5210053554367270479148075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6946738072489693972197433 5210053554367270479148075)
      ·
        refine ⟨7815080331550905718722113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5210053554367270479148075 7815080331550905718722113)
        ·
          refine ⟨5861310248663179289041585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7815080331550905718722113 5861310248663179289041585)
          ·
            refine ⟨4395982686497384466781189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5861310248663179289041585 4395982686497384466781189)
            ·
              refine ⟨824246753718259587521473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4395982686497384466781189 824246753718259587521473)
              ·
                refine ⟨618185065288694690641105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 824246753718259587521473 618185065288694690641105)
                ·
                  refine ⟨463638798966521017980829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 618185065288694690641105 463638798966521017980829)
                  ·
                    refine ⟨173864549612445381742811, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 463638798966521017980829 173864549612445381742811)
                    ·
                      rfl

theorem cell22_507900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 4, 2, 2, 3].length) (baseStart_507900 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_507900 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_507900 prefixEnd_507900 := by exact prefixLift 507900
  have htrace : WordTrace (prefixWord ++ tailWord_507900) baseStart_507900 baseEnd_507900 := by
    simpa [prefixWord, tailWord_507900, baseEnd_507900] using wordTrace_append hprefix tailTrace_507900
  have hstable : (prefixWord ++ tailWord_507900).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_507900).length < 2 ^ (prefixWord ++ tailWord_507900).sum := by decide
  have hdescent : baseEnd_507900 < baseStart_507900 := by decide
  rcases family_descends (prefixWord ++ tailWord_507900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_507902 : List Nat := [4, 2, 2, 2, 1, 2, 1, 4, 4]
def baseStart_507902 : Nat := 118140960795 + 507902 * 2 ^ 59
def prefixEnd_507902 : Nat := 4983230072969 + 3 ^ 40 * 507902 * 2
def baseEnd_507902 : Nat := 57955078084439347730935

theorem tailTrace_507902 : CollatzResearch.WordTrace tailWord_507902 prefixEnd_507902 57955078084439347730935 := by
  unfold tailWord_507902
  simp only [CollatzResearch.WordTrace]
  refine ⟨2315588475745658950095745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12349805203976847733843973 2315588475745658950095745)
  ·
    refine ⟨1736691356809244212571809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2315588475745658950095745 1736691356809244212571809)
    ·
      refine ⟨1302518517606933159428857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1736691356809244212571809 1302518517606933159428857)
      ·
        refine ⟨976888888205199869571643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1302518517606933159428857 976888888205199869571643)
        ·
          refine ⟨1465333332307799804357465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 976888888205199869571643 1465333332307799804357465)
          ·
            refine ⟨1098999999230849853268099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1465333332307799804357465 1098999999230849853268099)
            ·
              refine ⟨1648499998846274779902149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1098999999230849853268099 1648499998846274779902149)
              ·
                refine ⟨309093749783676521231653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1648499998846274779902149 309093749783676521231653)
                ·
                  refine ⟨57955078084439347730935, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 309093749783676521231653 57955078084439347730935)
                  ·
                    rfl

theorem cell22_507902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 2, 1, 4, 4].length) (baseStart_507902 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_507902 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_507902 prefixEnd_507902 := by exact prefixLift 507902
  have htrace : WordTrace (prefixWord ++ tailWord_507902) baseStart_507902 baseEnd_507902 := by
    simpa [prefixWord, tailWord_507902, baseEnd_507902] using wordTrace_append hprefix tailTrace_507902
  have hstable : (prefixWord ++ tailWord_507902).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_507902).length < 2 ^ (prefixWord ++ tailWord_507902).sum := by decide
  have hdescent : baseEnd_507902 < baseStart_507902 := by decide
  rcases family_descends (prefixWord ++ tailWord_507902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_507971 : List Nat := [1, 1, 1, 3, 1, 2, 2, 1, 2, 8]
def baseStart_507971 : Nat := 118140960795 + 507971 * 2 ^ 59
def prefixEnd_507971 : Nat := 4983230072969 + 3 ^ 40 * 507971 * 2
def baseEnd_507971 : Nat := 173888854363424863217593

theorem tailTrace_507971 : CollatzResearch.WordTrace tailWord_507971 prefixEnd_507971 173888854363424863217593 := by
  unfold tailWord_507971
  simp only [CollatzResearch.WordTrace]
  refine ⟨18527224442715296385027767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12351482961810197590018511 18527224442715296385027767)
  ·
    refine ⟨27790836664072944577541651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18527224442715296385027767 27790836664072944577541651)
    ·
      refine ⟨41686254996109416866312477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27790836664072944577541651 41686254996109416866312477)
      ·
        refine ⟨15632345623541031324867179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41686254996109416866312477 15632345623541031324867179)
        ·
          refine ⟨23448518435311546987300769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15632345623541031324867179 23448518435311546987300769)
          ·
            refine ⟨17586388826483660240475577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23448518435311546987300769 17586388826483660240475577)
            ·
              refine ⟨13189791619862745180356683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17586388826483660240475577 13189791619862745180356683)
              ·
                refine ⟨19784687429794117770535025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13189791619862745180356683 19784687429794117770535025)
                ·
                  refine ⟨14838515572345588327901269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19784687429794117770535025 14838515572345588327901269)
                  ·
                    refine ⟨173888854363424863217593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 14838515572345588327901269 173888854363424863217593)
                    ·
                      rfl

theorem cell22_507971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 1, 2, 8].length) (baseStart_507971 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_507971 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_507971 prefixEnd_507971 := by exact prefixLift 507971
  have htrace : WordTrace (prefixWord ++ tailWord_507971) baseStart_507971 baseEnd_507971 := by
    simpa [prefixWord, tailWord_507971, baseEnd_507971] using wordTrace_append hprefix tailTrace_507971
  have hstable : (prefixWord ++ tailWord_507971).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_507971).length < 2 ^ (prefixWord ++ tailWord_507971).sum := by decide
  have hdescent : baseEnd_507971 < baseStart_507971 := by decide
  rcases family_descends (prefixWord ++ tailWord_507971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_507975 : List Nat := [1, 1, 4, 1, 3, 1, 5, 1, 5]
def baseStart_507975 : Nat := 118140960795 + 507975 * 2 ^ 59
def prefixEnd_507975 : Nat := 4983230072969 + 3 ^ 40 * 507975 * 2
def baseEnd_507975 : Nat := 57963407881723395372527

theorem tailTrace_507975 : CollatzResearch.WordTrace tailWord_507975 prefixEnd_507975 57963407881723395372527 := by
  unfold tailWord_507975
  simp only [CollatzResearch.WordTrace]
  refine ⟨18527370334700805068173379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12351580223133870045448919 18527370334700805068173379)
  ·
    refine ⟨27791055502051207602260069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18527370334700805068173379 27791055502051207602260069)
    ·
      refine ⟨5210822906634601425423763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27791055502051207602260069 5210822906634601425423763)
      ·
        refine ⟨7816234359951902138135645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5210822906634601425423763 7816234359951902138135645)
        ·
          refine ⟨2931087884981963301800867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7816234359951902138135645 2931087884981963301800867)
          ·
            refine ⟨4396631827472944952701301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2931087884981963301800867 4396631827472944952701301)
            ·
              refine ⟨412184233825588589315747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4396631827472944952701301 412184233825588589315747)
              ·
                refine ⟨618276350738382883973621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 412184233825588589315747 618276350738382883973621)
                ·
                  refine ⟨57963407881723395372527, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 618276350738382883973621 57963407881723395372527)
                  ·
                    rfl

theorem cell22_507975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 5, 1, 5].length) (baseStart_507975 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_507975 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_507975 prefixEnd_507975 := by exact prefixLift 507975
  have htrace : WordTrace (prefixWord ++ tailWord_507975) baseStart_507975 baseEnd_507975 := by
    simpa [prefixWord, tailWord_507975, baseEnd_507975] using wordTrace_append hprefix tailTrace_507975
  have hstable : (prefixWord ++ tailWord_507975).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_507975).length < 2 ^ (prefixWord ++ tailWord_507975).sum := by decide
  have hdescent : baseEnd_507975 < baseStart_507975 := by decide
  rcases family_descends (prefixWord ++ tailWord_507975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_508005 : List Nat := [1, 3, 1, 3, 2, 2, 2, 3, 1, 4]
def baseStart_508005 : Nat := 118140960795 + 508005 * 2 ^ 59
def prefixEnd_508005 : Nat := 4983230072969 + 3 ^ 40 * 508005 * 2
def baseEnd_508005 : Nat := 173900493258260107867489

theorem tailTrace_508005 : CollatzResearch.WordTrace tailWord_508005 prefixEnd_508005 173900493258260107867489 := by
  unfold tailWord_508005
  simp only [CollatzResearch.WordTrace]
  refine ⟨18528464524592120191765469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12352309683061413461176979 18528464524592120191765469)
  ·
    refine ⟨6948174196722045071912051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18528464524592120191765469 6948174196722045071912051)
    ·
      refine ⟨10422261295083067607868077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6948174196722045071912051 10422261295083067607868077)
      ·
        refine ⟨3908347985656150352950529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10422261295083067607868077 3908347985656150352950529)
        ·
          refine ⟨2931260989242112764712897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3908347985656150352950529 2931260989242112764712897)
          ·
            refine ⟨2198445741931584573534673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2931260989242112764712897 2198445741931584573534673)
            ·
              refine ⟨1648834306448688430151005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2198445741931584573534673 1648834306448688430151005)
              ·
                refine ⟨618312864918258161306627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1648834306448688430151005 618312864918258161306627)
                ·
                  refine ⟨927469297377387241959941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 618312864918258161306627 927469297377387241959941)
                  ·
                    refine ⟨173900493258260107867489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 927469297377387241959941 173900493258260107867489)
                    ·
                      rfl

theorem cell22_508005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 2, 3, 1, 4].length) (baseStart_508005 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_508005 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_508005 prefixEnd_508005 := by exact prefixLift 508005
  have htrace : WordTrace (prefixWord ++ tailWord_508005) baseStart_508005 baseEnd_508005 := by
    simpa [prefixWord, tailWord_508005, baseEnd_508005] using wordTrace_append hprefix tailTrace_508005
  have hstable : (prefixWord ++ tailWord_508005).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_508005).length < 2 ^ (prefixWord ++ tailWord_508005).sum := by decide
  have hdescent : baseEnd_508005 < baseStart_508005 := by decide
  rcases family_descends (prefixWord ++ tailWord_508005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_508071 : List Nat := [1, 1, 6, 2, 2, 2, 2, 2, 4]
def baseStart_508071 : Nat := 118140960795 + 508071 * 2 ^ 59
def prefixEnd_508071 : Nat := 4983230072969 + 3 ^ 40 * 508071 * 2
def baseEnd_508071 : Nat := 57974362135685978572429

theorem tailTrace_508071 : CollatzResearch.WordTrace tailWord_508071 prefixEnd_508071 57974362135685978572429 := by
  unfold tailWord_508071
  simp only [CollatzResearch.WordTrace]
  refine ⟨18530871742353013463668067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12353914494902008975778711 18530871742353013463668067)
  ·
    refine ⟨27796307613529520195502101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18530871742353013463668067 27796307613529520195502101)
    ·
      refine ⟨1302951919384196259164161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 27796307613529520195502101 1302951919384196259164161)
      ·
        refine ⟨977213939538147194373121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1302951919384196259164161 977213939538147194373121)
        ·
          refine ⟨732910454653610395779841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 977213939538147194373121 732910454653610395779841)
          ·
            refine ⟨549682840990207796834881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 732910454653610395779841 549682840990207796834881)
            ·
              refine ⟨412262130742655847626161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 549682840990207796834881 412262130742655847626161)
              ·
                refine ⟨309196598056991885719621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 412262130742655847626161 309196598056991885719621)
                ·
                  refine ⟨57974362135685978572429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 309196598056991885719621 57974362135685978572429)
                  ·
                    rfl

theorem cell22_508071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 2, 2, 2, 4].length) (baseStart_508071 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_508071 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_508071 prefixEnd_508071 := by exact prefixLift 508071
  have htrace : WordTrace (prefixWord ++ tailWord_508071) baseStart_508071 baseEnd_508071 := by
    simpa [prefixWord, tailWord_508071, baseEnd_508071] using wordTrace_append hprefix tailTrace_508071
  have hstable : (prefixWord ++ tailWord_508071).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_508071).length < 2 ^ (prefixWord ++ tailWord_508071).sum := by decide
  have hdescent : baseEnd_508071 < baseStart_508071 := by decide
  rcases family_descends (prefixWord ++ tailWord_508071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_508093 : List Nat := [1, 4, 1, 2, 1, 1, 1, 2, 9]
def baseStart_508093 : Nat := 118140960795 + 508093 * 2 ^ 59
def prefixEnd_508093 : Nat := 4983230072969 + 3 ^ 40 * 508093 * 2
def baseEnd_508093 : Nat := 57976872485552403889073

theorem tailTrace_508093 : CollatzResearch.WordTrace tailWord_508093 prefixEnd_508093 57976872485552403889073 := by
  unfold tailWord_508093
  simp only [CollatzResearch.WordTrace]
  refine ⟨18531674148273311220968933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12354449432182207480645955 18531674148273311220968933)
  ·
    refine ⟨3474688902801245853931675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18531674148273311220968933 3474688902801245853931675)
    ·
      refine ⟨5212033354201868780897513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3474688902801245853931675 5212033354201868780897513)
      ·
        refine ⟨3909025015651401585673135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5212033354201868780897513 3909025015651401585673135)
        ·
          refine ⟨5863537523477102378509703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3909025015651401585673135 5863537523477102378509703)
          ·
            refine ⟨8795306285215653567764555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5863537523477102378509703 8795306285215653567764555)
            ·
              refine ⟨13192959427823480351646833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8795306285215653567764555 13192959427823480351646833)
              ·
                refine ⟨9894719570867610263735125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13192959427823480351646833 9894719570867610263735125)
                ·
                  refine ⟨57976872485552403889073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 9894719570867610263735125 57976872485552403889073)
                  ·
                    rfl

theorem cell22_508093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 2, 9].length) (baseStart_508093 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_508093 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_508093 prefixEnd_508093 := by exact prefixLift 508093
  have htrace : WordTrace (prefixWord ++ tailWord_508093) baseStart_508093 baseEnd_508093 := by
    simpa [prefixWord, tailWord_508093, baseEnd_508093] using wordTrace_append hprefix tailTrace_508093
  have hstable : (prefixWord ++ tailWord_508093).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_508093).length < 2 ^ (prefixWord ++ tailWord_508093).sum := by decide
  have hdescent : baseEnd_508093 < baseStart_508093 := by decide
  rcases family_descends (prefixWord ++ tailWord_508093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_508114 : List Nat := [3, 2, 2, 2, 1, 2, 1, 5, 1, 3]
def baseStart_508114 : Nat := 118140960795 + 508114 * 2 ^ 59
def prefixEnd_508114 : Nat := 4983230072969 + 3 ^ 40 * 508114 * 2
def baseEnd_508114 : Nat := 173937806185820156892155

theorem tailTrace_508114 : CollatzResearch.WordTrace tailWord_508114 prefixEnd_508114 173937806185820156892155 := by
  unfold tailWord_508114
  simp only [CollatzResearch.WordTrace]
  refine ⟨4633110020299307951870849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12354960054131487871655597 4633110020299307951870849)
  ·
    refine ⟨3474832515224480963903137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4633110020299307951870849 3474832515224480963903137)
    ·
      refine ⟨2606124386418360722927353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3474832515224480963903137 2606124386418360722927353)
      ·
        refine ⟨1954593289813770542195515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2606124386418360722927353 1954593289813770542195515)
        ·
          refine ⟨2931889934720655813293273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1954593289813770542195515 2931889934720655813293273)
          ·
            refine ⟨2198917451040491859969955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2931889934720655813293273 2198917451040491859969955)
            ·
              refine ⟨3298376176560737789954933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2198917451040491859969955 3298376176560737789954933)
              ·
                refine ⟨309222766552569167808275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3298376176560737789954933 309222766552569167808275)
                ·
                  refine ⟨463834149828853751712413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 309222766552569167808275 463834149828853751712413)
                  ·
                    refine ⟨173937806185820156892155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 463834149828853751712413 173937806185820156892155)
                    ·
                      rfl

theorem cell22_508114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 1, 5, 1, 3].length) (baseStart_508114 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_508114 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_508114 prefixEnd_508114 := by exact prefixLift 508114
  have htrace : WordTrace (prefixWord ++ tailWord_508114) baseStart_508114 baseEnd_508114 := by
    simpa [prefixWord, tailWord_508114, baseEnd_508114] using wordTrace_append hprefix tailTrace_508114
  have hstable : (prefixWord ++ tailWord_508114).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_508114).length < 2 ^ (prefixWord ++ tailWord_508114).sum := by decide
  have hdescent : baseEnd_508114 < baseStart_508114 := by decide
  rcases family_descends (prefixWord ++ tailWord_508114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_508170 : List Nat := [3, 1, 2, 2, 1, 1, 2, 4, 1, 5]
def baseStart_508170 : Nat := 118140960795 + 508170 * 2 ^ 59
def prefixEnd_508170 : Nat := 4983230072969 + 3 ^ 40 * 508170 * 2
def baseEnd_508170 : Nat := 173956976130254677491983

theorem tailTrace_508170 : CollatzResearch.WordTrace tailWord_508170 prefixEnd_508170 173956976130254677491983 := by
  unfold tailWord_508170
  simp only [CollatzResearch.WordTrace]
  refine ⟨4633620642248588342880491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12356321712662902247681309 4633620642248588342880491)
  ·
    refine ⟨6950430963372882514320737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4633620642248588342880491 6950430963372882514320737)
    ·
      refine ⟨5212823222529661885740553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6950430963372882514320737 5212823222529661885740553)
      ·
        refine ⟨3909617416897246414305415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5212823222529661885740553 3909617416897246414305415)
        ·
          refine ⟨5864426125345869621458123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3909617416897246414305415 5864426125345869621458123)
          ·
            refine ⟨8796639188018804432187185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5864426125345869621458123 8796639188018804432187185)
            ·
              refine ⟨6597479391014103324140389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8796639188018804432187185 6597479391014103324140389)
              ·
                refine ⟨1237027385815144373276323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6597479391014103324140389 1237027385815144373276323)
                ·
                  refine ⟨1855541078722716559914485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1237027385815144373276323 1855541078722716559914485)
                  ·
                    refine ⟨173956976130254677491983, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1855541078722716559914485 173956976130254677491983)
                    ·
                      rfl

theorem cell22_508170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 2, 4, 1, 5].length) (baseStart_508170 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_508170 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_508170 prefixEnd_508170 := by exact prefixLift 508170
  have htrace : WordTrace (prefixWord ++ tailWord_508170) baseStart_508170 baseEnd_508170 := by
    simpa [prefixWord, tailWord_508170, baseEnd_508170] using wordTrace_append hprefix tailTrace_508170
  have hstable : (prefixWord ++ tailWord_508170).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_508170).length < 2 ^ (prefixWord ++ tailWord_508170).sum := by decide
  have hdescent : baseEnd_508170 < baseStart_508170 := by decide
  rcases family_descends (prefixWord ++ tailWord_508170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_508189 : List Nat := [1, 4, 2, 3, 2, 2, 1, 1, 6]
def baseStart_508189 : Nat := 118140960795 + 508189 * 2 ^ 59
def prefixEnd_508189 : Nat := 4983230072969 + 3 ^ 40 * 508189 * 2
def baseEnd_508189 : Nat := 57987826739514987088975

theorem tailTrace_508189 : CollatzResearch.WordTrace tailWord_508189 prefixEnd_508189 57987826739514987088975 := by
  unfold tailWord_508189
  simp only [CollatzResearch.WordTrace]
  refine ⟨18535175555925519616463621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12356783703950346410975747 18535175555925519616463621)
  ·
    refine ⟨3475345416736034928086929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18535175555925519616463621 3475345416736034928086929)
    ·
      refine ⟨2606509062552026196065197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3475345416736034928086929 2606509062552026196065197)
      ·
        refine ⟨977440898457009823524449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2606509062552026196065197 977440898457009823524449)
        ·
          refine ⟨733080673842757367643337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 977440898457009823524449 733080673842757367643337)
          ·
            refine ⟨549810505382068025732503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 733080673842757367643337 549810505382068025732503)
            ·
              refine ⟨824715758073102038598755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 549810505382068025732503 824715758073102038598755)
              ·
                refine ⟨1237073637109653057898133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 824715758073102038598755 1237073637109653057898133)
                ·
                  refine ⟨57987826739514987088975, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1237073637109653057898133 57987826739514987088975)
                  ·
                    rfl

theorem cell22_508189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 2, 1, 1, 6].length) (baseStart_508189 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_508189 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_508189 prefixEnd_508189 := by exact prefixLift 508189
  have htrace : WordTrace (prefixWord ++ tailWord_508189) baseStart_508189 baseEnd_508189 := by
    simpa [prefixWord, tailWord_508189, baseEnd_508189] using wordTrace_append hprefix tailTrace_508189
  have hstable : (prefixWord ++ tailWord_508189).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_508189).length < 2 ^ (prefixWord ++ tailWord_508189).sum := by decide
  have hdescent : baseEnd_508189 < baseStart_508189 := by decide
  rcases family_descends (prefixWord ++ tailWord_508189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_508204 : List Nat := [2, 2, 1, 1, 1, 3, 6, 1, 2, 3]
def baseStart_508204 : Nat := 118140960795 + 508204 * 2 ^ 59
def prefixEnd_508204 : Nat := 4983230072969 + 3 ^ 40 * 508204 * 2
def baseEnd_508204 : Nat := 173968615025089922141879

theorem tailTrace_508204 : CollatzResearch.WordTrace tailWord_508204 prefixEnd_508204 173968615025089922141879 := by
  unfold tailWord_508204
  simp only [CollatzResearch.WordTrace]
  refine ⟨9267861325435588589129833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12357148433914118118839777 9267861325435588589129833)
  ·
    refine ⟨6950895994076691441847375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9267861325435588589129833 6950895994076691441847375)
    ·
      refine ⟨10426343991115037162771063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6950895994076691441847375 10426343991115037162771063)
      ·
        refine ⟨15639515986672555744156595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10426343991115037162771063 15639515986672555744156595)
        ·
          refine ⟨23459273980008833616234893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15639515986672555744156595 23459273980008833616234893)
          ·
            refine ⟨8797227742503312606088085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23459273980008833616234893 8797227742503312606088085)
            ·
              refine ⟨412370050429842778410379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 8797227742503312606088085 412370050429842778410379)
              ·
                refine ⟨618555075644764167615569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 412370050429842778410379 618555075644764167615569)
                ·
                  refine ⟨463916306733573125711677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 618555075644764167615569 463916306733573125711677)
                  ·
                    refine ⟨173968615025089922141879, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 463916306733573125711677 173968615025089922141879)
                    ·
                      rfl

theorem cell22_508204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 2, 3].length) (baseStart_508204 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_508204 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_508204 prefixEnd_508204 := by exact prefixLift 508204
  have htrace : WordTrace (prefixWord ++ tailWord_508204) baseStart_508204 baseEnd_508204 := by
    simpa [prefixWord, tailWord_508204, baseEnd_508204] using wordTrace_append hprefix tailTrace_508204
  have hstable : (prefixWord ++ tailWord_508204).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_508204).length < 2 ^ (prefixWord ++ tailWord_508204).sum := by decide
  have hdescent : baseEnd_508204 < baseStart_508204 := by decide
  rcases family_descends (prefixWord ++ tailWord_508204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_508337 : List Nat := [1, 2, 2, 4, 1, 2, 2, 1, 1, 6]
def baseStart_508337 : Nat := 118140960795 + 508337 * 2 ^ 59
def prefixEnd_508337 : Nat := 4983230072969 + 3 ^ 40 * 508337 * 2
def baseEnd_508337 : Nat := 174014143643121908566471

theorem tailTrace_508337 : CollatzResearch.WordTrace tailWord_508337 prefixEnd_508337 174014143643121908566471 := by
  unfold tailWord_508337
  simp only [CollatzResearch.WordTrace]
  refine ⟨18540573559389340892851265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12360382372926227261900843 18540573559389340892851265)
  ·
    refine ⟨13905430169542005669638449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18540573559389340892851265 13905430169542005669638449)
    ·
      refine ⟨10429072627156504252228837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13905430169542005669638449 10429072627156504252228837)
      ·
        refine ⟨1955451117591844547292907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10429072627156504252228837 1955451117591844547292907)
        ·
          refine ⟨2933176676387766820939361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1955451117591844547292907 2933176676387766820939361)
          ·
            refine ⟨2199882507290825115704521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2933176676387766820939361 2199882507290825115704521)
            ·
              refine ⟨1649911880468118836778391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2199882507290825115704521 1649911880468118836778391)
              ·
                refine ⟨2474867820702178255167587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1649911880468118836778391 2474867820702178255167587)
                ·
                  refine ⟨3712301731053267382751381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2474867820702178255167587 3712301731053267382751381)
                  ·
                    refine ⟨174014143643121908566471, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3712301731053267382751381 174014143643121908566471)
                    ·
                      rfl

theorem cell22_508337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 2, 1, 1, 6].length) (baseStart_508337 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_508337 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_508337 prefixEnd_508337 := by exact prefixLift 508337
  have htrace : WordTrace (prefixWord ++ tailWord_508337) baseStart_508337 baseEnd_508337 := by
    simpa [prefixWord, tailWord_508337, baseEnd_508337] using wordTrace_append hprefix tailTrace_508337
  have hstable : (prefixWord ++ tailWord_508337).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_508337).length < 2 ^ (prefixWord ++ tailWord_508337).sum := by decide
  have hdescent : baseEnd_508337 < baseStart_508337 := by decide
  rcases family_descends (prefixWord ++ tailWord_508337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_508373 : List Nat := [1, 3, 2, 3, 1, 4, 2, 1, 2, 3]
def baseStart_508373 : Nat := 118140960795 + 508373 * 2 ^ 59
def prefixEnd_508373 : Nat := 4983230072969 + 3 ^ 40 * 508373 * 2
def baseEnd_508373 : Nat := 174026467178829814666361

theorem tailTrace_508373 : CollatzResearch.WordTrace tailWord_508373 prefixEnd_508373 174026467178829814666361 := by
  unfold tailWord_508373
  simp only [CollatzResearch.WordTrace]
  refine ⟨18541886587258919041161773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12361257724839279360774515 18541886587258919041161773)
  ·
    refine ⟨6953207470222094640435665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18541886587258919041161773 6953207470222094640435665)
    ·
      refine ⟨5214905602666570980326749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6953207470222094640435665 5214905602666570980326749)
      ·
        refine ⟨1955589600999964117622531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5214905602666570980326749 1955589600999964117622531)
        ·
          refine ⟨2933384401499946176433797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1955589600999964117622531 2933384401499946176433797)
          ·
            refine ⟨550009575281239908081337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2933384401499946176433797 550009575281239908081337)
            ·
              refine ⟨412507181460929931061003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 550009575281239908081337 412507181460929931061003)
              ·
                refine ⟨618760772191394896591505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 412507181460929931061003 618760772191394896591505)
                ·
                  refine ⟨464070579143546172443629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 618760772191394896591505 464070579143546172443629)
                  ·
                    refine ⟨174026467178829814666361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 464070579143546172443629 174026467178829814666361)
                    ·
                      rfl

theorem cell22_508373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 4, 2, 1, 2, 3].length) (baseStart_508373 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_508373 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_508373 prefixEnd_508373 := by exact prefixLift 508373
  have htrace : WordTrace (prefixWord ++ tailWord_508373) baseStart_508373 baseEnd_508373 := by
    simpa [prefixWord, tailWord_508373, baseEnd_508373] using wordTrace_append hprefix tailTrace_508373
  have hstable : (prefixWord ++ tailWord_508373).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_508373).length < 2 ^ (prefixWord ++ tailWord_508373).sum := by decide
  have hdescent : baseEnd_508373 < baseStart_508373 := by decide
  rcases family_descends (prefixWord ++ tailWord_508373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_508401 : List Nat := [1, 2, 2, 2, 3, 1, 2, 5, 1, 3]
def baseStart_508401 : Nat := 118140960795 + 508401 * 2 ^ 59
def prefixEnd_508401 : Nat := 4983230072969 + 3 ^ 40 * 508401 * 2
def baseEnd_508401 : Nat := 174036052151047074966275

theorem tailTrace_508401 : CollatzResearch.WordTrace tailWord_508401 prefixEnd_508401 174036052151047074966275 := by
  unfold tailWord_508401
  simp only [CollatzResearch.WordTrace]
  refine ⟨18542907831157479823181057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12361938554104986548787371 18542907831157479823181057)
  ·
    refine ⟨13907180873368109867385793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18542907831157479823181057 13907180873368109867385793)
    ·
      refine ⟨10430385655026082400539345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13907180873368109867385793 10430385655026082400539345)
      ·
        refine ⟨7822789241269561800404509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10430385655026082400539345 7822789241269561800404509)
        ·
          refine ⟨2933545965476085675151691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7822789241269561800404509 2933545965476085675151691)
          ·
            refine ⟨4400318948214128512727537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2933545965476085675151691 4400318948214128512727537)
            ·
              refine ⟨3300239211160596384545653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4400318948214128512727537 3300239211160596384545653)
              ·
                refine ⟨309397426046305911051155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3300239211160596384545653 309397426046305911051155)
                ·
                  refine ⟨464096139069458866576733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 309397426046305911051155 464096139069458866576733)
                  ·
                    refine ⟨174036052151047074966275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 464096139069458866576733 174036052151047074966275)
                    ·
                      rfl

theorem cell22_508401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 2, 5, 1, 3].length) (baseStart_508401 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_508401 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_508401 prefixEnd_508401 := by exact prefixLift 508401
  have htrace : WordTrace (prefixWord ++ tailWord_508401) baseStart_508401 baseEnd_508401 := by
    simpa [prefixWord, tailWord_508401, baseEnd_508401] using wordTrace_append hprefix tailTrace_508401
  have hstable : (prefixWord ++ tailWord_508401).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_508401).length < 2 ^ (prefixWord ++ tailWord_508401).sum := by decide
  have hdescent : baseEnd_508401 < baseStart_508401 := by decide
  rcases family_descends (prefixWord ++ tailWord_508401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_508412 : List Nat := [2, 2, 2, 1, 2, 1, 1, 4, 2, 5]
def baseStart_508412 : Nat := 118140960795 + 508412 * 2 ^ 59
def prefixEnd_508412 : Nat := 4983230072969 + 3 ^ 40 * 508412 * 2
def baseEnd_508412 : Nat := 174039817675846712941241

theorem tailTrace_508412 : CollatzResearch.WordTrace tailWord_508412 prefixEnd_508412 174039817675846712941241 := by
  unfold tailWord_508412
  simp only [CollatzResearch.WordTrace]
  refine ⟨9271654517058814350915745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12362206022745085801220993 9271654517058814350915745)
  ·
    refine ⟨6953740887794110763186809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9271654517058814350915745 6953740887794110763186809)
    ·
      refine ⟨5215305665845583072390107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6953740887794110763186809 5215305665845583072390107)
      ·
        refine ⟨7822958498768374608585161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5215305665845583072390107 7822958498768374608585161)
        ·
          refine ⟨5867218874076280956438871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7822958498768374608585161 5867218874076280956438871)
          ·
            refine ⟨8800828311114421434658307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5867218874076280956438871 8800828311114421434658307)
            ·
              refine ⟨13201242466671632151987461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8800828311114421434658307 13201242466671632151987461)
              ·
                refine ⟨2475232962500931028497649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13201242466671632151987461 2475232962500931028497649)
                ·
                  refine ⟨1856424721875698271373237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2475232962500931028497649 1856424721875698271373237)
                  ·
                    refine ⟨174039817675846712941241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1856424721875698271373237 174039817675846712941241)
                    ·
                      rfl

theorem cell22_508412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 4, 2, 5].length) (baseStart_508412 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_508412 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_508412 prefixEnd_508412 := by exact prefixLift 508412
  have htrace : WordTrace (prefixWord ++ tailWord_508412) baseStart_508412 baseEnd_508412 := by
    simpa [prefixWord, tailWord_508412, baseEnd_508412] using wordTrace_append hprefix tailTrace_508412
  have hstable : (prefixWord ++ tailWord_508412).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_508412).length < 2 ^ (prefixWord ++ tailWord_508412).sum := by decide
  have hdescent : baseEnd_508412 < baseStart_508412 := by decide
  rcases family_descends (prefixWord ++ tailWord_508412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_508442 : List Nat := [3, 1, 1, 3, 1, 1, 3, 1, 8]
def baseStart_508442 : Nat := 118140960795 + 508442 * 2 ^ 59
def prefixEnd_508442 : Nat := 4983230072969 + 3 ^ 40 * 508442 * 2
def baseEnd_508442 : Nat := 58016695762978878230383

theorem tailTrace_508442 : CollatzResearch.WordTrace tailWord_508442 prefixEnd_508442 58016695762978878230383 := by
  unfold tailWord_508442
  simp only [CollatzResearch.WordTrace]
  refine ⟨4636100806002235956355895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12362935482672629216949053 4636100806002235956355895)
  ·
    refine ⟨6954151209003353934533843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4636100806002235956355895 6954151209003353934533843)
    ·
      refine ⟨10431226813505030901800765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6954151209003353934533843 10431226813505030901800765)
      ·
        refine ⟨3911710055064386588175287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10431226813505030901800765 3911710055064386588175287)
        ·
          refine ⟨5867565082596579882262931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3911710055064386588175287 5867565082596579882262931)
          ·
            refine ⟨8801347623894869823394397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5867565082596579882262931 8801347623894869823394397)
            ·
              refine ⟨3300505358960576183772899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8801347623894869823394397 3300505358960576183772899)
              ·
                refine ⟨4950758038440864275659349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3300505358960576183772899 4950758038440864275659349)
                ·
                  refine ⟨58016695762978878230383, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 4950758038440864275659349 58016695762978878230383)
                  ·
                    rfl

theorem cell22_508442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 3, 1, 8].length) (baseStart_508442 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_508442 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_508442 prefixEnd_508442 := by exact prefixLift 508442
  have htrace : WordTrace (prefixWord ++ tailWord_508442) baseStart_508442 baseEnd_508442 := by
    simpa [prefixWord, tailWord_508442, baseEnd_508442] using wordTrace_append hprefix tailTrace_508442
  have hstable : (prefixWord ++ tailWord_508442).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_508442).length < 2 ^ (prefixWord ++ tailWord_508442).sum := by decide
  have hdescent : baseEnd_508442 < baseStart_508442 := by decide
  rcases family_descends (prefixWord ++ tailWord_508442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_508444 : List Nat := [2, 2, 3, 1, 2, 2, 2, 1, 3, 4]
def baseStart_508444 : Nat := 118140960795 + 508444 * 2 ^ 59
def prefixEnd_508444 : Nat := 4983230072969 + 3 ^ 40 * 508444 * 2
def baseEnd_508444 : Nat := 174050771929809296141143

theorem tailTrace_508444 : CollatzResearch.WordTrace tailWord_508444 prefixEnd_508444 174050771929809296141143 := by
  unfold tailWord_508444
  simp only [CollatzResearch.WordTrace]
  refine ⟨9272238085000849083498193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12362984113334465444664257 9272238085000849083498193)
  ·
    refine ⟨6954178563750636812623645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9272238085000849083498193 6954178563750636812623645)
    ·
      refine ⟨2607816961406488804733867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6954178563750636812623645 2607816961406488804733867)
      ·
        refine ⟨3911725442109733207100801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2607816961406488804733867 3911725442109733207100801)
        ·
          refine ⟨2933794081582299905325601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3911725442109733207100801 2933794081582299905325601)
          ·
            refine ⟨2200345561186724928994201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2933794081582299905325601 2200345561186724928994201)
            ·
              refine ⟨1650259170890043696745651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2200345561186724928994201 1650259170890043696745651)
              ·
                refine ⟨2475388756335065545118477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1650259170890043696745651 2475388756335065545118477)
                ·
                  refine ⟨928270783625649579419429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2475388756335065545118477 928270783625649579419429)
                  ·
                    refine ⟨174050771929809296141143, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 928270783625649579419429 174050771929809296141143)
                    ·
                      rfl

theorem cell22_508444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 2, 1, 3, 4].length) (baseStart_508444 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_508444 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_508444 prefixEnd_508444 := by exact prefixLift 508444
  have htrace : WordTrace (prefixWord ++ tailWord_508444) baseStart_508444 baseEnd_508444 := by
    simpa [prefixWord, tailWord_508444, baseEnd_508444] using wordTrace_append hprefix tailTrace_508444
  have hstable : (prefixWord ++ tailWord_508444).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_508444).length < 2 ^ (prefixWord ++ tailWord_508444).sum := by decide
  have hdescent : baseEnd_508444 < baseStart_508444 := by decide
  rcases family_descends (prefixWord ++ tailWord_508444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_508476 : List Nat := [2, 2, 2, 2, 3, 1, 2, 4, 4]
def baseStart_508476 : Nat := 118140960795 + 508476 * 2 ^ 59
def prefixEnd_508476 : Nat := 4983230072969 + 3 ^ 40 * 508476 * 2
def baseEnd_508476 : Nat := 58020575394590626447015

theorem tailTrace_508476 : CollatzResearch.WordTrace tailWord_508476 prefixEnd_508476 58020575394590626447015 := by
  unfold tailWord_508476
  simp only [CollatzResearch.WordTrace]
  refine ⟨9272821652942883816080641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12363762203923845088107521 9272821652942883816080641)
  ·
    refine ⟨6954616239707162862060481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9272821652942883816080641 6954616239707162862060481)
    ·
      refine ⟨5215962179780372146545361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6954616239707162862060481 5215962179780372146545361)
      ·
        refine ⟨3911971634835279109909021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5215962179780372146545361 3911971634835279109909021)
        ·
          refine ⟨1466989363063229666215883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3911971634835279109909021 1466989363063229666215883)
          ·
            refine ⟨2200484044594844499323825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1466989363063229666215883 2200484044594844499323825)
            ·
              refine ⟨1650363033446133374492869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2200484044594844499323825 1650363033446133374492869)
              ·
                refine ⟨309443068771150007717413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1650363033446133374492869 309443068771150007717413)
                ·
                  refine ⟨58020575394590626447015, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 309443068771150007717413 58020575394590626447015)
                  ·
                    rfl

theorem cell22_508476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 2, 4, 4].length) (baseStart_508476 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_508476 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_508476 prefixEnd_508476 := by exact prefixLift 508476
  have htrace : WordTrace (prefixWord ++ tailWord_508476) baseStart_508476 baseEnd_508476 := by
    simpa [prefixWord, tailWord_508476, baseEnd_508476] using wordTrace_append hprefix tailTrace_508476
  have hstable : (prefixWord ++ tailWord_508476).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_508476).length < 2 ^ (prefixWord ++ tailWord_508476).sum := by decide
  have hdescent : baseEnd_508476 < baseStart_508476 := by decide
  rcases family_descends (prefixWord ++ tailWord_508476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_508504 : List Nat := [2, 1, 2, 2, 1, 2, 6, 6]
def baseStart_508504 : Nat := 118140960795 + 508504 * 2 ^ 59
def prefixEnd_508504 : Nat := 4983230072969 + 3 ^ 40 * 508504 * 2
def baseEnd_508504 : Nat := 19341256795109904404551

theorem tailTrace_508504 : CollatzResearch.WordTrace tailWord_508504 prefixEnd_508504 19341256795109904404551 := by
  unfold tailWord_508504
  simp only [CollatzResearch.WordTrace]
  refine ⟨9273332274892164207090283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12364443033189552276120377 9273332274892164207090283)
  ·
    refine ⟨13909998412338246310635425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9273332274892164207090283 13909998412338246310635425)
    ·
      refine ⟨10432498809253684732976569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13909998412338246310635425 10432498809253684732976569)
      ·
        refine ⟨7824374106940263549732427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10432498809253684732976569 7824374106940263549732427)
        ·
          refine ⟨11736561160410395324598641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7824374106940263549732427 11736561160410395324598641)
          ·
            refine ⟨8802420870307796493448981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11736561160410395324598641 8802420870307796493448981)
            ·
              refine ⟨412613478295677960630421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 8802420870307796493448981 412613478295677960630421)
              ·
                refine ⟨19341256795109904404551, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 412613478295677960630421 19341256795109904404551)
                ·
                  rfl

theorem cell22_508504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 6, 6].length) (baseStart_508504 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_508504 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_508504 prefixEnd_508504 := by exact prefixLift 508504
  have htrace : WordTrace (prefixWord ++ tailWord_508504) baseStart_508504 baseEnd_508504 := by
    simpa [prefixWord, tailWord_508504, baseEnd_508504] using wordTrace_append hprefix tailTrace_508504
  have hstable : (prefixWord ++ tailWord_508504).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_508504).length < 2 ^ (prefixWord ++ tailWord_508504).sum := by decide
  have hdescent : baseEnd_508504 < baseStart_508504 := by decide
  rcases family_descends (prefixWord ++ tailWord_508504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_508594 : List Nat := [3, 2, 1, 1, 1, 2, 1, 5, 6]
def baseStart_508594 : Nat := 118140960795 + 508594 * 2 ^ 59
def prefixEnd_508594 : Nat := 4983230072969 + 3 ^ 40 * 508594 * 2
def baseEnd_508594 : Nat := 58034039998419634963561

theorem tailTrace_508594 : CollatzResearch.WordTrace tailWord_508594 prefixEnd_508594 58034039998419634963561 := by
  unfold tailWord_508594
  simp only [CollatzResearch.WordTrace]
  refine ⟨4637486779864568446239209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12366631412972182523304557 4637486779864568446239209)
  ·
    refine ⟨3478115084898426334679407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4637486779864568446239209 3478115084898426334679407)
    ·
      refine ⟨5217172627347639502019111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3478115084898426334679407 5217172627347639502019111)
      ·
        refine ⟨7825758941021459253028667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5217172627347639502019111 7825758941021459253028667)
        ·
          refine ⟨11738638411532188879543001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7825758941021459253028667 11738638411532188879543001)
          ·
            refine ⟨8803978808649141659657251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11738638411532188879543001 8803978808649141659657251)
            ·
              refine ⟨13205968212973712489485877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8803978808649141659657251 13205968212973712489485877)
              ·
                refine ⟨1238059519966285545889301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13205968212973712489485877 1238059519966285545889301)
                ·
                  refine ⟨58034039998419634963561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1238059519966285545889301 58034039998419634963561)
                  ·
                    rfl

theorem cell22_508594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 5, 6].length) (baseStart_508594 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_508594 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_508594 prefixEnd_508594 := by exact prefixLift 508594
  have htrace : WordTrace (prefixWord ++ tailWord_508594) baseStart_508594 baseEnd_508594 := by
    simpa [prefixWord, tailWord_508594, baseEnd_508594] using wordTrace_append hprefix tailTrace_508594
  have hstable : (prefixWord ++ tailWord_508594).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_508594).length < 2 ^ (prefixWord ++ tailWord_508594).sum := by decide
  have hdescent : baseEnd_508594 < baseStart_508594 := by decide
  rcases family_descends (prefixWord ++ tailWord_508594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_508639 : List Nat := [1, 1, 2, 3, 2, 4, 9]
def baseStart_508639 : Nat := 118140960795 + 508639 * 2 ^ 59
def prefixEnd_508639 : Nat := 4983230072969 + 3 ^ 40 * 508639 * 2
def baseEnd_508639 : Nat := 6448797200551621759835

theorem tailTrace_508639 : CollatzResearch.WordTrace tailWord_508639 prefixEnd_508639 6448797200551621759835 := by
  unfold tailWord_508639
  simp only [CollatzResearch.WordTrace]
  refine ⟨18551588404295246470344971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12367725602863497646896647 18551588404295246470344971)
  ·
    refine ⟨27827382606442869705517457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18551588404295246470344971 27827382606442869705517457)
    ·
      refine ⟨20870536954832152279138093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27827382606442869705517457 20870536954832152279138093)
      ·
        refine ⟨7826451358062057104676785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20870536954832152279138093 7826451358062057104676785)
        ·
          refine ⟨5869838518546542828507589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7826451358062057104676785 5869838518546542828507589)
          ·
            refine ⟨1100594722227476780345173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5869838518546542828507589 1100594722227476780345173)
            ·
              refine ⟨6448797200551621759835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1100594722227476780345173 6448797200551621759835)
              ·
                rfl

theorem cell22_508639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 4, 9].length) (baseStart_508639 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_508639 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_508639 prefixEnd_508639 := by exact prefixLift 508639
  have htrace : WordTrace (prefixWord ++ tailWord_508639) baseStart_508639 baseEnd_508639 := by
    simpa [prefixWord, tailWord_508639, baseEnd_508639] using wordTrace_append hprefix tailTrace_508639
  have hstable : (prefixWord ++ tailWord_508639).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_508639).length < 2 ^ (prefixWord ++ tailWord_508639).sum := by decide
  have hdescent : baseEnd_508639 < baseStart_508639 := by decide
  rcases family_descends (prefixWord ++ tailWord_508639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_508643 : List Nat := [1, 1, 1, 7, 1, 2, 1, 1, 4, 3]
def baseStart_508643 : Nat := 118140960795 + 508643 * 2 ^ 59
def prefixEnd_508643 : Nat := 4983230072969 + 3 ^ 40 * 508643 * 2
def baseEnd_508643 : Nat := 174118893696639110415533

theorem tailTrace_508643 : CollatzResearch.WordTrace tailWord_508643 prefixEnd_508643 174118893696639110415533 := by
  unfold tailWord_508643
  simp only [CollatzResearch.WordTrace]
  refine ⟨18551734296280755153490583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12367822864187170102327055 18551734296280755153490583)
  ·
    refine ⟨27827601444421132730235875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18551734296280755153490583 27827601444421132730235875)
    ·
      refine ⟨41741402166631699095353813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27827601444421132730235875 41741402166631699095353813)
      ·
        refine ⟨978314113280430447547355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 41741402166631699095353813 978314113280430447547355)
        ·
          refine ⟨1467471169920645671321033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 978314113280430447547355 1467471169920645671321033)
          ·
            refine ⟨1100603377440484253490775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1467471169920645671321033 1100603377440484253490775)
            ·
              refine ⟨1650905066160726380236163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1100603377440484253490775 1650905066160726380236163)
              ·
                refine ⟨2476357599241089570354245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1650905066160726380236163 2476357599241089570354245)
                ·
                  refine ⟨464317049857704294441421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2476357599241089570354245 464317049857704294441421)
                  ·
                    refine ⟨174118893696639110415533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 464317049857704294441421 174118893696639110415533)
                    ·
                      rfl

theorem cell22_508643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 2, 1, 1, 4, 3].length) (baseStart_508643 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_508643 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_508643 prefixEnd_508643 := by exact prefixLift 508643
  have htrace : WordTrace (prefixWord ++ tailWord_508643) baseStart_508643 baseEnd_508643 := by
    simpa [prefixWord, tailWord_508643, baseEnd_508643] using wordTrace_append hprefix tailTrace_508643
  have hstable : (prefixWord ++ tailWord_508643).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_508643).length < 2 ^ (prefixWord ++ tailWord_508643).sum := by decide
  have hdescent : baseEnd_508643 < baseStart_508643 := by decide
  rcases family_descends (prefixWord ++ tailWord_508643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_508690 : List Nat := [3, 2, 4, 1, 3, 1, 8]
def baseStart_508690 : Nat := 118140960795 + 508690 * 2 ^ 59
def prefixEnd_508690 : Nat := 4983230072969 + 3 ^ 40 * 508690 * 2
def baseEnd_508690 : Nat := 6449443805820246462607

theorem tailTrace_508690 : CollatzResearch.WordTrace tailWord_508690 prefixEnd_508690 6449443805820246462607 := by
  unfold tailWord_508690
  simp only [CollatzResearch.WordTrace]
  refine ⟨4638362131777620545112881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12368965684740321453634349 4638362131777620545112881)
  ·
    refine ⟨3478771598833215408834661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4638362131777620545112881 3478771598833215408834661)
    ·
      refine ⟨652269674781227889156499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3478771598833215408834661 652269674781227889156499)
      ·
        refine ⟨978404512171841833734749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 652269674781227889156499 978404512171841833734749)
        ·
          refine ⟨366901692064440687650531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 978404512171841833734749 366901692064440687650531)
          ·
            refine ⟨550352538096661031475797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 366901692064440687650531 550352538096661031475797)
            ·
              refine ⟨6449443805820246462607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 550352538096661031475797 6449443805820246462607)
              ·
                rfl

theorem cell22_508690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 3, 1, 8].length) (baseStart_508690 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_508690 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_508690 prefixEnd_508690 := by exact prefixLift 508690
  have htrace : WordTrace (prefixWord ++ tailWord_508690) baseStart_508690 baseEnd_508690 := by
    simpa [prefixWord, tailWord_508690, baseEnd_508690] using wordTrace_append hprefix tailTrace_508690
  have hstable : (prefixWord ++ tailWord_508690).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_508690).length < 2 ^ (prefixWord ++ tailWord_508690).sum := by decide
  have hdescent : baseEnd_508690 < baseStart_508690 := by decide
  rcases family_descends (prefixWord ++ tailWord_508690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_508756 : List Nat := [2, 4, 1, 1, 5, 1, 2, 2, 1, 3]
def baseStart_508756 : Nat := 118140960795 + 508756 * 2 ^ 59
def prefixEnd_508756 : Nat := 4983230072969 + 3 ^ 40 * 508756 * 2
def baseEnd_508756 : Nat := 174157575905944482340187

theorem tailTrace_508756 : CollatzResearch.WordTrace tailWord_508756 prefixEnd_508756 174157575905944482340187 := by
  unfold tailWord_508756
  simp only [CollatzResearch.WordTrace]
  refine ⟨9277927872435687726177061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12370570496580916968236081 9277927872435687726177061)
  ·
    refine ⟨1739611476081691448658199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9277927872435687726177061 1739611476081691448658199)
    ·
      refine ⟨2609417214122537172987299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1739611476081691448658199 2609417214122537172987299)
      ·
        refine ⟨3914125821183805759480949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2609417214122537172987299 3914125821183805759480949)
        ·
          refine ⟨366949295735981789951339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 3914125821183805759480949 366949295735981789951339)
          ·
            refine ⟨550423943603972684927009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 366949295735981789951339 550423943603972684927009)
            ·
              refine ⟨412817957702979513695257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 550423943603972684927009 412817957702979513695257)
              ·
                refine ⟨309613468277234635271443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 412817957702979513695257 309613468277234635271443)
                ·
                  refine ⟨464420202415851952907165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 309613468277234635271443 464420202415851952907165)
                  ·
                    refine ⟨174157575905944482340187, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 464420202415851952907165 174157575905944482340187)
                    ·
                      rfl

theorem cell22_508756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 5, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 5, 1, 2, 2, 1, 3].length) (baseStart_508756 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_508756 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_508756 prefixEnd_508756 := by exact prefixLift 508756
  have htrace : WordTrace (prefixWord ++ tailWord_508756) baseStart_508756 baseEnd_508756 := by
    simpa [prefixWord, tailWord_508756, baseEnd_508756] using wordTrace_append hprefix tailTrace_508756
  have hstable : (prefixWord ++ tailWord_508756).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_508756).length < 2 ^ (prefixWord ++ tailWord_508756).sum := by decide
  have hdescent : baseEnd_508756 < baseStart_508756 := by decide
  rcases family_descends (prefixWord ++ tailWord_508756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_508793 : List Nat := [1, 2, 1, 3, 2, 3, 3, 1, 2, 4]
def baseStart_508793 : Nat := 118140960795 + 508793 * 2 ^ 59
def prefixEnd_508793 : Nat := 4983230072969 + 3 ^ 40 * 508793 * 2
def baseEnd_508793 : Nat := 174170241762088719165073

theorem tailTrace_508793 : CollatzResearch.WordTrace tailWord_508793 prefixEnd_508793 174170241762088719165073 := by
  unfold tailWord_508793
  simp only [CollatzResearch.WordTrace]
  refine ⟨18557205245737330771451033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12371470163824887180967355 18557205245737330771451033)
  ·
    refine ⟨13917903934302998078588275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18557205245737330771451033 13917903934302998078588275)
    ·
      refine ⟨20876855901454497117882413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13917903934302998078588275 20876855901454497117882413)
      ·
        refine ⟨7828820963045436419205905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20876855901454497117882413 7828820963045436419205905)
        ·
          refine ⟨5871615722284077314404429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7828820963045436419205905 5871615722284077314404429)
          ·
            refine ⟨2201855895856528992901661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5871615722284077314404429 2201855895856528992901661)
            ·
              refine ⟨825695960946198372338123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2201855895856528992901661 825695960946198372338123)
              ·
                refine ⟨1238543941419297558507185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 825695960946198372338123 1238543941419297558507185)
                ·
                  refine ⟨928907956064473168880389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1238543941419297558507185 928907956064473168880389)
                  ·
                    refine ⟨174170241762088719165073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 928907956064473168880389 174170241762088719165073)
                    ·
                      rfl

theorem cell22_508793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 3, 1, 2, 4].length) (baseStart_508793 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_508793 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_508793 prefixEnd_508793 := by exact prefixLift 508793
  have htrace : WordTrace (prefixWord ++ tailWord_508793) baseStart_508793 baseEnd_508793 := by
    simpa [prefixWord, tailWord_508793, baseEnd_508793] using wordTrace_append hprefix tailTrace_508793
  have hstable : (prefixWord ++ tailWord_508793).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_508793).length < 2 ^ (prefixWord ++ tailWord_508793).sum := by decide
  have hdescent : baseEnd_508793 < baseStart_508793 := by decide
  rcases family_descends (prefixWord ++ tailWord_508793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_508851 : List Nat := [1, 1, 1, 2, 3, 1, 2, 2, 4, 5]
def baseStart_508851 : Nat := 118140960795 + 508851 * 2 ^ 59
def prefixEnd_508851 : Nat := 4983230072969 + 3 ^ 40 * 508851 * 2
def baseEnd_508851 : Nat := 174190096347395901214895

theorem tailTrace_508851 : CollatzResearch.WordTrace tailWord_508851 prefixEnd_508851 174190096347395901214895 := by
  unfold tailWord_508851
  simp only [CollatzResearch.WordTrace]
  refine ⟨18559320679527206677062407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12372880453018137784708271 18559320679527206677062407)
  ·
    refine ⟨27838981019290810015593611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18559320679527206677062407 27838981019290810015593611)
    ·
      refine ⟨41758471528936215023390417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27838981019290810015593611 41758471528936215023390417)
      ·
        refine ⟨31318853646702161267542813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41758471528936215023390417 31318853646702161267542813)
        ·
          refine ⟨11744570117513310475328555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31318853646702161267542813 11744570117513310475328555)
          ·
            refine ⟨17616855176269965712992833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11744570117513310475328555 17616855176269965712992833)
            ·
              refine ⟨13212641382202474284744625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17616855176269965712992833 13212641382202474284744625)
              ·
                refine ⟨9909481036651855713558469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13212641382202474284744625 9909481036651855713558469)
                ·
                  refine ⟨1858027694372222946292213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9909481036651855713558469 1858027694372222946292213)
                  ·
                    refine ⟨174190096347395901214895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1858027694372222946292213 174190096347395901214895)
                    ·
                      rfl

theorem cell22_508851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 2, 4, 5].length) (baseStart_508851 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_508851 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_508851 prefixEnd_508851 := by exact prefixLift 508851
  have htrace : WordTrace (prefixWord ++ tailWord_508851) baseStart_508851 baseEnd_508851 := by
    simpa [prefixWord, tailWord_508851, baseEnd_508851] using wordTrace_append hprefix tailTrace_508851
  have hstable : (prefixWord ++ tailWord_508851).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_508851).length < 2 ^ (prefixWord ++ tailWord_508851).sum := by decide
  have hdescent : baseEnd_508851 < baseStart_508851 := by decide
  rcases family_descends (prefixWord ++ tailWord_508851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_508857 : List Nat := [1, 2, 1, 4, 2, 2, 3, 3, 1, 3]
def baseStart_508857 : Nat := 118140960795 + 508857 * 2 ^ 59
def prefixEnd_508857 : Nat := 4983230072969 + 3 ^ 40 * 508857 * 2
def baseEnd_508857 : Nat := 174192150270013885564877

theorem tailTrace_508857 : CollatzResearch.WordTrace tailWord_508857 prefixEnd_508857 174192150270013885564877 := by
  unfold tailWord_508857
  simp only [CollatzResearch.WordTrace]
  refine ⟨18559539517505469701780825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12373026345003646467853883 18559539517505469701780825)
  ·
    refine ⟨13919654638129102276335619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18559539517505469701780825 13919654638129102276335619)
    ·
      refine ⟨20879481957193653414503429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13919654638129102276335619 20879481957193653414503429)
      ·
        refine ⟨3914902866973810015219393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20879481957193653414503429 3914902866973810015219393)
        ·
          refine ⟨2936177150230357511414545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3914902866973810015219393 2936177150230357511414545)
          ·
            refine ⟨2202132862672768133560909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2936177150230357511414545 2202132862672768133560909)
            ·
              refine ⟨825799823502288050085341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2202132862672768133560909 825799823502288050085341)
              ·
                refine ⟨309674933813358018782003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 825799823502288050085341 309674933813358018782003)
                ·
                  refine ⟨464512400720037028173005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 309674933813358018782003 464512400720037028173005)
                  ·
                    refine ⟨174192150270013885564877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 464512400720037028173005 174192150270013885564877)
                    ·
                      rfl

theorem cell22_508857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 3, 3, 1, 3].length) (baseStart_508857 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_508857 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_508857 prefixEnd_508857 := by exact prefixLift 508857
  have htrace : WordTrace (prefixWord ++ tailWord_508857) baseStart_508857 baseEnd_508857 := by
    simpa [prefixWord, tailWord_508857, baseEnd_508857] using wordTrace_append hprefix tailTrace_508857
  have hstable : (prefixWord ++ tailWord_508857).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_508857).length < 2 ^ (prefixWord ++ tailWord_508857).sum := by decide
  have hdescent : baseEnd_508857 < baseStart_508857 := by decide
  rcases family_descends (prefixWord ++ tailWord_508857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_508913 : List Nat := [1, 2, 2, 2, 4, 1, 1, 1, 3, 5]
def baseStart_508913 : Nat := 118140960795 + 508913 * 2 ^ 59
def prefixEnd_508913 : Nat := 4983230072969 + 3 ^ 40 * 508913 * 2
def baseEnd_508913 : Nat := 174211320214448406164705

theorem tailTrace_508913 : CollatzResearch.WordTrace tailWord_508913 prefixEnd_508913 174211320214448406164705 := by
  unfold tailWord_508913
  simp only [CollatzResearch.WordTrace]
  refine ⟨18561582005302591265819393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12374388003535060843879595 18561582005302591265819393)
  ·
    refine ⟨13921186503976943449364545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18561582005302591265819393 13921186503976943449364545)
    ·
      refine ⟨10440889877982707587023409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13921186503976943449364545 10440889877982707587023409)
      ·
        refine ⟨7830667408487030690267557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10440889877982707587023409 7830667408487030690267557)
        ·
          refine ⟨1468250139091318254425167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7830667408487030690267557 1468250139091318254425167)
          ·
            refine ⟨2202375208636977381637751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1468250139091318254425167 2202375208636977381637751)
            ·
              refine ⟨3303562812955466072456627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2202375208636977381637751 3303562812955466072456627)
              ·
                refine ⟨4955344219433199108684941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3303562812955466072456627 4955344219433199108684941)
                ·
                  refine ⟨1858254082287449665756853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4955344219433199108684941 1858254082287449665756853)
                  ·
                    refine ⟨174211320214448406164705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1858254082287449665756853 174211320214448406164705)
                    ·
                      rfl

theorem cell22_508913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 1, 1, 3, 5].length) (baseStart_508913 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_508913 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_508913 prefixEnd_508913 := by exact prefixLift 508913
  have htrace : WordTrace (prefixWord ++ tailWord_508913) baseStart_508913 baseEnd_508913 := by
    simpa [prefixWord, tailWord_508913, baseEnd_508913] using wordTrace_append hprefix tailTrace_508913
  have hstable : (prefixWord ++ tailWord_508913).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_508913).length < 2 ^ (prefixWord ++ tailWord_508913).sum := by decide
  have hdescent : baseEnd_508913 < baseStart_508913 := by decide
  rcases family_descends (prefixWord ++ tailWord_508913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_508962 : List Nat := [3, 3, 1, 1, 1, 5, 1, 1, 2, 4]
def baseStart_508962 : Nat := 118140960795 + 508962 * 2 ^ 59
def prefixEnd_508962 : Nat := 4983230072969 + 3 ^ 40 * 508962 * 2
def baseEnd_508962 : Nat := 174228093915828611689555

theorem tailTrace_508962 : CollatzResearch.WordTrace tailWord_508962 prefixEnd_508962 174228093915828611689555 := by
  unfold tailWord_508962
  simp only [CollatzResearch.WordTrace]
  refine ⟨4640842295531268158588285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12375579454750048422902093 4640842295531268158588285)
  ·
    refine ⟨1740315860824225559470607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4640842295531268158588285 1740315860824225559470607)
    ·
      refine ⟨2610473791236338339205911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1740315860824225559470607 2610473791236338339205911)
      ·
        refine ⟨3915710686854507508808867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2610473791236338339205911 3915710686854507508808867)
        ·
          refine ⟨5873566030281761263213301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3915710686854507508808867 5873566030281761263213301)
          ·
            refine ⟨550646815338915118426247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 5873566030281761263213301 550646815338915118426247)
            ·
              refine ⟨825970223008372677639371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 550646815338915118426247 825970223008372677639371)
              ·
                refine ⟨1238955334512559016459057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 825970223008372677639371 1238955334512559016459057)
                ·
                  refine ⟨929216500884419262344293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1238955334512559016459057 929216500884419262344293)
                  ·
                    refine ⟨174228093915828611689555, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 929216500884419262344293 174228093915828611689555)
                    ·
                      rfl

theorem cell22_508962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 5, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 5, 1, 1, 2, 4].length) (baseStart_508962 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_508962 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_508962 prefixEnd_508962 := by exact prefixLift 508962
  have htrace : WordTrace (prefixWord ++ tailWord_508962) baseStart_508962 baseEnd_508962 := by
    simpa [prefixWord, tailWord_508962, baseEnd_508962] using wordTrace_append hprefix tailTrace_508962
  have hstable : (prefixWord ++ tailWord_508962).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_508962).length < 2 ^ (prefixWord ++ tailWord_508962).sum := by decide
  have hdescent : baseEnd_508962 < baseStart_508962 := by decide
  rcases family_descends (prefixWord ++ tailWord_508962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_508992 : List Nat := [2, 1, 1, 2, 2, 3, 1, 6, 1, 3]
def baseStart_508992 : Nat := 118140960795 + 508992 * 2 ^ 59
def prefixEnd_508992 : Nat := 4983230072969 + 3 ^ 40 * 508992 * 2
def baseEnd_508992 : Nat := 174238363528918533439463

theorem tailTrace_508992 : CollatzResearch.WordTrace tailWord_508992 prefixEnd_508992 174238363528918533439463 := by
  unfold tailWord_508992
  simp only [CollatzResearch.WordTrace]
  refine ⟨9282231686008193878972615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12376308914677591838630153 9282231686008193878972615)
  ·
    refine ⟨13923347529012290818458923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9282231686008193878972615 13923347529012290818458923)
    ·
      refine ⟨20885021293518436227688385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13923347529012290818458923 20885021293518436227688385)
      ·
        refine ⟨15663765970138827170766289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20885021293518436227688385 15663765970138827170766289)
        ·
          refine ⟨11747824477604120378074717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15663765970138827170766289 11747824477604120378074717)
          ·
            refine ⟨4405434179101545141778019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11747824477604120378074717 4405434179101545141778019)
            ·
              refine ⟨6608151268652317712667029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4405434179101545141778019 6608151268652317712667029)
              ·
                refine ⟨309757090718077392781267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 6608151268652317712667029 309757090718077392781267)
                ·
                  refine ⟨464635636077116089171901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 309757090718077392781267 464635636077116089171901)
                  ·
                    refine ⟨174238363528918533439463, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 464635636077116089171901 174238363528918533439463)
                    ·
                      rfl

theorem cell22_508992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 1, 6, 1, 3].length) (baseStart_508992 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_508992 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_508992 prefixEnd_508992 := by exact prefixLift 508992
  have htrace : WordTrace (prefixWord ++ tailWord_508992) baseStart_508992 baseEnd_508992 := by
    simpa [prefixWord, tailWord_508992, baseEnd_508992] using wordTrace_append hprefix tailTrace_508992
  have hstable : (prefixWord ++ tailWord_508992).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_508992).length < 2 ^ (prefixWord ++ tailWord_508992).sum := by decide
  have hdescent : baseEnd_508992 < baseStart_508992 := by decide
  rcases family_descends (prefixWord ++ tailWord_508992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_509026 : List Nat := [3, 3, 2, 2, 1, 1, 3, 3, 1, 3]
def baseStart_509026 : Nat := 118140960795 + 509026 * 2 ^ 59
def prefixEnd_509026 : Nat := 4983230072969 + 3 ^ 40 * 509026 * 2
def baseEnd_509026 : Nat := 174250002423753778089359

theorem tailTrace_509026 : CollatzResearch.WordTrace tailWord_509026 prefixEnd_509026 174250002423753778089359 := by
  unfold tailWord_509026
  simp only [CollatzResearch.WordTrace]
  refine ⟨4641425863473302891170733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12377135635928807709788621 4641425863473302891170733)
  ·
    refine ⟨1740534698802488584189025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4641425863473302891170733 1740534698802488584189025)
    ·
      refine ⟨1305401024101866438141769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1740534698802488584189025 1305401024101866438141769)
      ·
        refine ⟨979050768076399828606327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1305401024101866438141769 979050768076399828606327)
        ·
          refine ⟨1468576152114599742909491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 979050768076399828606327 1468576152114599742909491)
          ·
            refine ⟨2202864228171899614364237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1468576152114599742909491 2202864228171899614364237)
            ·
              refine ⟨826074085564462355386589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2202864228171899614364237 826074085564462355386589)
              ·
                refine ⟨309777782086673383269971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 826074085564462355386589 309777782086673383269971)
                ·
                  refine ⟨464666673130010074904957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 309777782086673383269971 464666673130010074904957)
                  ·
                    refine ⟨174250002423753778089359, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 464666673130010074904957 174250002423753778089359)
                    ·
                      rfl

theorem cell22_509026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 3, 3, 1, 3].length) (baseStart_509026 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_509026 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_509026 prefixEnd_509026 := by exact prefixLift 509026
  have htrace : WordTrace (prefixWord ++ tailWord_509026) baseStart_509026 baseEnd_509026 := by
    simpa [prefixWord, tailWord_509026, baseEnd_509026] using wordTrace_append hprefix tailTrace_509026
  have hstable : (prefixWord ++ tailWord_509026).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_509026).length < 2 ^ (prefixWord ++ tailWord_509026).sum := by decide
  have hdescent : baseEnd_509026 < baseStart_509026 := by decide
  rcases family_descends (prefixWord ++ tailWord_509026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_509082 : List Nat := [3, 1, 1, 5, 1, 2, 1, 2, 1, 5]
def baseStart_509082 : Nat := 118140960795 + 509082 * 2 ^ 59
def prefixEnd_509082 : Nat := 4983230072969 + 3 ^ 40 * 509082 * 2
def baseEnd_509082 : Nat := 174269172368188298689187

theorem tailTrace_509082 : CollatzResearch.WordTrace tailWord_509082 prefixEnd_509082 174269172368188298689187 := by
  unfold tailWord_509082
  simp only [CollatzResearch.WordTrace]
  refine ⟨4641936485422583282180375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12378497294460222085814333 4641936485422583282180375)
  ·
    refine ⟨6962904728133874923270563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4641936485422583282180375 6962904728133874923270563)
    ·
      refine ⟨10444357092200812384905845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6962904728133874923270563 10444357092200812384905845)
      ·
        refine ⟨979158477393826161084923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 10444357092200812384905845 979158477393826161084923)
        ·
          refine ⟨1468737716090739241627385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 979158477393826161084923 1468737716090739241627385)
          ·
            refine ⟨1101553287068054431220539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1468737716090739241627385 1101553287068054431220539)
            ·
              refine ⟨1652329930602081646830809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1101553287068054431220539 1652329930602081646830809)
              ·
                refine ⟨1239247447951561235123107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1652329930602081646830809 1239247447951561235123107)
                ·
                  refine ⟨1858871171927341852684661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1239247447951561235123107 1858871171927341852684661)
                  ·
                    refine ⟨174269172368188298689187, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1858871171927341852684661 174269172368188298689187)
                    ·
                      rfl

theorem cell22_509082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 2, 1, 2, 1, 5].length) (baseStart_509082 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_509082 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_509082 prefixEnd_509082 := by exact prefixLift 509082
  have htrace : WordTrace (prefixWord ++ tailWord_509082) baseStart_509082 baseEnd_509082 := by
    simpa [prefixWord, tailWord_509082, baseEnd_509082] using wordTrace_append hprefix tailTrace_509082
  have hstable : (prefixWord ++ tailWord_509082).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_509082).length < 2 ^ (prefixWord ++ tailWord_509082).sum := by decide
  have hdescent : baseEnd_509082 < baseStart_509082 := by decide
  rcases family_descends (prefixWord ++ tailWord_509082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_509086 : List Nat := [4, 3, 1, 1, 2, 2, 3, 1, 1, 4]
def baseStart_509086 : Nat := 118140960795 + 509086 * 2 ^ 59
def prefixEnd_509086 : Nat := 4983230072969 + 3 ^ 40 * 509086 * 2
def baseEnd_509086 : Nat := 174270541649933621589175

theorem tailTrace_509086 : CollatzResearch.WordTrace tailWord_509086 prefixEnd_509086 174270541649933621589175 := by
  unfold tailWord_509086
  simp only [CollatzResearch.WordTrace]
  refine ⟨2320986479209480226483389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12378594555783894541244741 2320986479209480226483389)
  ·
    refine ⟨870369929703555084931271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2320986479209480226483389 870369929703555084931271)
    ·
      refine ⟨1305554894555332627396907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 870369929703555084931271 1305554894555332627396907)
      ·
        refine ⟨1958332341832998941095361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1305554894555332627396907 1958332341832998941095361)
        ·
          refine ⟨1468749256374749205821521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1958332341832998941095361 1468749256374749205821521)
          ·
            refine ⟨1101561942281061904366141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1468749256374749205821521 1101561942281061904366141)
            ·
              refine ⟨413085728355398214137303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1101561942281061904366141 413085728355398214137303)
              ·
                refine ⟨619628592533097321205955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 413085728355398214137303 619628592533097321205955)
                ·
                  refine ⟨929442888799645981808933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 619628592533097321205955 929442888799645981808933)
                  ·
                    refine ⟨174270541649933621589175, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 929442888799645981808933 174270541649933621589175)
                    ·
                      rfl

theorem cell22_509086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 2, 3, 1, 1, 4].length) (baseStart_509086 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_509086 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_509086 prefixEnd_509086 := by exact prefixLift 509086
  have htrace : WordTrace (prefixWord ++ tailWord_509086) baseStart_509086 baseEnd_509086 := by
    simpa [prefixWord, tailWord_509086, baseEnd_509086] using wordTrace_append hprefix tailTrace_509086
  have hstable : (prefixWord ++ tailWord_509086).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_509086).length < 2 ^ (prefixWord ++ tailWord_509086).sum := by decide
  have hdescent : baseEnd_509086 < baseStart_509086 := by decide
  rcases family_descends (prefixWord ++ tailWord_509086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_509095 : List Nat := [1, 1, 6, 2, 1, 11]
def baseStart_509095 : Nat := 118140960795 + 509095 * 2 ^ 59
def prefixEnd_509095 : Nat := 4983230072969 + 3 ^ 40 * 509095 * 2
def baseEnd_509095 : Nat := 2151526204121735779187

theorem tailTrace_509095 : CollatzResearch.WordTrace tailWord_509095 prefixEnd_509095 2151526204121735779187 := by
  unfold tailWord_509095
  simp only [CollatzResearch.WordTrace]
  refine ⟨18568220090643236348944739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12378813393762157565963159 18568220090643236348944739)
  ·
    refine ⟨27852330135964854523417109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18568220090643236348944739 27852330135964854523417109)
    ·
      refine ⟨1305577975123352555785177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 27852330135964854523417109 1305577975123352555785177)
      ·
        refine ⟨979183481342514416838883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1305577975123352555785177 979183481342514416838883)
        ·
          refine ⟨1468775222013771625258325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 979183481342514416838883 1468775222013771625258325)
          ·
            refine ⟨2151526204121735779187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 1468775222013771625258325 2151526204121735779187)
            ·
              rfl

theorem cell22_509095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 11].length) (baseStart_509095 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_509095 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_509095 prefixEnd_509095 := by exact prefixLift 509095
  have htrace : WordTrace (prefixWord ++ tailWord_509095) baseStart_509095 baseEnd_509095 := by
    simpa [prefixWord, tailWord_509095, baseEnd_509095] using wordTrace_append hprefix tailTrace_509095
  have hstable : (prefixWord ++ tailWord_509095).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_509095).length < 2 ^ (prefixWord ++ tailWord_509095).sum := by decide
  have hdescent : baseEnd_509095 < baseStart_509095 := by decide
  rcases family_descends (prefixWord ++ tailWord_509095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_509157 : List Nat := [1, 3, 1, 4, 3, 1, 1, 1, 7]
def baseStart_509157 : Nat := 118140960795 + 509157 * 2 ^ 59
def prefixEnd_509157 : Nat := 4983230072969 + 3 ^ 40 * 509157 * 2
def baseEnd_509157 : Nat := 58098282133637701021319

theorem tailTrace_509157 : CollatzResearch.WordTrace tailWord_509157 prefixEnd_509157 58098282133637701021319 := by
  unfold tailWord_509157
  simp only [CollatzResearch.WordTrace]
  refine ⟨18570481416418620937701725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12380320944279080625134483 18570481416418620937701725)
  ·
    refine ⟨6963930531156982851638147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18570481416418620937701725 6963930531156982851638147)
    ·
      refine ⟨10445895796735474277457221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6963930531156982851638147 10445895796735474277457221)
      ·
        refine ⟨1958605461887901427023229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10445895796735474277457221 1958605461887901427023229)
        ·
          refine ⟨734477048207963035133711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1958605461887901427023229 734477048207963035133711)
          ·
            refine ⟨1101715572311944552700567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 734477048207963035133711 1101715572311944552700567)
            ·
              refine ⟨1652573358467916829050851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1101715572311944552700567 1652573358467916829050851)
              ·
                refine ⟨2478860037701875243576277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1652573358467916829050851 2478860037701875243576277)
                ·
                  refine ⟨58098282133637701021319, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2478860037701875243576277 58098282133637701021319)
                  ·
                    rfl

theorem cell22_509157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 1, 1, 1, 7].length) (baseStart_509157 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_509157 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_509157 prefixEnd_509157 := by exact prefixLift 509157
  have htrace : WordTrace (prefixWord ++ tailWord_509157) baseStart_509157 baseEnd_509157 := by
    simpa [prefixWord, tailWord_509157, baseEnd_509157] using wordTrace_append hprefix tailTrace_509157
  have hstable : (prefixWord ++ tailWord_509157).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_509157).length < 2 ^ (prefixWord ++ tailWord_509157).sum := by decide
  have hdescent : baseEnd_509157 < baseStart_509157 := by decide
  rcases family_descends (prefixWord ++ tailWord_509157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_509187 : List Nat := [1, 1, 1, 3, 2, 4, 1, 4, 1, 4]
def baseStart_509187 : Nat := 118140960795 + 509187 * 2 ^ 59
def prefixEnd_509187 : Nat := 4983230072969 + 3 ^ 40 * 509187 * 2
def baseEnd_509187 : Nat := 174305116014003024813865

theorem tailTrace_509187 : CollatzResearch.WordTrace tailWord_509187 prefixEnd_509187 174305116014003024813865 := by
  unfold tailWord_509187
  simp only [CollatzResearch.WordTrace]
  refine ⟨18571575606309936061293815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12381050404206624040862543 18571575606309936061293815)
  ·
    refine ⟨27857363409464904091940723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18571575606309936061293815 27857363409464904091940723)
    ·
      refine ⟨41786045114197356137911085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27857363409464904091940723 41786045114197356137911085)
      ·
        refine ⟨15669766917824008551716657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41786045114197356137911085 15669766917824008551716657)
        ·
          refine ⟨11752325188368006413787493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15669766917824008551716657 11752325188368006413787493)
          ·
            refine ⟨2203560972819001202585155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11752325188368006413787493 2203560972819001202585155)
            ·
              refine ⟨3305341459228501803877733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2203560972819001202585155 3305341459228501803877733)
              ·
                refine ⟨619751523605344088227075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3305341459228501803877733 619751523605344088227075)
                ·
                  refine ⟨929627285408016132340613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 619751523605344088227075 929627285408016132340613)
                  ·
                    refine ⟨174305116014003024813865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 929627285408016132340613 174305116014003024813865)
                    ·
                      rfl

theorem cell22_509187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 1, 4, 1, 4].length) (baseStart_509187 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_509187 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_509187 prefixEnd_509187 := by exact prefixLift 509187
  have htrace : WordTrace (prefixWord ++ tailWord_509187) baseStart_509187 baseEnd_509187 := by
    simpa [prefixWord, tailWord_509187, baseEnd_509187] using wordTrace_append hprefix tailTrace_509187
  have hstable : (prefixWord ++ tailWord_509187).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_509187).length < 2 ^ (prefixWord ++ tailWord_509187).sum := by decide
  have hdescent : baseEnd_509187 < baseStart_509187 := by decide
  rcases family_descends (prefixWord ++ tailWord_509187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_509249 : List Nat := [1, 2, 5, 2, 1, 1, 1, 3, 2, 4]
def baseStart_509249 : Nat := 118140960795 + 509249 * 2 ^ 59
def prefixEnd_509249 : Nat := 4983230072969 + 3 ^ 40 * 509249 * 2
def baseEnd_509249 : Nat := 174326339881055529763675

theorem tailTrace_509249 : CollatzResearch.WordTrace tailWord_509249 prefixEnd_509249 174326339881055529763675 := by
  unfold tailWord_509249
  simp only [CollatzResearch.WordTrace]
  refine ⟨18573836932085320650050801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12382557954723547100033867 18573836932085320650050801)
  ·
    refine ⟨13930377699063990487538101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18573836932085320650050801 13930377699063990487538101)
    ·
      refine ⟨1305972909287249108206697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 13930377699063990487538101 1305972909287249108206697)
      ·
        refine ⟨979479681965436831155023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1305972909287249108206697 979479681965436831155023)
        ·
          refine ⟨1469219522948155246732535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 979479681965436831155023 1469219522948155246732535)
          ·
            refine ⟨2203829284422232870098803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1469219522948155246732535 2203829284422232870098803)
            ·
              refine ⟨3305743926633349305148205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2203829284422232870098803 3305743926633349305148205)
              ·
                refine ⟨1239653972487505989430577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3305743926633349305148205 1239653972487505989430577)
                ·
                  refine ⟨929740479365629492072933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1239653972487505989430577 929740479365629492072933)
                  ·
                    refine ⟨174326339881055529763675, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 929740479365629492072933 174326339881055529763675)
                    ·
                      rfl

theorem cell22_509249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 1, 3, 2, 4].length) (baseStart_509249 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_509249 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_509249 prefixEnd_509249 := by exact prefixLift 509249
  have htrace : WordTrace (prefixWord ++ tailWord_509249) baseStart_509249 baseEnd_509249 := by
    simpa [prefixWord, tailWord_509249, baseEnd_509249] using wordTrace_append hprefix tailTrace_509249
  have hstable : (prefixWord ++ tailWord_509249).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_509249).length < 2 ^ (prefixWord ++ tailWord_509249).sum := by decide
  have hdescent : baseEnd_509249 < baseStart_509249 := by decide
  rcases family_descends (prefixWord ++ tailWord_509249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_509337 : List Nat := [1, 2, 1, 2, 1, 5, 1, 3, 6]
def baseStart_509337 : Nat := 118140960795 + 509337 * 2 ^ 59
def prefixEnd_509337 : Nat := 4983230072969 + 3 ^ 40 * 509337 * 2
def baseEnd_509337 : Nat := 58118821359817544521135

theorem tailTrace_509337 : CollatzResearch.WordTrace tailWord_509337 prefixEnd_509337 58118821359817544521135 := by
  unfold tailWord_509337
  simp only [CollatzResearch.WordTrace]
  refine ⟨18577046555766511679254265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12384697703844341119502843 18577046555766511679254265)
  ·
    refine ⟨13932784916824883759440699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18577046555766511679254265 13932784916824883759440699)
    ·
      refine ⟨20899177375237325639161049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13932784916824883759440699 20899177375237325639161049)
      ·
        refine ⟨15674383031427994229370787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20899177375237325639161049 15674383031427994229370787)
        ·
          refine ⟨23511574547141991344056181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15674383031427994229370787 23511574547141991344056181)
          ·
            refine ⟨2204210113794561688505267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 23511574547141991344056181 2204210113794561688505267)
            ·
              refine ⟨3306315170691842532757901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2204210113794561688505267 3306315170691842532757901)
              ·
                refine ⟨1239868189009440949784213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3306315170691842532757901 1239868189009440949784213)
                ·
                  refine ⟨58118821359817544521135, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1239868189009440949784213 58118821359817544521135)
                  ·
                    rfl

theorem cell22_509337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 1, 3, 6].length) (baseStart_509337 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_509337 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_509337 prefixEnd_509337 := by exact prefixLift 509337
  have htrace : WordTrace (prefixWord ++ tailWord_509337) baseStart_509337 baseEnd_509337 := by
    simpa [prefixWord, tailWord_509337, baseEnd_509337] using wordTrace_append hprefix tailTrace_509337
  have hstable : (prefixWord ++ tailWord_509337).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_509337).length < 2 ^ (prefixWord ++ tailWord_509337).sum := by decide
  have hdescent : baseEnd_509337 < baseStart_509337 := by decide
  rcases family_descends (prefixWord ++ tailWord_509337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_509367 : List Nat := [1, 1, 3, 1, 3, 2, 1, 3, 1, 6]
def baseStart_509367 : Nat := 118140960795 + 509367 * 2 ^ 59
def prefixEnd_509367 : Nat := 4983230072969 + 3 ^ 40 * 509367 * 2
def baseEnd_509367 : Nat := 174366733692542555313313

theorem tailTrace_509367 : CollatzResearch.WordTrace tailWord_509367 prefixEnd_509367 174366733692542555313313 := by
  unfold tailWord_509367
  simp only [CollatzResearch.WordTrace]
  refine ⟨18578140745657826802846355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12385427163771884535230903 18578140745657826802846355)
  ·
    refine ⟨27867211118486740204269533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18578140745657826802846355 27867211118486740204269533)
    ·
      refine ⟨10450204169432527576601075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27867211118486740204269533 10450204169432527576601075)
      ·
        refine ⟨15675306254148791364901613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10450204169432527576601075 15675306254148791364901613)
        ·
          refine ⟨5878239845305796761838105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15675306254148791364901613 5878239845305796761838105)
          ·
            refine ⟨4408679883979347571378579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5878239845305796761838105 4408679883979347571378579)
            ·
              refine ⟨6613019825969021357067869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4408679883979347571378579 6613019825969021357067869)
              ·
                refine ⟨2479882434738383008900451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6613019825969021357067869 2479882434738383008900451)
                ·
                  refine ⟨3719823652107574513350677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2479882434738383008900451 3719823652107574513350677)
                  ·
                    refine ⟨174366733692542555313313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3719823652107574513350677 174366733692542555313313)
                    ·
                      rfl

theorem cell22_509367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 1, 3, 1, 6].length) (baseStart_509367 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_509367 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_509367 prefixEnd_509367 := by exact prefixLift 509367
  have htrace : WordTrace (prefixWord ++ tailWord_509367) baseStart_509367 baseEnd_509367 := by
    simpa [prefixWord, tailWord_509367, baseEnd_509367] using wordTrace_append hprefix tailTrace_509367
  have hstable : (prefixWord ++ tailWord_509367).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_509367).length < 2 ^ (prefixWord ++ tailWord_509367).sum := by decide
  have hdescent : baseEnd_509367 < baseStart_509367 := by decide
  rcases family_descends (prefixWord ++ tailWord_509367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_509384 : List Nat := [2, 1, 3, 1, 3, 1, 3, 2, 2, 4]
def baseStart_509384 : Nat := 118140960795 + 509384 * 2 ^ 59
def prefixEnd_509384 : Nat := 4983230072969 + 3 ^ 40 * 509384 * 2
def baseEnd_509384 : Nat := 174372553139960177638261

theorem tailTrace_509384 : CollatzResearch.WordTrace tailWord_509384 prefixEnd_509384 174372553139960177638261 := by
  unfold tailWord_509384
  simp only [CollatzResearch.WordTrace]
  refine ⟨9289380393298119353107603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12385840524397492470810137 9289380393298119353107603)
  ·
    refine ⟨13934070589947179029661405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9289380393298119353107603 13934070589947179029661405)
    ·
      refine ⟨5225276471230192136123027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13934070589947179029661405 5225276471230192136123027)
      ·
        refine ⟨7837914706845288204184541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5225276471230192136123027 7837914706845288204184541)
        ·
          refine ⟨2939218015066983076569203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7837914706845288204184541 2939218015066983076569203)
          ·
            refine ⟨4408827022600474614853805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2939218015066983076569203 4408827022600474614853805)
            ·
              refine ⟨1653310133475177980570177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4408827022600474614853805 1653310133475177980570177)
              ·
                refine ⟨1239982600106383485427633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1653310133475177980570177 1239982600106383485427633)
                ·
                  refine ⟨929986950079787614070725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1239982600106383485427633 929986950079787614070725)
                  ·
                    refine ⟨174372553139960177638261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 929986950079787614070725 174372553139960177638261)
                    ·
                      rfl

theorem cell22_509384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 3, 2, 2, 4].length) (baseStart_509384 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_509384 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_509384 prefixEnd_509384 := by exact prefixLift 509384
  have htrace : WordTrace (prefixWord ++ tailWord_509384) baseStart_509384 baseEnd_509384 := by
    simpa [prefixWord, tailWord_509384, baseEnd_509384] using wordTrace_append hprefix tailTrace_509384
  have hstable : (prefixWord ++ tailWord_509384).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_509384).length < 2 ^ (prefixWord ++ tailWord_509384).sum := by decide
  have hdescent : baseEnd_509384 < baseStart_509384 := by decide
  rcases family_descends (prefixWord ++ tailWord_509384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_509388 : List Nat := [2, 2, 1, 4, 2, 2, 3, 2, 4]
def baseStart_509388 : Nat := 118140960795 + 509388 * 2 ^ 59
def prefixEnd_509388 : Nat := 4983230072969 + 3 ^ 40 * 509388 * 2
def baseEnd_509388 : Nat := 58124640807235166846083

theorem tailTrace_509388 : CollatzResearch.WordTrace tailWord_509388 prefixEnd_509388 58124640807235166846083 := by
  unfold tailWord_509388
  simp only [CollatzResearch.WordTrace]
  refine ⟨9289453339290873694680409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12385937785721164926240545 9289453339290873694680409)
  ·
    refine ⟨6967090004468155271010307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9289453339290873694680409 6967090004468155271010307)
    ·
      refine ⟨10450635006702232906515461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6967090004468155271010307 10450635006702232906515461)
      ·
        refine ⟨1959494063756668669971649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10450635006702232906515461 1959494063756668669971649)
        ·
          refine ⟨1469620547817501502478737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1959494063756668669971649 1469620547817501502478737)
          ·
            refine ⟨1102215410863126126859053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1469620547817501502478737 1102215410863126126859053)
            ·
              refine ⟨413330779073672297572145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1102215410863126126859053 413330779073672297572145)
              ·
                refine ⟨309998084305254223179109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 413330779073672297572145 309998084305254223179109)
                ·
                  refine ⟨58124640807235166846083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 309998084305254223179109 58124640807235166846083)
                  ·
                    rfl

theorem cell22_509388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 2, 3, 2, 4].length) (baseStart_509388 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_509388 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_509388 prefixEnd_509388 := by exact prefixLift 509388
  have htrace : WordTrace (prefixWord ++ tailWord_509388) baseStart_509388 baseEnd_509388 := by
    simpa [prefixWord, tailWord_509388, baseEnd_509388] using wordTrace_append hprefix tailTrace_509388
  have hstable : (prefixWord ++ tailWord_509388).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_509388).length < 2 ^ (prefixWord ++ tailWord_509388).sum := by decide
  have hdescent : baseEnd_509388 < baseStart_509388 := by decide
  rcases family_descends (prefixWord ++ tailWord_509388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_509427 : List Nat := [1, 1, 1, 2, 2, 2, 2, 4, 7]
def baseStart_509427 : Nat := 118140960795 + 509427 * 2 ^ 59
def prefixEnd_509427 : Nat := 4983230072969 + 3 ^ 40 * 509427 * 2
def baseEnd_509427 : Nat := 58129090972907466271043

theorem tailTrace_509427 : CollatzResearch.WordTrace tailWord_509427 prefixEnd_509427 58129090972907466271043 := by
  unfold tailWord_509427
  simp only [CollatzResearch.WordTrace]
  refine ⟨18580329125440457050030535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12386886083626971366687023 18580329125440457050030535)
  ·
    refine ⟨27870493688160685575045803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18580329125440457050030535 27870493688160685575045803)
    ·
      refine ⟨41805740532241028362568705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27870493688160685575045803 41805740532241028362568705)
      ·
        refine ⟨31354305399180771271926529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41805740532241028362568705 31354305399180771271926529)
        ·
          refine ⟨23515729049385578453944897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31354305399180771271926529 23515729049385578453944897)
          ·
            refine ⟨17636796787039183840458673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23515729049385578453944897 17636796787039183840458673)
            ·
              refine ⟨13227597590279387880344005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17636796787039183840458673 13227597590279387880344005)
              ·
                refine ⟨2480174548177385227564501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13227597590279387880344005 2480174548177385227564501)
                ·
                  refine ⟨58129090972907466271043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2480174548177385227564501 58129090972907466271043)
                  ·
                    rfl

theorem cell22_509427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 4, 7].length) (baseStart_509427 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_509427 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_509427 prefixEnd_509427 := by exact prefixLift 509427
  have htrace : WordTrace (prefixWord ++ tailWord_509427) baseStart_509427 baseEnd_509427 := by
    simpa [prefixWord, tailWord_509427, baseEnd_509427] using wordTrace_append hprefix tailTrace_509427
  have hstable : (prefixWord ++ tailWord_509427).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_509427).length < 2 ^ (prefixWord ++ tailWord_509427).sum := by decide
  have hdescent : baseEnd_509427 < baseStart_509427 := by decide
  rcases family_descends (prefixWord ++ tailWord_509427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_509459 : List Nat := [1, 1, 1, 2, 1, 7, 1, 1, 2, 5]
def baseStart_509459 : Nat := 118140960795 + 509459 * 2 ^ 59
def prefixEnd_509459 : Nat := 4983230072969 + 3 ^ 40 * 509459 * 2
def baseEnd_509459 : Nat := 174398227172684982013031

theorem tailTrace_509459 : CollatzResearch.WordTrace tailWord_509459 prefixEnd_509459 174398227172684982013031 := by
  unfold tailWord_509459
  simp only [CollatzResearch.WordTrace]
  refine ⟨18581496261324526515195431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12387664174216351010130287 18581496261324526515195431)
  ·
    refine ⟨27872244391986789772793147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18581496261324526515195431 27872244391986789772793147)
    ·
      refine ⟨41808366587980184659189721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27872244391986789772793147 41808366587980184659189721)
      ·
        refine ⟨31356274940985138494392291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41808366587980184659189721 31356274940985138494392291)
        ·
          refine ⟨47034412411477707741588437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31356274940985138494392291 47034412411477707741588437)
          ·
            refine ⟨1102369040894008775193479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 47034412411477707741588437 1102369040894008775193479)
            ·
              refine ⟨1653553561341013162790219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1102369040894008775193479 1653553561341013162790219)
              ·
                refine ⟨2480330342011519744185329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1653553561341013162790219 2480330342011519744185329)
                ·
                  refine ⟨1860247756508639808138997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2480330342011519744185329 1860247756508639808138997)
                  ·
                    refine ⟨174398227172684982013031, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1860247756508639808138997 174398227172684982013031)
                    ·
                      rfl

theorem cell22_509459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 7, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 7, 1, 1, 2, 5].length) (baseStart_509459 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_509459 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_509459 prefixEnd_509459 := by exact prefixLift 509459
  have htrace : WordTrace (prefixWord ++ tailWord_509459) baseStart_509459 baseEnd_509459 := by
    simpa [prefixWord, tailWord_509459, baseEnd_509459] using wordTrace_append hprefix tailTrace_509459
  have hstable : (prefixWord ++ tailWord_509459).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_509459).length < 2 ^ (prefixWord ++ tailWord_509459).sum := by decide
  have hdescent : baseEnd_509459 < baseStart_509459 := by decide
  rcases family_descends (prefixWord ++ tailWord_509459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_509491 : List Nat := [1, 1, 1, 2, 4, 4, 1, 3, 1, 4]
def baseStart_509491 : Nat := 118140960795 + 509491 * 2 ^ 59
def prefixEnd_509491 : Nat := 4983230072969 + 3 ^ 40 * 509491 * 2
def baseEnd_509491 : Nat := 174409181426647565212933

theorem tailTrace_509491 : CollatzResearch.WordTrace tailWord_509491 prefixEnd_509491 174409181426647565212933 := by
  unfold tailWord_509491
  simp only [CollatzResearch.WordTrace]
  refine ⟨18582663397208595980360327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12388442264805730653573551 18582663397208595980360327)
  ·
    refine ⟨27873995095812893970540491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18582663397208595980360327 27873995095812893970540491)
    ·
      refine ⟨41810992643719340955810737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27873995095812893970540491 41810992643719340955810737)
      ·
        refine ⟨31358244482789505716858053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41810992643719340955810737 31358244482789505716858053)
        ·
          refine ⟨5879670840523032321910885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31358244482789505716858053 5879670840523032321910885)
          ·
            refine ⟨1102438282598068560358291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5879670840523032321910885 1102438282598068560358291)
            ·
              refine ⟨1653657423897102840537437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1102438282598068560358291 1653657423897102840537437)
              ·
                refine ⟨620121533961413565201539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1653657423897102840537437 620121533961413565201539)
                ·
                  refine ⟨930182300942120347802309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 620121533961413565201539 930182300942120347802309)
                  ·
                    refine ⟨174409181426647565212933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 930182300942120347802309 174409181426647565212933)
                    ·
                      rfl

theorem cell22_509491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 4, 1, 3, 1, 4].length) (baseStart_509491 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_509491 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_509491 prefixEnd_509491 := by exact prefixLift 509491
  have htrace : WordTrace (prefixWord ++ tailWord_509491) baseStart_509491 baseEnd_509491 := by
    simpa [prefixWord, tailWord_509491, baseEnd_509491] using wordTrace_append hprefix tailTrace_509491
  have hstable : (prefixWord ++ tailWord_509491).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_509491).length < 2 ^ (prefixWord ++ tailWord_509491).sum := by decide
  have hdescent : baseEnd_509491 < baseStart_509491 := by decide
  rcases family_descends (prefixWord ++ tailWord_509491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_509564 : List Nat := [2, 2, 2, 1, 1, 2, 1, 3, 2, 6]
def baseStart_509564 : Nat := 118140960795 + 509564 * 2 ^ 59
def prefixEnd_509564 : Nat := 4983230072969 + 3 ^ 40 * 509564 * 2
def baseEnd_509564 : Nat := 174434170818499708137709

theorem tailTrace_509564 : CollatzResearch.WordTrace tailWord_509564 prefixEnd_509564 174434170818499708137709 := by
  unfold tailWord_509564
  simp only [CollatzResearch.WordTrace]
  refine ⟨9292662962972064723883873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12390217283962752965178497 9292662962972064723883873)
  ·
    refine ⟨6969497222229048542912905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9292662962972064723883873 6969497222229048542912905)
    ·
      refine ⟨5227122916671786407184679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6969497222229048542912905 5227122916671786407184679)
      ·
        refine ⟨7840684375007679610777019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5227122916671786407184679 7840684375007679610777019)
        ·
          refine ⟨11761026562511519416165529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7840684375007679610777019 11761026562511519416165529)
          ·
            refine ⟨8820769921883639562124147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11761026562511519416165529 8820769921883639562124147)
            ·
              refine ⟨13231154882825459343186221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8820769921883639562124147 13231154882825459343186221)
              ·
                refine ⟨4961683081059547253694833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13231154882825459343186221 4961683081059547253694833)
                ·
                  refine ⟨3721262310794660440271125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4961683081059547253694833 3721262310794660440271125)
                  ·
                    refine ⟨174434170818499708137709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3721262310794660440271125 174434170818499708137709)
                    ·
                      rfl

theorem cell22_509564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 3, 2, 6].length) (baseStart_509564 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_509564 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_509564 prefixEnd_509564 := by exact prefixLift 509564
  have htrace : WordTrace (prefixWord ++ tailWord_509564) baseStart_509564 baseEnd_509564 := by
    simpa [prefixWord, tailWord_509564, baseEnd_509564] using wordTrace_append hprefix tailTrace_509564
  have hstable : (prefixWord ++ tailWord_509564).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_509564).length < 2 ^ (prefixWord ++ tailWord_509564).sum := by decide
  have hdescent : baseEnd_509564 < baseStart_509564 := by decide
  rcases family_descends (prefixWord ++ tailWord_509564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_509572 : List Nat := [2, 3, 2, 1, 4, 2, 2, 1, 2, 3]
def baseStart_509572 : Nat := 118140960795 + 509572 * 2 ^ 59
def prefixEnd_509572 : Nat := 4983230072969 + 3 ^ 40 * 509572 * 2
def baseEnd_509572 : Nat := 174436909381990353937685

theorem tailTrace_509572 : CollatzResearch.WordTrace tailWord_509572 prefixEnd_509572 174436909381990353937685 := by
  unfold tailWord_509572
  simp only [CollatzResearch.WordTrace]
  refine ⟨9292808854957573407029485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12390411806610097876039313 9292808854957573407029485)
  ·
    refine ⟨3484803320609090027636057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9292808854957573407029485 3484803320609090027636057)
    ·
      refine ⟨2613602490456817520727043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3484803320609090027636057 2613602490456817520727043)
      ·
        refine ⟨3920403735685226281090565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2613602490456817520727043 3920403735685226281090565)
        ·
          refine ⟨735075700440979927704481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3920403735685226281090565 735075700440979927704481)
          ·
            refine ⟨551306775330734945778361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 735075700440979927704481 551306775330734945778361)
            ·
              refine ⟨413480081498051209333771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 551306775330734945778361 413480081498051209333771)
              ·
                refine ⟨620220122247076814000657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 413480081498051209333771 620220122247076814000657)
                ·
                  refine ⟨465165091685307610500493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 620220122247076814000657 465165091685307610500493)
                  ·
                    refine ⟨174436909381990353937685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 465165091685307610500493 174436909381990353937685)
                    ·
                      rfl

theorem cell22_509572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 2, 2, 1, 2, 3].length) (baseStart_509572 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_509572 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_509572 prefixEnd_509572 := by exact prefixLift 509572
  have htrace : WordTrace (prefixWord ++ tailWord_509572) baseStart_509572 baseEnd_509572 := by
    simpa [prefixWord, tailWord_509572, baseEnd_509572] using wordTrace_append hprefix tailTrace_509572
  have hstable : (prefixWord ++ tailWord_509572).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_509572).length < 2 ^ (prefixWord ++ tailWord_509572).sum := by decide
  have hdescent : baseEnd_509572 < baseStart_509572 := by decide
  rcases family_descends (prefixWord ++ tailWord_509572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_509613 : List Nat := [1, 5, 2, 1, 1, 1, 4, 2, 5]
def baseStart_509613 : Nat := 118140960795 + 509613 * 2 ^ 59
def prefixEnd_509613 : Nat := 4983230072969 + 3 ^ 40 * 509613 * 2
def baseEnd_509613 : Nat := 58150314839959971220853

theorem tailTrace_509613 : CollatzResearch.WordTrace tailWord_509613 prefixEnd_509613 58150314839959971220853 := by
  unfold tailWord_509613
  simp only [CollatzResearch.WordTrace]
  refine ⟨18587113102766610816301493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12391408735177740544200995 18587113102766610816301493)
  ·
    refine ⟨1742541853384369764028265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 18587113102766610816301493 1742541853384369764028265)
    ·
      refine ⟨1306906390038277323021199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1742541853384369764028265 1306906390038277323021199)
      ·
        refine ⟨1960359585057415984531799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1306906390038277323021199 1960359585057415984531799)
        ·
          refine ⟨2940539377586123976797699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1960359585057415984531799 2940539377586123976797699)
          ·
            refine ⟨4410809066379185965196549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2940539377586123976797699 4410809066379185965196549)
            ·
              refine ⟨827026699946097368474353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4410809066379185965196549 827026699946097368474353)
              ·
                refine ⟨620270024959573026355765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 827026699946097368474353 620270024959573026355765)
                ·
                  refine ⟨58150314839959971220853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 620270024959573026355765 58150314839959971220853)
                  ·
                    rfl

theorem cell22_509613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 4, 2, 5].length) (baseStart_509613 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_509613 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_509613 prefixEnd_509613 := by exact prefixLift 509613
  have htrace : WordTrace (prefixWord ++ tailWord_509613) baseStart_509613 baseEnd_509613 := by
    simpa [prefixWord, tailWord_509613, baseEnd_509613] using wordTrace_append hprefix tailTrace_509613
  have hstable : (prefixWord ++ tailWord_509613).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_509613).length < 2 ^ (prefixWord ++ tailWord_509613).sum := by decide
  have hdescent : baseEnd_509613 < baseStart_509613 := by decide
  rcases family_descends (prefixWord ++ tailWord_509613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_509624 : List Nat := [2, 1, 2, 1, 2, 1, 1, 2, 10]
def baseStart_509624 : Nat := 118140960795 + 509624 * 2 ^ 59
def prefixEnd_509624 : Nat := 4983230072969 + 3 ^ 40 * 509624 * 2
def baseEnd_509624 : Nat := 58151570014893183879175

theorem tailTrace_509624 : CollatzResearch.WordTrace tailWord_509624 prefixEnd_509624 58151570014893183879175 := by
  unfold tailWord_509624
  simp only [CollatzResearch.WordTrace]
  refine ⟨9293757152863379847475963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12391676203817839796634617 9293757152863379847475963)
  ·
    refine ⟨13940635729295069771213945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9293757152863379847475963 13940635729295069771213945)
    ·
      refine ⟨10455476796971302328410459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13940635729295069771213945 10455476796971302328410459)
      ·
        refine ⟨15683215195456953492615689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10455476796971302328410459 15683215195456953492615689)
        ·
          refine ⟨11762411396592715119461767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15683215195456953492615689 11762411396592715119461767)
          ·
            refine ⟨17643617094889072679192651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11762411396592715119461767 17643617094889072679192651)
            ·
              refine ⟨26465425642333609018788977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17643617094889072679192651 26465425642333609018788977)
              ·
                refine ⟨19849069231750206764091733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26465425642333609018788977 19849069231750206764091733)
                ·
                  refine ⟨58151570014893183879175, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 19849069231750206764091733 58151570014893183879175)
                  ·
                    rfl

theorem cell22_509624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 2, 10].length) (baseStart_509624 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_509624 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_509624 prefixEnd_509624 := by exact prefixLift 509624
  have htrace : WordTrace (prefixWord ++ tailWord_509624) baseStart_509624 baseEnd_509624 := by
    simpa [prefixWord, tailWord_509624, baseEnd_509624] using wordTrace_append hprefix tailTrace_509624
  have hstable : (prefixWord ++ tailWord_509624).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_509624).length < 2 ^ (prefixWord ++ tailWord_509624).sum := by decide
  have hdescent : baseEnd_509624 < baseStart_509624 := by decide
  rcases family_descends (prefixWord ++ tailWord_509624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_509626 : List Nat := [3, 1, 1, 1, 2, 4, 1, 2, 3, 4]
def baseStart_509626 : Nat := 118140960795 + 509626 * 2 ^ 59
def prefixEnd_509626 : Nat := 4983230072969 + 3 ^ 40 * 509626 * 2
def baseEnd_509626 : Nat := 174455394685552213087519

theorem tailTrace_509626 : CollatzResearch.WordTrace tailWord_509626 prefixEnd_509626 174455394685552213087519 := by
  unfold tailWord_509626
  simp only [CollatzResearch.WordTrace]
  refine ⟨4646896812929878509131183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12391724834479676024349821 4646896812929878509131183)
  ·
    refine ⟨6970345219394817763696775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4646896812929878509131183 6970345219394817763696775)
    ·
      refine ⟨10455517829092226645545163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6970345219394817763696775 10455517829092226645545163)
      ·
        refine ⟨15683276743638339968317745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10455517829092226645545163 15683276743638339968317745)
        ·
          refine ⟨11762457557728754976238309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15683276743638339968317745 11762457557728754976238309)
          ·
            refine ⟨2205460792074141558044683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11762457557728754976238309 2205460792074141558044683)
            ·
              refine ⟨3308191188111212337067025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2205460792074141558044683 3308191188111212337067025)
              ·
                refine ⟨2481143391083409252800269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3308191188111212337067025 2481143391083409252800269)
                ·
                  refine ⟨930428771656278469800101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2481143391083409252800269 930428771656278469800101)
                  ·
                    refine ⟨174455394685552213087519, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 930428771656278469800101 174455394685552213087519)
                    ·
                      rfl

theorem cell22_509626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 1, 2, 3, 4].length) (baseStart_509626 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_509626 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_509626 prefixEnd_509626 := by exact prefixLift 509626
  have htrace : WordTrace (prefixWord ++ tailWord_509626) baseStart_509626 baseEnd_509626 := by
    simpa [prefixWord, tailWord_509626, baseEnd_509626] using wordTrace_append hprefix tailTrace_509626
  have hstable : (prefixWord ++ tailWord_509626).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_509626).length < 2 ^ (prefixWord ++ tailWord_509626).sum := by decide
  have hdescent : baseEnd_509626 < baseStart_509626 := by decide
  rcases family_descends (prefixWord ++ tailWord_509626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_509634 : List Nat := [3, 5, 1, 2, 1, 1, 1, 2, 3, 3]
def baseStart_509634 : Nat := 118140960795 + 509634 * 2 ^ 59
def prefixEnd_509634 : Nat := 4983230072969 + 3 ^ 40 * 509634 * 2
def baseEnd_509634 : Nat := 174458133249042858887495

theorem tailTrace_509634 : CollatzResearch.WordTrace tailWord_509634 prefixEnd_509634 174458133249042858887495 := by
  unfold tailWord_509634
  simp only [CollatzResearch.WordTrace]
  refine ⟨4646969758922632850703989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12391919357127020935210637 4646969758922632850703989)
  ·
    refine ⟨435653414898996829753499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 4646969758922632850703989 435653414898996829753499)
    ·
      refine ⟨653480122348495244630249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 435653414898996829753499 653480122348495244630249)
      ·
        refine ⟨490110091761371433472687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 653480122348495244630249 490110091761371433472687)
        ·
          refine ⟨735165137642057150209031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 490110091761371433472687 735165137642057150209031)
          ·
            refine ⟨1102747706463085725313547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 735165137642057150209031 1102747706463085725313547)
            ·
              refine ⟨1654121559694628587970321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1102747706463085725313547 1654121559694628587970321)
              ·
                refine ⟨1240591169770971440977741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1654121559694628587970321 1240591169770971440977741)
                ·
                  refine ⟨465221688664114290366653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1240591169770971440977741 465221688664114290366653)
                  ·
                    refine ⟨174458133249042858887495, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 465221688664114290366653 174458133249042858887495)
                    ·
                      rfl

theorem cell22_509634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 1, 1, 2, 3, 3].length) (baseStart_509634 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_509634 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_509634 prefixEnd_509634 := by exact prefixLift 509634
  have htrace : WordTrace (prefixWord ++ tailWord_509634) baseStart_509634 baseEnd_509634 := by
    simpa [prefixWord, tailWord_509634, baseEnd_509634] using wordTrace_append hprefix tailTrace_509634
  have hstable : (prefixWord ++ tailWord_509634).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_509634).length < 2 ^ (prefixWord ++ tailWord_509634).sum := by decide
  have hdescent : baseEnd_509634 < baseStart_509634 := by decide
  rcases family_descends (prefixWord ++ tailWord_509634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_509656 : List Nat := [2, 1, 2, 2, 3, 1, 1, 4, 1, 5]
def baseStart_509656 : Nat := 118140960795 + 509656 * 2 ^ 59
def prefixEnd_509656 : Nat := 4983230072969 + 3 ^ 40 * 509656 * 2
def baseEnd_509656 : Nat := 174465664298642134837427

theorem tailTrace_509656 : CollatzResearch.WordTrace tailWord_509656 prefixEnd_509656 174465664298642134837427 := by
  unfold tailWord_509656
  simp only [CollatzResearch.WordTrace]
  refine ⟨9294340720805414580058411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12392454294407219440077881 9294340720805414580058411)
  ·
    refine ⟨13941511081208121870087617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9294340720805414580058411 13941511081208121870087617)
    ·
      refine ⟨10456133310906091402565713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13941511081208121870087617 10456133310906091402565713)
      ·
        refine ⟨7842099983179568551924285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10456133310906091402565713 7842099983179568551924285)
        ·
          refine ⟨2940787493692338206971607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7842099983179568551924285 2940787493692338206971607)
          ·
            refine ⟨4411181240538507310457411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2940787493692338206971607 4411181240538507310457411)
            ·
              refine ⟨6616771860807760965686117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4411181240538507310457411 6616771860807760965686117)
              ·
                refine ⟨1240644723901455181066147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6616771860807760965686117 1240644723901455181066147)
                ·
                  refine ⟨1860967085852182771599221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1240644723901455181066147 1860967085852182771599221)
                  ·
                    refine ⟨174465664298642134837427, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1860967085852182771599221 174465664298642134837427)
                    ·
                      rfl

theorem cell22_509656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 1, 4, 1, 5].length) (baseStart_509656 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_509656 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_509656 prefixEnd_509656 := by exact prefixLift 509656
  have htrace : WordTrace (prefixWord ++ tailWord_509656) baseStart_509656 baseEnd_509656 := by
    simpa [prefixWord, tailWord_509656, baseEnd_509656] using wordTrace_append hprefix tailTrace_509656
  have hstable : (prefixWord ++ tailWord_509656).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_509656).length < 2 ^ (prefixWord ++ tailWord_509656).sum := by decide
  have hdescent : baseEnd_509656 < baseStart_509656 := by decide
  rcases family_descends (prefixWord ++ tailWord_509656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_509658 : List Nat := [3, 1, 1, 2, 2, 3, 1, 5, 4]
def baseStart_509658 : Nat := 118140960795 + 509658 * 2 ^ 59
def prefixEnd_509658 : Nat := 4983230072969 + 3 ^ 40 * 509658 * 2
def baseEnd_509658 : Nat := 58155449646504932095807

theorem tailTrace_509658 : CollatzResearch.WordTrace tailWord_509658 prefixEnd_509658 58155449646504932095807 := by
  unfold tailWord_509658
  simp only [CollatzResearch.WordTrace]
  refine ⟨4647188596900895875422407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12392502925069055667793085 4647188596900895875422407)
  ·
    refine ⟨6970782895351343813133611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4647188596900895875422407 6970782895351343813133611)
    ·
      refine ⟨10456174343027015719700417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6970782895351343813133611 10456174343027015719700417)
      ·
        refine ⟨7842130757270261789775313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10456174343027015719700417 7842130757270261789775313)
        ·
          refine ⟨5881598067952696342331485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7842130757270261789775313 5881598067952696342331485)
          ·
            refine ⟨2205599275482261128374307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5881598067952696342331485 2205599275482261128374307)
            ·
              refine ⟨3308398913223391692561461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2205599275482261128374307 3308398913223391692561461)
              ·
                refine ⟨310162398114692971177637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3308398913223391692561461 310162398114692971177637)
                ·
                  refine ⟨58155449646504932095807, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 310162398114692971177637 58155449646504932095807)
                  ·
                    rfl

theorem cell22_509658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 1, 5, 4].length) (baseStart_509658 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_509658 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_509658 prefixEnd_509658 := by exact prefixLift 509658
  have htrace : WordTrace (prefixWord ++ tailWord_509658) baseStart_509658 baseEnd_509658 := by
    simpa [prefixWord, tailWord_509658, baseEnd_509658] using wordTrace_append hprefix tailTrace_509658
  have hstable : (prefixWord ++ tailWord_509658).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_509658).length < 2 ^ (prefixWord ++ tailWord_509658).sum := by decide
  have hdescent : baseEnd_509658 < baseStart_509658 := by decide
  rcases family_descends (prefixWord ++ tailWord_509658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_509702 : List Nat := [6, 2, 2, 1, 2, 1, 1, 3, 1, 3]
def baseStart_509702 : Nat := 118140960795 + 509702 * 2 ^ 59
def prefixEnd_509702 : Nat := 4983230072969 + 3 ^ 40 * 509702 * 2
def baseEnd_509702 : Nat := 174481411038713348187287

theorem tailTrace_509702 : CollatzResearch.WordTrace tailWord_509702 prefixEnd_509702 174481411038713348187287 := by
  unfold tailWord_509702
  simp only [CollatzResearch.WordTrace]
  refine ⟨580948724982630594259105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 12393572799629452677527573 580948724982630594259105)
  ·
    refine ⟨435711543736972945694329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 580948724982630594259105 435711543736972945694329)
    ·
      refine ⟨326783657802729709270747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 435711543736972945694329 326783657802729709270747)
      ·
        refine ⟨490175486704094563906121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 326783657802729709270747 490175486704094563906121)
        ·
          refine ⟨367631615028070922929591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 490175486704094563906121 367631615028070922929591)
          ·
            refine ⟨551447422542106384394387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 367631615028070922929591 551447422542106384394387)
            ·
              refine ⟨827171133813159576591581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 551447422542106384394387 827171133813159576591581)
              ·
                refine ⟨310189175179934841221843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 827171133813159576591581 310189175179934841221843)
                ·
                  refine ⟨465283762769902261832765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 310189175179934841221843 465283762769902261832765)
                  ·
                    refine ⟨174481411038713348187287, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 465283762769902261832765 174481411038713348187287)
                    ·
                      rfl

theorem cell22_509702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 2, 1, 1, 3, 1, 3].length) (baseStart_509702 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_509702 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_509702 prefixEnd_509702 := by exact prefixLift 509702
  have htrace : WordTrace (prefixWord ++ tailWord_509702) baseStart_509702 baseEnd_509702 := by
    simpa [prefixWord, tailWord_509702, baseEnd_509702] using wordTrace_append hprefix tailTrace_509702
  have hstable : (prefixWord ++ tailWord_509702).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_509702).length < 2 ^ (prefixWord ++ tailWord_509702).sum := by decide
  have hdescent : baseEnd_509702 < baseStart_509702 := by decide
  rcases family_descends (prefixWord ++ tailWord_509702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_509703 : List Nat := [1, 1, 4, 4, 2, 1, 1, 8]
def baseStart_509703 : Nat := 118140960795 + 509703 * 2 ^ 59
def prefixEnd_509703 : Nat := 4983230072969 + 3 ^ 40 * 509703 * 2
def baseEnd_509703 : Nat := 19386861484349964323587

theorem tailTrace_509703 : CollatzResearch.WordTrace tailWord_509703 prefixEnd_509703 19386861484349964323587 := by
  unfold tailWord_509703
  simp only [CollatzResearch.WordTrace]
  refine ⟨18590395672440556187077763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12393597114960370791385175 18590395672440556187077763)
  ·
    refine ⟨27885593508660834280616645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18590395672440556187077763 27885593508660834280616645)
    ·
      refine ⟨5228548782873906427615621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27885593508660834280616645 5228548782873906427615621)
      ·
        refine ⟨980352896788857455177929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5228548782873906427615621 980352896788857455177929)
        ·
          refine ⟨735264672591643091383447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 980352896788857455177929 735264672591643091383447)
          ·
            refine ⟨1102897008887464637075171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 735264672591643091383447 1102897008887464637075171)
            ·
              refine ⟨1654345513331196955612757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1102897008887464637075171 1654345513331196955612757)
              ·
                refine ⟨19386861484349964323587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1654345513331196955612757 19386861484349964323587)
                ·
                  rfl

theorem cell22_509703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 1, 1, 8].length) (baseStart_509703 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_509703 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_509703 prefixEnd_509703 := by exact prefixLift 509703
  have htrace : WordTrace (prefixWord ++ tailWord_509703) baseStart_509703 baseEnd_509703 := by
    simpa [prefixWord, tailWord_509703, baseEnd_509703] using wordTrace_append hprefix tailTrace_509703
  have hstable : (prefixWord ++ tailWord_509703).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_509703).length < 2 ^ (prefixWord ++ tailWord_509703).sum := by decide
  have hdescent : baseEnd_509703 < baseStart_509703 := by decide
  rcases family_descends (prefixWord ++ tailWord_509703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_509726 : List Nat := [4, 3, 2, 2, 1, 1, 3, 2, 4]
def baseStart_509726 : Nat := 118140960795 + 509726 * 2 ^ 59
def prefixEnd_509726 : Nat := 4983230072969 + 3 ^ 40 * 509726 * 2
def baseEnd_509726 : Nat := 58163208909728428529071

theorem tailTrace_509726 : CollatzResearch.WordTrace tailWord_509726 prefixEnd_509726 58163208909728428529071 := by
  unfold tailWord_509726
  simp only [CollatzResearch.WordTrace]
  refine ⟨2323904318919653889395629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12394156367571487410110021 2323904318919653889395629)
  ·
    refine ⟨871464119594870208523361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2323904318919653889395629 871464119594870208523361)
    ·
      refine ⟨653598089696152656392521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 871464119594870208523361 653598089696152656392521)
      ·
        refine ⟨490198567272114492294391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 653598089696152656392521 490198567272114492294391)
        ·
          refine ⟨735297850908171738441587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 490198567272114492294391 735297850908171738441587)
          ·
            refine ⟨1102946776362257607662381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 735297850908171738441587 1102946776362257607662381)
            ·
              refine ⟨413605041135846602873393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1102946776362257607662381 413605041135846602873393)
              ·
                refine ⟨310203780851884952155045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 413605041135846602873393 310203780851884952155045)
                ·
                  refine ⟨58163208909728428529071, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 310203780851884952155045 58163208909728428529071)
                  ·
                    rfl

theorem cell22_509726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 1, 3, 2, 4].length) (baseStart_509726 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_509726 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_509726 prefixEnd_509726 := by exact prefixLift 509726
  have htrace : WordTrace (prefixWord ++ tailWord_509726) baseStart_509726 baseEnd_509726 := by
    simpa [prefixWord, tailWord_509726, baseEnd_509726] using wordTrace_append hprefix tailTrace_509726
  have hstable : (prefixWord ++ tailWord_509726).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_509726).length < 2 ^ (prefixWord ++ tailWord_509726).sum := by decide
  have hdescent : baseEnd_509726 < baseStart_509726 := by decide
  rcases family_descends (prefixWord ++ tailWord_509726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_509731 : List Nat := [1, 1, 1, 4, 2, 1, 4, 1, 7]
def baseStart_509731 : Nat := 118140960795 + 509731 * 2 ^ 59
def prefixEnd_509731 : Nat := 4983230072969 + 3 ^ 40 * 509731 * 2
def baseEnd_509731 : Nat := 58163779443788979737399

theorem tailTrace_509731 : CollatzResearch.WordTrace tailWord_509731 prefixEnd_509731 58163779443788979737399 := by
  unfold tailWord_509731
  simp only [CollatzResearch.WordTrace]
  refine ⟨18591416916339116969097047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12394277944226077979398031 18591416916339116969097047)
  ·
    refine ⟨27887125374508675453645571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18591416916339116969097047 27887125374508675453645571)
    ·
      refine ⟨41830688061763013180468357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27887125374508675453645571 41830688061763013180468357)
      ·
        refine ⟨7843254011580564971337817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41830688061763013180468357 7843254011580564971337817)
        ·
          refine ⟨5882440508685423728503363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7843254011580564971337817 5882440508685423728503363)
          ·
            refine ⟨8823660763028135592755045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5882440508685423728503363 8823660763028135592755045)
            ·
              refine ⟨1654436393067775423641571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8823660763028135592755045 1654436393067775423641571)
              ·
                refine ⟨2481654589601663135462357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1654436393067775423641571 2481654589601663135462357)
                ·
                  refine ⟨58163779443788979737399, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2481654589601663135462357 58163779443788979737399)
                  ·
                    rfl

theorem cell22_509731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 4, 1, 7].length) (baseStart_509731 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_509731 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_509731 prefixEnd_509731 := by exact prefixLift 509731
  have htrace : WordTrace (prefixWord ++ tailWord_509731) baseStart_509731 baseEnd_509731 := by
    simpa [prefixWord, tailWord_509731, baseEnd_509731] using wordTrace_append hprefix tailTrace_509731
  have hstable : (prefixWord ++ tailWord_509731).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_509731).length < 2 ^ (prefixWord ++ tailWord_509731).sum := by decide
  have hdescent : baseEnd_509731 < baseStart_509731 := by decide
  rcases family_descends (prefixWord ++ tailWord_509731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_509808 : List Nat := [2, 1, 1, 1, 4, 1, 1, 2, 6, 3]
def baseStart_509808 : Nat := 118140960795 + 509808 * 2 ^ 59
def prefixEnd_509808 : Nat := 4983230072969 + 3 ^ 40 * 509808 * 2
def baseEnd_509808 : Nat := 174517697004964405036961

theorem tailTrace_509808 : CollatzResearch.WordTrace tailWord_509808 prefixEnd_509808 174517697004964405036961 := by
  unfold tailWord_509808
  simp only [CollatzResearch.WordTrace]
  refine ⟨9297112668530079559825039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12396150224706772746433385 9297112668530079559825039)
  ·
    refine ⟨13945669002795119339737559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9297112668530079559825039 13945669002795119339737559)
    ·
      refine ⟨20918503504192679009606339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13945669002795119339737559 20918503504192679009606339)
      ·
        refine ⟨31377755256289018514409509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20918503504192679009606339 31377755256289018514409509)
        ·
          refine ⟨5883329110554190971451783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31377755256289018514409509 5883329110554190971451783)
          ·
            refine ⟨8824993665831286457177675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5883329110554190971451783 8824993665831286457177675)
            ·
              refine ⟨13237490498746929685766513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8824993665831286457177675 13237490498746929685766513)
              ·
                refine ⟨9928117874060197264324885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13237490498746929685766513 9928117874060197264324885)
                ·
                  refine ⟨465380525346571746765229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9928117874060197264324885 465380525346571746765229)
                  ·
                    refine ⟨174517697004964405036961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 465380525346571746765229 174517697004964405036961)
                    ·
                      rfl

theorem cell22_509808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 2, 6, 3].length) (baseStart_509808 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_509808 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_509808 prefixEnd_509808 := by exact prefixLift 509808
  have htrace : WordTrace (prefixWord ++ tailWord_509808) baseStart_509808 baseEnd_509808 := by
    simpa [prefixWord, tailWord_509808, baseEnd_509808] using wordTrace_append hprefix tailTrace_509808
  have hstable : (prefixWord ++ tailWord_509808).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_509808).length < 2 ^ (prefixWord ++ tailWord_509808).sum := by decide
  have hdescent : baseEnd_509808 < baseStart_509808 := by decide
  rcases family_descends (prefixWord ++ tailWord_509808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_509842 : List Nat := [3, 2, 3, 2, 1, 2, 1, 1, 4, 3]
def baseStart_509842 : Nat := 118140960795 + 509842 * 2 ^ 59
def prefixEnd_509842 : Nat := 4983230072969 + 3 ^ 40 * 509842 * 2
def baseEnd_509842 : Nat := 174529335899799649686857

theorem tailTrace_509842 : CollatzResearch.WordTrace tailWord_509842 prefixEnd_509842 174529335899799649686857 := by
  unfold tailWord_509842
  simp only [CollatzResearch.WordTrace]
  refine ⟨4648866354734245731596945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12396976945957988617591853 4648866354734245731596945)
  ·
    refine ⟨3486649766050684298697709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4648866354734245731596945 3486649766050684298697709)
    ·
      refine ⟨1307493662269006612011641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3486649766050684298697709 1307493662269006612011641)
      ·
        refine ⟨980620246701754959008731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1307493662269006612011641 980620246701754959008731)
        ·
          refine ⟨1470930370052632438513097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 980620246701754959008731 1470930370052632438513097)
          ·
            refine ⟨1103197777539474328884823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1470930370052632438513097 1103197777539474328884823)
            ·
              refine ⟨1654796666309211493327235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1103197777539474328884823 1654796666309211493327235)
              ·
                refine ⟨2482194999463817239990853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1654796666309211493327235 2482194999463817239990853)
                ·
                  refine ⟨465411562399465732498285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2482194999463817239990853 465411562399465732498285)
                  ·
                    refine ⟨174529335899799649686857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 465411562399465732498285 174529335899799649686857)
                    ·
                      rfl

theorem cell22_509842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 2, 1, 1, 4, 3].length) (baseStart_509842 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_509842 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_509842 prefixEnd_509842 := by exact prefixLift 509842
  have htrace : WordTrace (prefixWord ++ tailWord_509842) baseStart_509842 baseEnd_509842 := by
    simpa [prefixWord, tailWord_509842, baseEnd_509842] using wordTrace_append hprefix tailTrace_509842
  have hstable : (prefixWord ++ tailWord_509842).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_509842).length < 2 ^ (prefixWord ++ tailWord_509842).sum := by decide
  have hdescent : baseEnd_509842 < baseStart_509842 := by decide
  rcases family_descends (prefixWord ++ tailWord_509842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_509898 : List Nat := [3, 1, 2, 1, 2, 1, 2, 1, 4, 5]
def baseStart_509898 : Nat := 118140960795 + 509898 * 2 ^ 59
def prefixEnd_509898 : Nat := 4983230072969 + 3 ^ 40 * 509898 * 2
def baseEnd_509898 : Nat := 174548505844234170286685

theorem tailTrace_509898 : CollatzResearch.WordTrace tailWord_509898 prefixEnd_509898 174548505844234170286685 := by
  unfold tailWord_509898
  simp only [CollatzResearch.WordTrace]
  refine ⟨4649376976683526122606587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12398338604489402993617565 4649376976683526122606587)
  ·
    refine ⟨6974065465025289183909881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4649376976683526122606587 6974065465025289183909881)
    ·
      refine ⟨5230549098768966887932411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6974065465025289183909881 5230549098768966887932411)
      ·
        refine ⟨7845823648153450331898617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5230549098768966887932411 7845823648153450331898617)
        ·
          refine ⟨5884367736115087748923963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7845823648153450331898617 5884367736115087748923963)
          ·
            refine ⟨8826551604172631623385945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5884367736115087748923963 8826551604172631623385945)
            ·
              refine ⟨6619913703129473717539459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8826551604172631623385945 6619913703129473717539459)
              ·
                refine ⟨9929870554694210576309189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6619913703129473717539459 9929870554694210576309189)
                ·
                  refine ⟨1861850729005164483057973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9929870554694210576309189 1861850729005164483057973)
                  ·
                    refine ⟨174548505844234170286685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1861850729005164483057973 174548505844234170286685)
                    ·
                      rfl

theorem cell22_509898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 2, 1, 4, 5].length) (baseStart_509898 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_509898 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_509898 prefixEnd_509898 := by exact prefixLift 509898
  have htrace : WordTrace (prefixWord ++ tailWord_509898) baseStart_509898 baseEnd_509898 := by
    simpa [prefixWord, tailWord_509898, baseEnd_509898] using wordTrace_append hprefix tailTrace_509898
  have hstable : (prefixWord ++ tailWord_509898).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_509898).length < 2 ^ (prefixWord ++ tailWord_509898).sum := by decide
  have hdescent : baseEnd_509898 < baseStart_509898 := by decide
  rcases family_descends (prefixWord ++ tailWord_509898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_509917 : List Nat := [1, 4, 3, 1, 3, 1, 1, 3, 5]
def baseStart_509917 : Nat := 118140960795 + 509917 * 2 ^ 59
def prefixEnd_509917 : Nat := 4983230072969 + 3 ^ 40 * 509917 * 2
def baseEnd_509917 : Nat := 58185003310841484687209

theorem tailTrace_509917 : CollatzResearch.WordTrace tailWord_509917 prefixEnd_509917 58185003310841484687209 := by
  unfold tailWord_509917
  simp only [CollatzResearch.WordTrace]
  refine ⟨18598200893665270735368005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12398800595776847156912003 18598200893665270735368005)
  ·
    refine ⟨3487162667562238262881501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18598200893665270735368005 3487162667562238262881501)
    ·
      refine ⟨1307686000335839348580563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3487162667562238262881501 1307686000335839348580563)
      ·
        refine ⟨1961529000503759022870845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1307686000335839348580563 1961529000503759022870845)
        ·
          refine ⟨735573375188909633576567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1961529000503759022870845 735573375188909633576567)
          ·
            refine ⟨1103360062783364450364851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 735573375188909633576567 1103360062783364450364851)
            ·
              refine ⟨1655040094175046675547277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1103360062783364450364851 1655040094175046675547277)
              ·
                refine ⟨620640035315642503330229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1655040094175046675547277 620640035315642503330229)
                ·
                  refine ⟨58185003310841484687209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 620640035315642503330229 58185003310841484687209)
                  ·
                    rfl

theorem cell22_509917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 1, 1, 3, 5].length) (baseStart_509917 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_509917 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_509917 prefixEnd_509917 := by exact prefixLift 509917
  have htrace : WordTrace (prefixWord ++ tailWord_509917) baseStart_509917 baseEnd_509917 := by
    simpa [prefixWord, tailWord_509917, baseEnd_509917] using wordTrace_append hprefix tailTrace_509917
  have hstable : (prefixWord ++ tailWord_509917).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_509917).length < 2 ^ (prefixWord ++ tailWord_509917).sum := by decide
  have hdescent : baseEnd_509917 < baseStart_509917 := by decide
  rcases family_descends (prefixWord ++ tailWord_509917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_509928 : List Nat := [2, 1, 4, 1, 1, 1, 1, 3, 8]
def baseStart_509928 : Nat := 118140960795 + 509928 * 2 ^ 59
def prefixEnd_509928 : Nat := 4983230072969 + 3 ^ 40 * 509928 * 2
def baseEnd_509928 : Nat := 58186258485774697345531

theorem tailTrace_509928 : CollatzResearch.WordTrace tailWord_509928 prefixEnd_509928 58186258485774697345531 := by
  unfold tailWord_509928
  simp only [CollatzResearch.WordTrace]
  refine ⟨9299301048312709807009219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12399068064416946409345625 9299301048312709807009219)
  ·
    refine ⟨13948951572469064710513829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9299301048312709807009219 13948951572469064710513829)
    ·
      refine ⟨2615428419837949633221343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13948951572469064710513829 2615428419837949633221343)
      ·
        refine ⟨3923142629756924449832015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2615428419837949633221343 3923142629756924449832015)
        ·
          refine ⟨5884713944635386674748023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3923142629756924449832015 5884713944635386674748023)
          ·
            refine ⟨8827070916953080012122035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5884713944635386674748023 8827070916953080012122035)
            ·
              refine ⟨13240606375429620018183053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8827070916953080012122035 13240606375429620018183053)
              ·
                refine ⟨4965227390786107506818645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13240606375429620018183053 4965227390786107506818645)
                ·
                  refine ⟨58186258485774697345531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 4965227390786107506818645 58186258485774697345531)
                  ·
                    rfl

theorem cell22_509928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 3, 8].length) (baseStart_509928 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_509928 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_509928 prefixEnd_509928 := by exact prefixLift 509928
  have htrace : WordTrace (prefixWord ++ tailWord_509928) baseStart_509928 baseEnd_509928 := by
    simpa [prefixWord, tailWord_509928, baseEnd_509928] using wordTrace_append hprefix tailTrace_509928
  have hstable : (prefixWord ++ tailWord_509928).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_509928).length < 2 ^ (prefixWord ++ tailWord_509928).sum := by decide
  have hdescent : baseEnd_509928 < baseStart_509928 := by decide
  rcases family_descends (prefixWord ++ tailWord_509928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_509930 : List Nat := [3, 1, 3, 1, 2, 1, 3, 1, 3, 4]
def baseStart_509930 : Nat := 118140960795 + 509930 * 2 ^ 59
def prefixEnd_509930 : Nat := 4983230072969 + 3 ^ 40 * 509930 * 2
def baseEnd_509930 : Nat := 174559460098196753486587

theorem tailTrace_509930 : CollatzResearch.WordTrace tailWord_509930 prefixEnd_509930 174559460098196753486587 := by
  unfold tailWord_509930
  simp only [CollatzResearch.WordTrace]
  refine ⟨4649668760654543488897811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12399116695078782637060829 4649668760654543488897811)
  ·
    refine ⟨6974503140981815233346717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4649668760654543488897811 6974503140981815233346717)
    ·
      refine ⟨2615438677868180712505019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6974503140981815233346717 2615438677868180712505019)
      ·
        refine ⟨3923158016802271068757529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2615438677868180712505019 3923158016802271068757529)
        ·
          refine ⟨2942368512601703301568147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3923158016802271068757529 2942368512601703301568147)
          ·
            refine ⟨4413552768902554952352221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2942368512601703301568147 4413552768902554952352221)
            ·
              refine ⟨1655082288338458107132083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4413552768902554952352221 1655082288338458107132083)
              ·
                refine ⟨2482623432507687160698125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1655082288338458107132083 2482623432507687160698125)
                ·
                  refine ⟨930983787190382685261797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2482623432507687160698125 930983787190382685261797)
                  ·
                    refine ⟨174559460098196753486587, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 930983787190382685261797 174559460098196753486587)
                    ·
                      rfl

theorem cell22_509930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 3, 1, 3, 4].length) (baseStart_509930 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_509930 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_509930 prefixEnd_509930 := by exact prefixLift 509930
  have htrace : WordTrace (prefixWord ++ tailWord_509930) baseStart_509930 baseEnd_509930 := by
    simpa [prefixWord, tailWord_509930, baseEnd_509930] using wordTrace_append hprefix tailTrace_509930
  have hstable : (prefixWord ++ tailWord_509930).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_509930).length < 2 ^ (prefixWord ++ tailWord_509930).sum := by decide
  have hdescent : baseEnd_509930 < baseStart_509930 := by decide
  rcases family_descends (prefixWord ++ tailWord_509930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_510112 : List Nat := [2, 1, 1, 4, 2, 3, 1, 2, 1, 5]
def baseStart_510112 : Nat := 118140960795 + 510112 * 2 ^ 59
def prefixEnd_510112 : Nat := 4983230072969 + 3 ^ 40 * 510112 * 2
def baseEnd_510112 : Nat := 174621762417608945436029

theorem tailTrace_510112 : CollatzResearch.WordTrace tailWord_510112 prefixEnd_510112 174621762417608945436029 := by
  unfold tailWord_510112
  simp only [CollatzResearch.WordTrace]
  refine ⟨9302656563979409519358295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12403542085305879359144393 9302656563979409519358295)
  ·
    refine ⟨13953984845969114279037443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9302656563979409519358295 13953984845969114279037443)
    ·
      refine ⟨20930977268953671418556165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13953984845969114279037443 20930977268953671418556165)
      ·
        refine ⟨3924558237928813390979281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20930977268953671418556165 3924558237928813390979281)
        ·
          refine ⟨2943418678446610043234461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3924558237928813390979281 2943418678446610043234461)
          ·
            refine ⟨1103782004417478766212923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2943418678446610043234461 1103782004417478766212923)
            ·
              refine ⟨1655673006626218149319385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1103782004417478766212923 1655673006626218149319385)
              ·
                refine ⟨1241754754969663611989539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1655673006626218149319385 1241754754969663611989539)
                ·
                  refine ⟨1862632132454495417984309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1241754754969663611989539 1862632132454495417984309)
                  ·
                    refine ⟨174621762417608945436029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1862632132454495417984309 174621762417608945436029)
                    ·
                      rfl

theorem cell22_510112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 3, 1, 2, 1, 5].length) (baseStart_510112 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_510112 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_510112 prefixEnd_510112 := by exact prefixLift 510112
  have htrace : WordTrace (prefixWord ++ tailWord_510112) baseStart_510112 baseEnd_510112 := by
    simpa [prefixWord, tailWord_510112, baseEnd_510112] using wordTrace_append hprefix tailTrace_510112
  have hstable : (prefixWord ++ tailWord_510112).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_510112).length < 2 ^ (prefixWord ++ tailWord_510112).sum := by decide
  have hdescent : baseEnd_510112 < baseStart_510112 := by decide
  rcases family_descends (prefixWord ++ tailWord_510112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_510116 : List Nat := [2, 3, 1, 2, 4, 1, 3, 1, 1, 4]
def baseStart_510116 : Nat := 118140960795 + 510116 * 2 ^ 59
def prefixEnd_510116 : Nat := 4983230072969 + 3 ^ 40 * 510116 * 2
def baseEnd_510116 : Nat := 174623131699354268336017

theorem tailTrace_510116 : CollatzResearch.WordTrace tailWord_510116 prefixEnd_510116 174623131699354268336017 := by
  unfold tailWord_510116
  simp only [CollatzResearch.WordTrace]
  refine ⟨9302729509972163860931101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12403639346629551814574801 9302729509972163860931101)
  ·
    refine ⟨3488523566239561447849163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9302729509972163860931101 3488523566239561447849163)
    ·
      refine ⟨5232785349359342171773745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3488523566239561447849163 5232785349359342171773745)
      ·
        refine ⟨3924589012019506628830309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5232785349359342171773745 3924589012019506628830309)
        ·
          refine ⟨735860439753657492905683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3924589012019506628830309 735860439753657492905683)
          ·
            refine ⟨1103790659630486239358525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 735860439753657492905683 1103790659630486239358525)
            ·
              refine ⟨413921497361432339759447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1103790659630486239358525 413921497361432339759447)
              ·
                refine ⟨620882246042148509639171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 413921497361432339759447 620882246042148509639171)
                ·
                  refine ⟨931323369063222764458757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 620882246042148509639171 931323369063222764458757)
                  ·
                    refine ⟨174623131699354268336017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 931323369063222764458757 174623131699354268336017)
                    ·
                      rfl

theorem cell22_510116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 1, 3, 1, 1, 4].length) (baseStart_510116 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_510116 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_510116 prefixEnd_510116 := by exact prefixLift 510116
  have htrace : WordTrace (prefixWord ++ tailWord_510116) baseStart_510116 baseEnd_510116 := by
    simpa [prefixWord, tailWord_510116, baseEnd_510116] using wordTrace_append hprefix tailTrace_510116
  have hstable : (prefixWord ++ tailWord_510116).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_510116).length < 2 ^ (prefixWord ++ tailWord_510116).sum := by decide
  have hdescent : baseEnd_510116 < baseStart_510116 := by decide
  rcases family_descends (prefixWord ++ tailWord_510116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_510146 : List Nat := [3, 5, 1, 1, 1, 1, 1, 3, 1, 5]
def baseStart_510146 : Nat := 118140960795 + 510146 * 2 ^ 59
def prefixEnd_510146 : Nat := 4983230072969 + 3 ^ 40 * 510146 * 2
def baseEnd_510146 : Nat := 174633401312444190085925

theorem tailTrace_510146 : CollatzResearch.WordTrace tailWord_510146 prefixEnd_510146 174633401312444190085925 := by
  unfold tailWord_510146
  simp only [CollatzResearch.WordTrace]
  refine ⟨4651638302458910711363573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12404368806557095230302861 4651638302458910711363573)
  ·
    refine ⟨436091090855522879190335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 4651638302458910711363573 436091090855522879190335)
    ·
      refine ⟨654136636283284318785503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 436091090855522879190335 654136636283284318785503)
      ·
        refine ⟨981204954424926478178255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 654136636283284318785503 981204954424926478178255)
        ·
          refine ⟨1471807431637389717267383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 981204954424926478178255 1471807431637389717267383)
          ·
            refine ⟨2207711147456084575901075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1471807431637389717267383 2207711147456084575901075)
            ·
              refine ⟨3311566721184126863851613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2207711147456084575901075 3311566721184126863851613)
              ·
                refine ⟨1241837520444047573944355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3311566721184126863851613 1241837520444047573944355)
                ·
                  refine ⟨1862756280666071360916533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1241837520444047573944355 1862756280666071360916533)
                  ·
                    refine ⟨174633401312444190085925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1862756280666071360916533 174633401312444190085925)
                    ·
                      rfl

theorem cell22_510146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 1, 3, 1, 5].length) (baseStart_510146 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_510146 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_510146 prefixEnd_510146 := by exact prefixLift 510146
  have htrace : WordTrace (prefixWord ++ tailWord_510146) baseStart_510146 baseEnd_510146 := by
    simpa [prefixWord, tailWord_510146, baseEnd_510146] using wordTrace_append hprefix tailTrace_510146
  have hstable : (prefixWord ++ tailWord_510146).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_510146).length < 2 ^ (prefixWord ++ tailWord_510146).sum := by decide
  have hdescent : baseEnd_510146 < baseStart_510146 := by decide
  rcases family_descends (prefixWord ++ tailWord_510146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_510155 : List Nat := [1, 1, 1, 1, 3, 2, 3, 2, 2, 6]
def baseStart_510155 : Nat := 118140960795 + 510155 * 2 ^ 59
def prefixEnd_510155 : Nat := 4983230072969 + 3 ^ 40 * 510155 * 2
def baseEnd_510155 : Nat := 174636482196371166610897

theorem tailTrace_510155 : CollatzResearch.WordTrace tailWord_510155 prefixEnd_510155 174636482196371166610897 := by
  unfold tailWord_510155
  simp only [CollatzResearch.WordTrace]
  refine ⟨18606881466803037382531919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12404587644535358255021279 18606881466803037382531919)
  ·
    refine ⟨27910322200204556073797879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18606881466803037382531919 27910322200204556073797879)
    ·
      refine ⟨41865483300306834110696819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27910322200204556073797879 41865483300306834110696819)
      ·
        refine ⟨62798224950460251166045229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41865483300306834110696819 62798224950460251166045229)
        ·
          refine ⟨23549334356422594187266961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62798224950460251166045229 23549334356422594187266961)
          ·
            refine ⟨17662000767316945640450221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23549334356422594187266961 17662000767316945640450221)
            ·
              refine ⟨6623250287743854615168833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17662000767316945640450221 6623250287743854615168833)
              ·
                refine ⟨4967437715807890961376625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6623250287743854615168833 4967437715807890961376625)
                ·
                  refine ⟨3725578286855918221032469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4967437715807890961376625 3725578286855918221032469)
                  ·
                    refine ⟨174636482196371166610897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3725578286855918221032469 174636482196371166610897)
                    ·
                      rfl

theorem cell22_510155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 3, 2, 2, 6].length) (baseStart_510155 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_510155 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_510155 prefixEnd_510155 := by exact prefixLift 510155
  have htrace : WordTrace (prefixWord ++ tailWord_510155) baseStart_510155 baseEnd_510155 := by
    simpa [prefixWord, tailWord_510155, baseEnd_510155] using wordTrace_append hprefix tailTrace_510155
  have hstable : (prefixWord ++ tailWord_510155).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_510155).length < 2 ^ (prefixWord ++ tailWord_510155).sum := by decide
  have hdescent : baseEnd_510155 < baseStart_510155 := by decide
  rcases family_descends (prefixWord ++ tailWord_510155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_510185 : List Nat := [1, 2, 1, 1, 1, 2, 2, 2, 3, 7]
def baseStart_510185 : Nat := 118140960795 + 510185 * 2 ^ 59
def prefixEnd_510185 : Nat := 4983230072969 + 3 ^ 40 * 510185 * 2
def baseEnd_510185 : Nat := 174646751809461088360805

theorem tailTrace_510185 : CollatzResearch.WordTrace tailWord_510185 prefixEnd_510185 174646751809461088360805 := by
  unfold tailWord_510185
  simp only [CollatzResearch.WordTrace]
  refine ⟨18607975656694352506124009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12405317104462901670749339 18607975656694352506124009)
  ·
    refine ⟨13955981742520764379593007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18607975656694352506124009 13955981742520764379593007)
    ·
      refine ⟨20933972613781146569389511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13955981742520764379593007 20933972613781146569389511)
      ·
        refine ⟨31400958920671719854084267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20933972613781146569389511 31400958920671719854084267)
        ·
          refine ⟨47101438381007579781126401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31400958920671719854084267 47101438381007579781126401)
          ·
            refine ⟨35326078785755684835844801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47101438381007579781126401 35326078785755684835844801)
            ·
              refine ⟨26494559089316763626883601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35326078785755684835844801 26494559089316763626883601)
              ·
                refine ⟨19870919316987572720162701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26494559089316763626883601 19870919316987572720162701)
                ·
                  refine ⟨7451594743870339770061013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19870919316987572720162701 7451594743870339770061013)
                  ·
                    refine ⟨174646751809461088360805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 7451594743870339770061013 174646751809461088360805)
                    ·
                      rfl

theorem cell22_510185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 2, 3, 7].length) (baseStart_510185 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_510185 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_510185 prefixEnd_510185 := by exact prefixLift 510185
  have htrace : WordTrace (prefixWord ++ tailWord_510185) baseStart_510185 baseEnd_510185 := by
    simpa [prefixWord, tailWord_510185, baseEnd_510185] using wordTrace_append hprefix tailTrace_510185
  have hstable : (prefixWord ++ tailWord_510185).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_510185).length < 2 ^ (prefixWord ++ tailWord_510185).sum := by decide
  have hdescent : baseEnd_510185 < baseStart_510185 := by decide
  rcases family_descends (prefixWord ++ tailWord_510185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_510191 : List Nat := [1, 1, 2, 1, 6, 1, 2, 4, 1, 3]
def baseStart_510191 : Nat := 118140960795 + 510191 * 2 ^ 59
def prefixEnd_510191 : Nat := 4983230072969 + 3 ^ 40 * 510191 * 2
def baseEnd_510191 : Nat := 174648805732079072710787

theorem tailTrace_510191 : CollatzResearch.WordTrace tailWord_510191 prefixEnd_510191 174648805732079072710787 := by
  unfold tailWord_510191
  simp only [CollatzResearch.WordTrace]
  refine ⟨18608194494672615530842427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12405462996448410353894951 18608194494672615530842427)
  ·
    refine ⟨27912291742008923296263641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18608194494672615530842427 27912291742008923296263641)
    ·
      refine ⟨20934218806506692472197731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27912291742008923296263641 20934218806506692472197731)
      ·
        refine ⟨31401328209760038708296597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20934218806506692472197731 31401328209760038708296597)
        ·
          refine ⟨1471937259832501814451403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 31401328209760038708296597 1471937259832501814451403)
          ·
            refine ⟨2207905889748752721677105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1471937259832501814451403 2207905889748752721677105)
            ·
              refine ⟨1655929417311564541257829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2207905889748752721677105 1655929417311564541257829)
              ·
                refine ⟨310486765745918351485843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1655929417311564541257829 310486765745918351485843)
                ·
                  refine ⟨465730148618877527228765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 310486765745918351485843 465730148618877527228765)
                  ·
                    refine ⟨174648805732079072710787, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 465730148618877527228765 174648805732079072710787)
                    ·
                      rfl

theorem cell22_510191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 2, 4, 1, 3].length) (baseStart_510191 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_510191 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_510191 prefixEnd_510191 := by exact prefixLift 510191
  have htrace : WordTrace (prefixWord ++ tailWord_510191) baseStart_510191 baseEnd_510191 := by
    simpa [prefixWord, tailWord_510191, baseEnd_510191] using wordTrace_append hprefix tailTrace_510191
  have hstable : (prefixWord ++ tailWord_510191).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_510191).length < 2 ^ (prefixWord ++ tailWord_510191).sum := by decide
  have hdescent : baseEnd_510191 < baseStart_510191 := by decide
  rcases family_descends (prefixWord ++ tailWord_510191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_510202 : List Nat := [3, 1, 1, 1, 1, 5, 2, 1, 2, 5]
def baseStart_510202 : Nat := 118140960795 + 510202 * 2 ^ 59
def prefixEnd_510202 : Nat := 4983230072969 + 3 ^ 40 * 510202 * 2
def baseEnd_510202 : Nat := 174652571256878710685753

theorem tailTrace_510202 : CollatzResearch.WordTrace tailWord_510202 prefixEnd_510202 174652571256878710685753 := by
  unfold tailWord_510202
  simp only [CollatzResearch.WordTrace]
  refine ⟨4652148924408191102373215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12405730465088509606328573 4652148924408191102373215)
  ·
    refine ⟨6978223386612286653559823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4652148924408191102373215 6978223386612286653559823)
    ·
      refine ⟨10467335079918429980339735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6978223386612286653559823 10467335079918429980339735)
      ·
        refine ⟨15701002619877644970509603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10467335079918429980339735 15701002619877644970509603)
        ·
          refine ⟨23551503929816467455764405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15701002619877644970509603 23551503929816467455764405)
          ·
            refine ⟨2207953493420293823977913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 23551503929816467455764405 2207953493420293823977913)
            ·
              refine ⟨1655965120065220367983435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2207953493420293823977913 1655965120065220367983435)
              ·
                refine ⟨2483947680097830551975153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1655965120065220367983435 2483947680097830551975153)
                ·
                  refine ⟨1862960760073372913981365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2483947680097830551975153 1862960760073372913981365)
                  ·
                    refine ⟨174652571256878710685753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1862960760073372913981365 174652571256878710685753)
                    ·
                      rfl

theorem cell22_510202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 2, 1, 2, 5].length) (baseStart_510202 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_510202 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_510202 prefixEnd_510202 := by exact prefixLift 510202
  have htrace : WordTrace (prefixWord ++ tailWord_510202) baseStart_510202 baseEnd_510202 := by
    simpa [prefixWord, tailWord_510202, baseEnd_510202] using wordTrace_append hprefix tailTrace_510202
  have hstable : (prefixWord ++ tailWord_510202).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_510202).length < 2 ^ (prefixWord ++ tailWord_510202).sum := by decide
  have hdescent : baseEnd_510202 < baseStart_510202 := by decide
  rcases family_descends (prefixWord ++ tailWord_510202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_510279 : List Nat := [1, 1, 4, 1, 2, 2, 4, 1, 2, 4]
def baseStart_510279 : Nat := 118140960795 + 510279 * 2 ^ 59
def prefixEnd_510279 : Nat := 4983230072969 + 3 ^ 40 * 510279 * 2
def baseEnd_510279 : Nat := 174678929930476176510517

theorem tailTrace_510279 : CollatzResearch.WordTrace tailWord_510279 prefixEnd_510279 174678929930476176510517 := by
  unfold tailWord_510279
  simp only [CollatzResearch.WordTrace]
  refine ⟨18611404118353806560045891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12407602745569204373363927 18611404118353806560045891)
  ·
    refine ⟨27917106177530709840068837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18611404118353806560045891 27917106177530709840068837)
    ·
      refine ⟨5234457408287008095012907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27917106177530709840068837 5234457408287008095012907)
      ·
        refine ⟨7851686112430512142519361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5234457408287008095012907 7851686112430512142519361)
        ·
          refine ⟨5888764584322884106889521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7851686112430512142519361 5888764584322884106889521)
          ·
            refine ⟨4416573438242163080167141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5888764584322884106889521 4416573438242163080167141)
            ·
              refine ⟨828107519670405577531339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4416573438242163080167141 828107519670405577531339)
              ·
                refine ⟨1242161279505608366297009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 828107519670405577531339 1242161279505608366297009)
                ·
                  refine ⟨931620959629206274722757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1242161279505608366297009 931620959629206274722757)
                  ·
                    refine ⟨174678929930476176510517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 931620959629206274722757 174678929930476176510517)
                    ·
                      rfl

theorem cell22_510279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 4, 1, 2, 4].length) (baseStart_510279 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_510279 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_510279 prefixEnd_510279 := by exact prefixLift 510279
  have htrace : WordTrace (prefixWord ++ tailWord_510279) baseStart_510279 baseEnd_510279 := by
    simpa [prefixWord, tailWord_510279, baseEnd_510279] using wordTrace_append hprefix tailTrace_510279
  have hstable : (prefixWord ++ tailWord_510279).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_510279).length < 2 ^ (prefixWord ++ tailWord_510279).sum := by decide
  have hdescent : baseEnd_510279 < baseStart_510279 := by decide
  rcases family_descends (prefixWord ++ tailWord_510279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_510307 : List Nat := [1, 1, 1, 5, 2, 1, 1, 1, 1, 8]
def baseStart_510307 : Nat := 118140960795 + 510307 * 2 ^ 59
def prefixEnd_510307 : Nat := 4983230072969 + 3 ^ 40 * 510307 * 2
def baseEnd_510307 : Nat := 174688514902693436810431

theorem tailTrace_510307 : CollatzResearch.WordTrace tailWord_510307 prefixEnd_510307 174688514902693436810431 := by
  unfold tailWord_510307
  simp only [CollatzResearch.WordTrace]
  refine ⟨18612425362252367342065175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12408283574834911561376783 18612425362252367342065175)
  ·
    refine ⟨27918638043378551013097763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18612425362252367342065175 27918638043378551013097763)
    ·
      refine ⟨41877957065067826519646645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27918638043378551013097763 41877957065067826519646645)
      ·
        refine ⟨3926058474850108736216873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 41877957065067826519646645 3926058474850108736216873)
        ·
          refine ⟨2944543856137581552162655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3926058474850108736216873 2944543856137581552162655)
          ·
            refine ⟨4416815784206372328243983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2944543856137581552162655 4416815784206372328243983)
            ·
              refine ⟨6625223676309558492365975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4416815784206372328243983 6625223676309558492365975)
              ·
                refine ⟨9937835514464337738548963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6625223676309558492365975 9937835514464337738548963)
                ·
                  refine ⟨14906753271696506607823445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9937835514464337738548963 14906753271696506607823445)
                  ·
                    refine ⟨174688514902693436810431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 14906753271696506607823445 174688514902693436810431)
                    ·
                      rfl

theorem cell22_510307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 1, 1, 1, 8].length) (baseStart_510307 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_510307 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_510307 prefixEnd_510307 := by exact prefixLift 510307
  have htrace : WordTrace (prefixWord ++ tailWord_510307) baseStart_510307 baseEnd_510307 := by
    simpa [prefixWord, tailWord_510307, baseEnd_510307] using wordTrace_append hprefix tailTrace_510307
  have hstable : (prefixWord ++ tailWord_510307).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_510307).length < 2 ^ (prefixWord ++ tailWord_510307).sum := by decide
  have hdescent : baseEnd_510307 < baseStart_510307 := by decide
  rcases family_descends (prefixWord ++ tailWord_510307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_510343 : List Nat := [1, 1, 4, 2, 2, 1, 4, 3, 1, 3]
def baseStart_510343 : Nat := 118140960795 + 510343 * 2 ^ 59
def prefixEnd_510343 : Nat := 4983230072969 + 3 ^ 40 * 510343 * 2
def baseEnd_510343 : Nat := 174700838438401342910321

theorem tailTrace_510343 : CollatzResearch.WordTrace tailWord_510343 prefixEnd_510343 174700838438401342910321 := by
  unfold tailWord_510343
  simp only [CollatzResearch.WordTrace]
  refine ⟨18613738390121945490375683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12409158926747963660250455 18613738390121945490375683)
  ·
    refine ⟨27920607585182918235563525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18613738390121945490375683 27920607585182918235563525)
    ·
      refine ⟨5235113922221797169168161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27920607585182918235563525 5235113922221797169168161)
      ·
        refine ⟨3926335441666347876876121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5235113922221797169168161 3926335441666347876876121)
        ·
          refine ⟨2944751581249760907657091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3926335441666347876876121 2944751581249760907657091)
          ·
            refine ⟨4417127371874641361485637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2944751581249760907657091 4417127371874641361485637)
            ·
              refine ⟨828211382226495255278557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4417127371874641361485637 828211382226495255278557)
              ·
                refine ⟨310579268334935720729459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 828211382226495255278557 310579268334935720729459)
                ·
                  refine ⟨465868902502403581094189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 310579268334935720729459 465868902502403581094189)
                  ·
                    refine ⟨174700838438401342910321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 465868902502403581094189 174700838438401342910321)
                    ·
                      rfl

theorem cell22_510343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 4, 3, 1, 3].length) (baseStart_510343 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_510343 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_510343 prefixEnd_510343 := by exact prefixLift 510343
  have htrace : WordTrace (prefixWord ++ tailWord_510343) baseStart_510343 baseEnd_510343 := by
    simpa [prefixWord, tailWord_510343, baseEnd_510343] using wordTrace_append hprefix tailTrace_510343
  have hstable : (prefixWord ++ tailWord_510343).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_510343).length < 2 ^ (prefixWord ++ tailWord_510343).sum := by decide
  have hdescent : baseEnd_510343 < baseStart_510343 := by decide
  rcases family_descends (prefixWord ++ tailWord_510343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_510356 : List Nat := [2, 4, 2, 1, 3, 1, 1, 1, 7]
def baseStart_510356 : Nat := 118140960795 + 510356 * 2 ^ 59
def prefixEnd_510356 : Nat := 4983230072969 + 3 ^ 40 * 510356 * 2
def baseEnd_510356 : Nat := 58235096201357880778427

theorem tailTrace_510356 : CollatzResearch.WordTrace tailWord_510356 prefixEnd_510356 58235096201357880778427 := by
  unfold tailWord_510356
  simp only [CollatzResearch.WordTrace]
  refine ⟨9307106269537424355299461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12409475026049899140399281 9307106269537424355299461)
  ·
    refine ⟨1745082425538267066618649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9307106269537424355299461 1745082425538267066618649)
    ·
      refine ⟨1308811819153700299963987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1745082425538267066618649 1308811819153700299963987)
      ·
        refine ⟨1963217728730550449945981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1308811819153700299963987 1963217728730550449945981)
        ·
          refine ⟨736206648273956418729743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1963217728730550449945981 736206648273956418729743)
          ·
            refine ⟨1104309972410934628094615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 736206648273956418729743 1104309972410934628094615)
            ·
              refine ⟨1656464958616401942141923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1104309972410934628094615 1656464958616401942141923)
              ·
                refine ⟨2484697437924602913212885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1656464958616401942141923 2484697437924602913212885)
                ·
                  refine ⟨58235096201357880778427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2484697437924602913212885 58235096201357880778427)
                  ·
                    rfl

theorem cell22_510356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 1, 1, 1, 7].length) (baseStart_510356 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_510356 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_510356 prefixEnd_510356 := by exact prefixLift 510356
  have htrace : WordTrace (prefixWord ++ tailWord_510356) baseStart_510356 baseEnd_510356 := by
    simpa [prefixWord, tailWord_510356, baseEnd_510356] using wordTrace_append hprefix tailTrace_510356
  have hstable : (prefixWord ++ tailWord_510356).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_510356).length < 2 ^ (prefixWord ++ tailWord_510356).sum := by decide
  have hdescent : baseEnd_510356 < baseStart_510356 := by decide
  rcases family_descends (prefixWord ++ tailWord_510356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_510386 : List Nat := [3, 2, 1, 1, 1, 1, 6, 2, 1, 4]
def baseStart_510386 : Nat := 118140960795 + 510386 * 2 ^ 59
def prefixEnd_510386 : Nat := 4983230072969 + 3 ^ 40 * 510386 * 2
def baseEnd_510386 : Nat := 174715558217163564085189

theorem tailTrace_510386 : CollatzResearch.WordTrace tailWord_510386 prefixEnd_510386 174715558217163564085189 := by
  unfold tailWord_510386
  simp only [CollatzResearch.WordTrace]
  refine ⟨4653826682241540958547753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12410204485977442556127341 4653826682241540958547753)
  ·
    refine ⟨3490370011681155718910815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4653826682241540958547753 3490370011681155718910815)
    ·
      refine ⟨5235555017521733578366223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3490370011681155718910815 5235555017521733578366223)
      ·
        refine ⟨7853332526282600367549335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5235555017521733578366223 7853332526282600367549335)
        ·
          refine ⟨11779998789423900551324003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7853332526282600367549335 11779998789423900551324003)
          ·
            refine ⟨17669998184135850826986005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11779998789423900551324003 17669998184135850826986005)
            ·
              refine ⟨828281164881368007514969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 17669998184135850826986005 828281164881368007514969)
              ·
                refine ⟨621210873661026005636227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 828281164881368007514969 621210873661026005636227)
                ·
                  refine ⟨931816310491539008454341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 621210873661026005636227 931816310491539008454341)
                  ·
                    refine ⟨174715558217163564085189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 931816310491539008454341 174715558217163564085189)
                    ·
                      rfl

theorem cell22_510386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 6, 2, 1, 4].length) (baseStart_510386 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_510386 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_510386 prefixEnd_510386 := by exact prefixLift 510386
  have htrace : WordTrace (prefixWord ++ tailWord_510386) baseStart_510386 baseEnd_510386 := by
    simpa [prefixWord, tailWord_510386, baseEnd_510386] using wordTrace_append hprefix tailTrace_510386
  have hstable : (prefixWord ++ tailWord_510386).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_510386).length < 2 ^ (prefixWord ++ tailWord_510386).sum := by decide
  have hdescent : baseEnd_510386 < baseStart_510386 := by decide
  rcases family_descends (prefixWord ++ tailWord_510386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_510489 : List Nat := [1, 2, 1, 2, 1, 1, 2, 5, 2, 5]
def baseStart_510489 : Nat := 118140960795 + 510489 * 2 ^ 59
def prefixEnd_510489 : Nat := 4983230072969 + 3 ^ 40 * 510489 * 2
def baseEnd_510489 : Nat := 174750817222105628759873

theorem tailTrace_510489 : CollatzResearch.WordTrace tailWord_510489 prefixEnd_510489 174750817222105628759873 := by
  unfold tailWord_510489
  simp only [CollatzResearch.WordTrace]
  refine ⟨18619063447593012425190521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12412708965062008283460347 18619063447593012425190521)
  ·
    refine ⟨13964297585694759318892891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18619063447593012425190521 13964297585694759318892891)
    ·
      refine ⟨20946446378542138978339337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13964297585694759318892891 20946446378542138978339337)
      ·
        refine ⟨15709834783906604233754503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20946446378542138978339337 15709834783906604233754503)
        ·
          refine ⟨23564752175859906350631755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15709834783906604233754503 23564752175859906350631755)
          ·
            refine ⟨35347128263789859525947633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23564752175859906350631755 35347128263789859525947633)
            ·
              refine ⟨26510346197842394644460725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35347128263789859525947633 26510346197842394644460725)
              ·
                refine ⟨2485344956047724497918193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 26510346197842394644460725 2485344956047724497918193)
                ·
                  refine ⟨1864008717035793373438645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2485344956047724497918193 1864008717035793373438645)
                  ·
                    refine ⟨174750817222105628759873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1864008717035793373438645 174750817222105628759873)
                    ·
                      rfl

theorem cell22_510489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 5, 2, 5].length) (baseStart_510489 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_510489 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_510489 prefixEnd_510489 := by exact prefixLift 510489
  have htrace : WordTrace (prefixWord ++ tailWord_510489) baseStart_510489 baseEnd_510489 := by
    simpa [prefixWord, tailWord_510489, baseEnd_510489] using wordTrace_append hprefix tailTrace_510489
  have hstable : (prefixWord ++ tailWord_510489).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_510489).length < 2 ^ (prefixWord ++ tailWord_510489).sum := by decide
  have hdescent : baseEnd_510489 < baseStart_510489 := by decide
  rcases family_descends (prefixWord ++ tailWord_510489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_510519 : List Nat := [1, 1, 3, 1, 2, 3, 1, 2, 8]
def baseStart_510519 : Nat := 118140960795 + 510519 * 2 ^ 59
def prefixEnd_510519 : Nat := 4983230072969 + 3 ^ 40 * 510519 * 2
def baseEnd_510519 : Nat := 58253695611731850169927

theorem tailTrace_510519 : CollatzResearch.WordTrace tailWord_510519 prefixEnd_510519 58253695611731850169927 := by
  unfold tailWord_510519
  simp only [CollatzResearch.WordTrace]
  refine ⟨18620157637484327548782611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12413438424989551699188407 18620157637484327548782611)
  ·
    refine ⟨27930236456226491323173917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18620157637484327548782611 27930236456226491323173917)
    ·
      refine ⟨10473838671084934246190219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27930236456226491323173917 10473838671084934246190219)
      ·
        refine ⟨15710758006627401369285329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10473838671084934246190219 15710758006627401369285329)
        ·
          refine ⟨11783068504970551026963997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15710758006627401369285329 11783068504970551026963997)
          ·
            refine ⟨4418650689363956635111499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11783068504970551026963997 4418650689363956635111499)
            ·
              refine ⟨6627976034045934952667249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4418650689363956635111499 6627976034045934952667249)
              ·
                refine ⟨4970982025534451214500437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6627976034045934952667249 4970982025534451214500437)
                ·
                  refine ⟨58253695611731850169927, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 4970982025534451214500437 58253695611731850169927)
                  ·
                    rfl

theorem cell22_510519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 1, 2, 8].length) (baseStart_510519 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_510519 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_510519 prefixEnd_510519 := by exact prefixLift 510519
  have htrace : WordTrace (prefixWord ++ tailWord_510519) baseStart_510519 baseEnd_510519 := by
    simpa [prefixWord, tailWord_510519, baseEnd_510519] using wordTrace_append hprefix tailTrace_510519
  have hstable : (prefixWord ++ tailWord_510519).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_510519).length < 2 ^ (prefixWord ++ tailWord_510519).sum := by decide
  have hdescent : baseEnd_510519 < baseStart_510519 := by decide
  rcases family_descends (prefixWord ++ tailWord_510519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_510643 : List Nat := [1, 1, 1, 2, 3, 5, 2, 2, 5]
def baseStart_510643 : Nat := 118140960795 + 510643 * 2 ^ 59
def prefixEnd_510643 : Nat := 4983230072969 + 3 ^ 40 * 510643 * 2
def baseEnd_510643 : Nat := 58267844856433520136467

theorem tailTrace_510643 : CollatzResearch.WordTrace tailWord_510643 prefixEnd_510643 58267844856433520136467 := by
  unfold tailWord_510643
  simp only [CollatzResearch.WordTrace]
  refine ⟨18624680289035096726296583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12416453526023397817531055 18624680289035096726296583)
  ·
    refine ⟨27937020433552645089444875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18624680289035096726296583 27937020433552645089444875)
    ·
      refine ⟨41905530650328967634167313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27937020433552645089444875 41905530650328967634167313)
      ·
        refine ⟨31429147987746725725625485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41905530650328967634167313 31429147987746725725625485)
        ·
          refine ⟨11785930495405022147109557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31429147987746725725625485 11785930495405022147109557)
          ·
            refine ⟨1104930983944220826291521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 11785930495405022147109557 1104930983944220826291521)
            ·
              refine ⟨828698237958165619718641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1104930983944220826291521 828698237958165619718641)
              ·
                refine ⟨621523678468624214788981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 828698237958165619718641 621523678468624214788981)
                ·
                  refine ⟨58267844856433520136467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 621523678468624214788981 58267844856433520136467)
                  ·
                    rfl

theorem cell22_510643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 5, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 5, 2, 2, 5].length) (baseStart_510643 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_510643 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_510643 prefixEnd_510643 := by exact prefixLift 510643
  have htrace : WordTrace (prefixWord ++ tailWord_510643) baseStart_510643 baseEnd_510643 := by
    simpa [prefixWord, tailWord_510643, baseEnd_510643] using wordTrace_append hprefix tailTrace_510643
  have hstable : (prefixWord ++ tailWord_510643).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_510643).length < 2 ^ (prefixWord ++ tailWord_510643).sum := by decide
  have hdescent : baseEnd_510643 < baseStart_510643 := by decide
  rcases family_descends (prefixWord ++ tailWord_510643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_510647 : List Nat := [1, 1, 3, 1, 6, 1, 1, 4, 1, 3]
def baseStart_510647 : Nat := 118140960795 + 510647 * 2 ^ 59
def prefixEnd_510647 : Nat := 4983230072969 + 3 ^ 40 * 510647 * 2
def baseEnd_510647 : Nat := 174804903851045883309389

theorem tailTrace_510647 : CollatzResearch.WordTrace tailWord_510647 prefixEnd_510647 174804903851045883309389 := by
  unfold tailWord_510647
  simp only [CollatzResearch.WordTrace]
  refine ⟨18624826181020605409442195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12416550787347070272961463 18624826181020605409442195)
  ·
    refine ⟨27937239271530908114163293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18624826181020605409442195 27937239271530908114163293)
    ·
      refine ⟨10476464726824090542811235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27937239271530908114163293 10476464726824090542811235)
      ·
        refine ⟨15714697090236135814216853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10476464726824090542811235 15714697090236135814216853)
        ·
          refine ⟨736626426104818866291415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 15714697090236135814216853 736626426104818866291415)
          ·
            refine ⟨1104939639157228299437123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 736626426104818866291415 1104939639157228299437123)
            ·
              refine ⟨1657409458735842449155685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1104939639157228299437123 1657409458735842449155685)
              ·
                refine ⟨310764273512970459216691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1657409458735842449155685 310764273512970459216691)
                ·
                  refine ⟨466146410269455688825037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 310764273512970459216691 466146410269455688825037)
                  ·
                    refine ⟨174804903851045883309389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 466146410269455688825037 174804903851045883309389)
                    ·
                      rfl

theorem cell22_510647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 1, 1, 4, 1, 3].length) (baseStart_510647 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_510647 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_510647 prefixEnd_510647 := by exact prefixLift 510647
  have htrace : WordTrace (prefixWord ++ tailWord_510647) baseStart_510647 baseEnd_510647 := by
    simpa [prefixWord, tailWord_510647, baseEnd_510647] using wordTrace_append hprefix tailTrace_510647
  have hstable : (prefixWord ++ tailWord_510647).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_510647).length < 2 ^ (prefixWord ++ tailWord_510647).sum := by decide
  have hdescent : baseEnd_510647 < baseStart_510647 := by decide
  rcases family_descends (prefixWord ++ tailWord_510647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_510673 : List Nat := [1, 2, 2, 1, 2, 3, 2, 4, 1, 4]
def baseStart_510673 : Nat := 118140960795 + 510673 * 2 ^ 59
def prefixEnd_510673 : Nat := 4983230072969 + 3 ^ 40 * 510673 * 2
def baseEnd_510673 : Nat := 174813804182390482159309

theorem tailTrace_510673 : CollatzResearch.WordTrace tailWord_510673 prefixEnd_510673 174813804182390482159309 := by
  unfold tailWord_510673
  simp only [CollatzResearch.WordTrace]
  refine ⟨18625774478926411849888673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12417182985950941233259115 18625774478926411849888673)
  ·
    refine ⟨13969330859194808887416505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18625774478926411849888673 13969330859194808887416505)
    ·
      refine ⟨10476998144396106665562379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13969330859194808887416505 10476998144396106665562379)
      ·
        refine ⟨15715497216594159998343569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10476998144396106665562379 15715497216594159998343569)
        ·
          refine ⟨11786622912445619998757677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15715497216594159998343569 11786622912445619998757677)
          ·
            refine ⟨4419983592167107499534129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11786622912445619998757677 4419983592167107499534129)
            ·
              refine ⟨3314987694125330624650597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4419983592167107499534129 3314987694125330624650597)
              ·
                refine ⟨621560192648499492121987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3314987694125330624650597 621560192648499492121987)
                ·
                  refine ⟨932340288972749238182981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 621560192648499492121987 932340288972749238182981)
                  ·
                    refine ⟨174813804182390482159309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 932340288972749238182981 174813804182390482159309)
                    ·
                      rfl

theorem cell22_510673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 2, 4, 1, 4].length) (baseStart_510673 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_510673 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_510673 prefixEnd_510673 := by exact prefixLift 510673
  have htrace : WordTrace (prefixWord ++ tailWord_510673) baseStart_510673 baseEnd_510673 := by
    simpa [prefixWord, tailWord_510673, baseEnd_510673] using wordTrace_append hprefix tailTrace_510673
  have hstable : (prefixWord ++ tailWord_510673).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_510673).length < 2 ^ (prefixWord ++ tailWord_510673).sum := by decide
  have hdescent : baseEnd_510673 < baseStart_510673 := by decide
  rcases family_descends (prefixWord ++ tailWord_510673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_510731 : List Nat := [1, 1, 1, 1, 5, 1, 1, 1, 1, 9]
def baseStart_510731 : Nat := 118140960795 + 510731 * 2 ^ 59
def prefixEnd_510731 : Nat := 4983230072969 + 3 ^ 40 * 510731 * 2
def baseEnd_510731 : Nat := 174833658767697664209131

theorem tailTrace_510731 : CollatzResearch.WordTrace tailWord_510731 prefixEnd_510731 174833658767697664209131 := by
  unfold tailWord_510731
  simp only [CollatzResearch.WordTrace]
  refine ⟨18627889912716287755500047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12418593275144191837000031 18627889912716287755500047)
  ·
    refine ⟨27941834869074431633250071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18627889912716287755500047 27941834869074431633250071)
    ·
      refine ⟨41912752303611647449875107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27941834869074431633250071 41912752303611647449875107)
      ·
        refine ⟨62869128455417471174812661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41912752303611647449875107 62869128455417471174812661)
        ·
          refine ⟨5893980792695387922638687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 62869128455417471174812661 5893980792695387922638687)
          ·
            refine ⟨8840971189043081883958031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5893980792695387922638687 8840971189043081883958031)
            ·
              refine ⟨13261456783564622825937047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8840971189043081883958031 13261456783564622825937047)
              ·
                refine ⟨19892185175346934238905571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13261456783564622825937047 19892185175346934238905571)
                ·
                  refine ⟨29838277763020401358358357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19892185175346934238905571 29838277763020401358358357)
                  ·
                    refine ⟨174833658767697664209131, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 29838277763020401358358357 174833658767697664209131)
                    ·
                      rfl

theorem cell22_510731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 1, 1, 9].length) (baseStart_510731 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_510731 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_510731 prefixEnd_510731 := by exact prefixLift 510731
  have htrace : WordTrace (prefixWord ++ tailWord_510731) baseStart_510731 baseEnd_510731 := by
    simpa [prefixWord, tailWord_510731, baseEnd_510731] using wordTrace_append hprefix tailTrace_510731
  have hstable : (prefixWord ++ tailWord_510731).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_510731).length < 2 ^ (prefixWord ++ tailWord_510731).sum := by decide
  have hdescent : baseEnd_510731 < baseStart_510731 := by decide
  rcases family_descends (prefixWord ++ tailWord_510731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_510812 : List Nat := [2, 2, 4, 2, 1, 2, 2, 2, 5]
def baseStart_510812 : Nat := 118140960795 + 510812 * 2 ^ 59
def prefixEnd_510812 : Nat := 4983230072969 + 3 ^ 40 * 510812 * 2
def baseEnd_510812 : Nat := 58287128907680150977961

theorem tailTrace_510812 : CollatzResearch.WordTrace tailWord_510812 prefixEnd_510812 58287128907680150977961 := by
  unfold tailWord_510812
  simp only [CollatzResearch.WordTrace]
  refine ⟨9315422112711419294599345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12420562816948559059465793 9315422112711419294599345)
  ·
    refine ⟨6986566584533564470949509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9315422112711419294599345 6986566584533564470949509)
    ·
      refine ⟨1309981234600043338303033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6986566584533564470949509 1309981234600043338303033)
      ·
        refine ⟨982485925950032503727275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1309981234600043338303033 982485925950032503727275)
        ·
          refine ⟨1473728888925048755590913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 982485925950032503727275 1473728888925048755590913)
          ·
            refine ⟨1105296666693786566693185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1473728888925048755590913 1105296666693786566693185)
            ·
              refine ⟨828972500020339925019889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1105296666693786566693185 828972500020339925019889)
              ·
                refine ⟨621729375015254943764917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 828972500020339925019889 621729375015254943764917)
                ·
                  refine ⟨58287128907680150977961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 621729375015254943764917 58287128907680150977961)
                  ·
                    rfl

theorem cell22_510812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 2, 2, 2, 5].length) (baseStart_510812 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_510812 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_510812 prefixEnd_510812 := by exact prefixLift 510812
  have htrace : WordTrace (prefixWord ++ tailWord_510812) baseStart_510812 baseEnd_510812 := by
    simpa [prefixWord, tailWord_510812, baseEnd_510812] using wordTrace_append hprefix tailTrace_510812
  have hstable : (prefixWord ++ tailWord_510812).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_510812).length < 2 ^ (prefixWord ++ tailWord_510812).sum := by decide
  have hdescent : baseEnd_510812 < baseStart_510812 := by decide
  rcases family_descends (prefixWord ++ tailWord_510812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_510855 : List Nat := [1, 1, 4, 2, 3, 1, 2, 2, 1, 5]
def baseStart_510855 : Nat := 118140960795 + 510855 * 2 ^ 59
def prefixEnd_510855 : Nat := 4983230072969 + 3 ^ 40 * 510855 * 2
def baseEnd_510855 : Nat := 174876106501802674108751

theorem tailTrace_510855 : CollatzResearch.WordTrace tailWord_510855 prefixEnd_510855 174876106501802674108751 := by
  unfold tailWord_510855
  simp only [CollatzResearch.WordTrace]
  refine ⟨18632412564267056933014019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12421608376178037955342679 18632412564267056933014019)
  ·
    refine ⟨27948618846400585399521029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18632412564267056933014019 27948618846400585399521029)
    ·
      refine ⟨5240366033700109762410193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27948618846400585399521029 5240366033700109762410193)
      ·
        refine ⟨3930274525275082321807645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5240366033700109762410193 3930274525275082321807645)
        ·
          refine ⟨1473852946978155870677867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3930274525275082321807645 1473852946978155870677867)
          ·
            refine ⟨2210779420467233806016801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1473852946978155870677867 2210779420467233806016801)
            ·
              refine ⟨1658084565350425354512601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2210779420467233806016801 1658084565350425354512601)
              ·
                refine ⟨1243563424012819015884451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1658084565350425354512601 1243563424012819015884451)
                ·
                  refine ⟨1865345136019228523826677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1243563424012819015884451 1865345136019228523826677)
                  ·
                    refine ⟨174876106501802674108751, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1865345136019228523826677 174876106501802674108751)
                    ·
                      rfl

theorem cell22_510855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 2, 2, 1, 5].length) (baseStart_510855 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_510855 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_510855 prefixEnd_510855 := by exact prefixLift 510855
  have htrace : WordTrace (prefixWord ++ tailWord_510855) baseStart_510855 baseEnd_510855 := by
    simpa [prefixWord, tailWord_510855, baseEnd_510855] using wordTrace_append hprefix tailTrace_510855
  have hstable : (prefixWord ++ tailWord_510855).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_510855).length < 2 ^ (prefixWord ++ tailWord_510855).sum := by decide
  have hdescent : baseEnd_510855 < baseStart_510855 := by decide
  rcases family_descends (prefixWord ++ tailWord_510855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_510857 : List Nat := [1, 2, 1, 1, 5, 3, 2, 3, 4]
def baseStart_510857 : Nat := 118140960795 + 510857 * 2 ^ 59
def prefixEnd_510857 : Nat := 4983230072969 + 3 ^ 40 * 510857 * 2
def baseEnd_510857 : Nat := 58292263714225111852915

theorem tailTrace_510857 : CollatzResearch.WordTrace tailWord_510857 prefixEnd_510857 58292263714225111852915 := by
  unfold tailWord_510857
  simp only [CollatzResearch.WordTrace]
  refine ⟨18632485510259811274586825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12421657006839874183057883 18632485510259811274586825)
  ·
    refine ⟨13974364132694858455940119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18632485510259811274586825 13974364132694858455940119)
    ·
      refine ⟨20961546199042287683910179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13974364132694858455940119 20961546199042287683910179)
      ·
        refine ⟨31442319298563431525865269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20961546199042287683910179 31442319298563431525865269)
        ·
          refine ⟨2947717434240321705549869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 31442319298563431525865269 2947717434240321705549869)
          ·
            refine ⟨1105394037840120639581201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2947717434240321705549869 1105394037840120639581201)
            ·
              refine ⟨829045528380090479685901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1105394037840120639581201 829045528380090479685901)
              ·
                refine ⟨310892073142533929882213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 829045528380090479685901 310892073142533929882213)
                ·
                  refine ⟨58292263714225111852915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 310892073142533929882213 58292263714225111852915)
                  ·
                    rfl

theorem cell22_510857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 3, 2, 3, 4].length) (baseStart_510857 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_510857 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_510857 prefixEnd_510857 := by exact prefixLift 510857
  have htrace : WordTrace (prefixWord ++ tailWord_510857) baseStart_510857 baseEnd_510857 := by
    simpa [prefixWord, tailWord_510857, baseEnd_510857] using wordTrace_append hprefix tailTrace_510857
  have hstable : (prefixWord ++ tailWord_510857).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_510857).length < 2 ^ (prefixWord ++ tailWord_510857).sum := by decide
  have hdescent : baseEnd_510857 < baseStart_510857 := by decide
  rcases family_descends (prefixWord ++ tailWord_510857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_510925 : List Nat := [1, 6, 3, 1, 1, 1, 3, 2, 4]
def baseStart_510925 : Nat := 118140960795 + 510925 * 2 ^ 59
def prefixEnd_510925 : Nat := 4983230072969 + 3 ^ 40 * 510925 * 2
def baseEnd_510925 : Nat := 58300022977448608286179

theorem tailTrace_510925 : CollatzResearch.WordTrace tailWord_510925 prefixEnd_510925 58300022977448608286179 := by
  unfold tailWord_510925
  simp only [CollatzResearch.WordTrace]
  refine ⟨18634965674013458888062229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12423310449342305925374819 18634965674013458888062229)
  ·
    refine ⟨873514015969380885377917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 18634965674013458888062229 873514015969380885377917)
    ·
      refine ⟨327567755988517832016719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 873514015969380885377917 327567755988517832016719)
      ·
        refine ⟨491351633982776748025079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 327567755988517832016719 491351633982776748025079)
        ·
          refine ⟨737027450974165122037619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 491351633982776748025079 737027450974165122037619)
          ·
            refine ⟨1105541176461247683056429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 737027450974165122037619 1105541176461247683056429)
            ·
              refine ⟨414577941172967881146161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1105541176461247683056429 414577941172967881146161)
              ·
                refine ⟨310933455879725910859621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 414577941172967881146161 310933455879725910859621)
                ·
                  refine ⟨58300022977448608286179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 310933455879725910859621 58300022977448608286179)
                  ·
                    rfl

theorem cell22_510925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 1, 3, 2, 4].length) (baseStart_510925 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_510925 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_510925 prefixEnd_510925 := by exact prefixLift 510925
  have htrace : WordTrace (prefixWord ++ tailWord_510925) baseStart_510925 baseEnd_510925 := by
    simpa [prefixWord, tailWord_510925, baseEnd_510925] using wordTrace_append hprefix tailTrace_510925
  have hstable : (prefixWord ++ tailWord_510925).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_510925).length < 2 ^ (prefixWord ++ tailWord_510925).sum := by decide
  have hdescent : baseEnd_510925 < baseStart_510925 := by decide
  rcases family_descends (prefixWord ++ tailWord_510925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_511007 : List Nat := [1, 1, 2, 4, 1, 4, 2, 1, 1, 5]
def baseStart_511007 : Nat := 118140960795 + 511007 * 2 ^ 59
def prefixEnd_511007 : Nat := 4983230072969 + 3 ^ 40 * 511007 * 2
def baseEnd_511007 : Nat := 174928139208124944308285

theorem tailTrace_511007 : CollatzResearch.WordTrace tailWord_511007 prefixEnd_511007 174928139208124944308285 := by
  unfold tailWord_511007
  simp only [CollatzResearch.WordTrace]
  refine ⟨18637956459716386892547275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12425304306477591261698183 18637956459716386892547275)
  ·
    refine ⟨27956934689574580338820913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18637956459716386892547275 27956934689574580338820913)
    ·
      refine ⟨20967701017180935254115685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27956934689574580338820913 20967701017180935254115685)
      ·
        refine ⟨3931443940721425360146691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20967701017180935254115685 3931443940721425360146691)
        ·
          refine ⟨5897165911082138040220037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3931443940721425360146691 5897165911082138040220037)
          ·
            refine ⟨1105718608327900882541257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5897165911082138040220037 1105718608327900882541257)
            ·
              refine ⟨829288956245925661905943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1105718608327900882541257 829288956245925661905943)
              ·
                refine ⟨1243933434368888492858915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 829288956245925661905943 1243933434368888492858915)
                ·
                  refine ⟨1865900151553332739288373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1243933434368888492858915 1865900151553332739288373)
                  ·
                    refine ⟨174928139208124944308285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1865900151553332739288373 174928139208124944308285)
                    ·
                      rfl

theorem cell22_511007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 4, 2, 1, 1, 5].length) (baseStart_511007 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_511007 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_511007 prefixEnd_511007 := by exact prefixLift 511007
  have htrace : WordTrace (prefixWord ++ tailWord_511007) baseStart_511007 baseEnd_511007 := by
    simpa [prefixWord, tailWord_511007, baseEnd_511007] using wordTrace_append hprefix tailTrace_511007
  have hstable : (prefixWord ++ tailWord_511007).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_511007).length < 2 ^ (prefixWord ++ tailWord_511007).sum := by decide
  have hdescent : baseEnd_511007 < baseStart_511007 := by decide
  rcases family_descends (prefixWord ++ tailWord_511007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_511022 : List Nat := [4, 1, 3, 1, 1, 1, 3, 1, 1, 6]
def baseStart_511022 : Nat := 118140960795 + 511022 * 2 ^ 59
def prefixEnd_511022 : Nat := 4983230072969 + 3 ^ 40 * 511022 * 2
def baseEnd_511022 : Nat := 174933274014669905183239

theorem tailTrace_511022 : CollatzResearch.WordTrace tailWord_511022 prefixEnd_511022 174933274014669905183239 := by
  unfold tailWord_511022
  simp only [CollatzResearch.WordTrace]
  refine ⟨2329812944332755556792915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12425669036441362969562213 2329812944332755556792915)
  ·
    refine ⟨3494719416499133335189373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2329812944332755556792915 3494719416499133335189373)
    ·
      refine ⟨1310519781187175000696015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3494719416499133335189373 1310519781187175000696015)
      ·
        refine ⟨1965779671780762501044023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1310519781187175000696015 1965779671780762501044023)
        ·
          refine ⟨2948669507671143751566035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1965779671780762501044023 2948669507671143751566035)
          ·
            refine ⟨4423004261506715627349053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2948669507671143751566035 4423004261506715627349053)
            ·
              refine ⟨1658626598065018360255895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4423004261506715627349053 1658626598065018360255895)
              ·
                refine ⟨2487939897097527540383843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1658626598065018360255895 2487939897097527540383843)
                ·
                  refine ⟨3731909845646291310575765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2487939897097527540383843 3731909845646291310575765)
                  ·
                    refine ⟨174933274014669905183239, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3731909845646291310575765 174933274014669905183239)
                    ·
                      rfl

theorem cell22_511022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 3, 1, 1, 6].length) (baseStart_511022 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_511022 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_511022 prefixEnd_511022 := by exact prefixLift 511022
  have htrace : WordTrace (prefixWord ++ tailWord_511022) baseStart_511022 baseEnd_511022 := by
    simpa [prefixWord, tailWord_511022, baseEnd_511022] using wordTrace_append hprefix tailTrace_511022
  have hstable : (prefixWord ++ tailWord_511022).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_511022).length < 2 ^ (prefixWord ++ tailWord_511022).sum := by decide
  have hdescent : baseEnd_511022 < baseStart_511022 := by decide
  rcases family_descends (prefixWord ++ tailWord_511022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_511028 : List Nat := [2, 5, 1, 2, 1, 3, 2, 1, 1, 4]
def baseStart_511028 : Nat := 118140960795 + 511028 * 2 ^ 59
def prefixEnd_511028 : Nat := 4983230072969 + 3 ^ 40 * 511028 * 2
def baseEnd_511028 : Nat := 174935327937287889533221

theorem tailTrace_511028 : CollatzResearch.WordTrace tailWord_511028 prefixEnd_511028 174935327937287889533221 := by
  unfold tailWord_511028
  simp only [CollatzResearch.WordTrace]
  refine ⟨9319361196320153739530869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12425814928426871652707825 9319361196320153739530869)
  ·
    refine ⟨873690112155014413081019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 9319361196320153739530869 873690112155014413081019)
    ·
      refine ⟨1310535168232521619621529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 873690112155014413081019 1310535168232521619621529)
      ·
        refine ⟨982901376174391214716147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1310535168232521619621529 982901376174391214716147)
        ·
          refine ⟨1474352064261586822074221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 982901376174391214716147 1474352064261586822074221)
          ·
            refine ⟨552882024098095058277833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1474352064261586822074221 552882024098095058277833)
            ·
              refine ⟨414661518073571293708375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 552882024098095058277833 414661518073571293708375)
              ·
                refine ⟨621992277110356940562563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 414661518073571293708375 621992277110356940562563)
                ·
                  refine ⟨932988415665535410843845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 621992277110356940562563 932988415665535410843845)
                  ·
                    refine ⟨174935327937287889533221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 932988415665535410843845 174935327937287889533221)
                    ·
                      rfl

theorem cell22_511028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 3, 2, 1, 1, 4].length) (baseStart_511028 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_511028 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_511028 prefixEnd_511028 := by exact prefixLift 511028
  have htrace : WordTrace (prefixWord ++ tailWord_511028) baseStart_511028 baseEnd_511028 := by
    simpa [prefixWord, tailWord_511028, baseEnd_511028] using wordTrace_append hprefix tailTrace_511028
  have hstable : (prefixWord ++ tailWord_511028).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_511028).length < 2 ^ (prefixWord ++ tailWord_511028).sum := by decide
  have hdescent : baseEnd_511028 < baseStart_511028 := by decide
  rcases family_descends (prefixWord ++ tailWord_511028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_511050 : List Nat := [3, 1, 2, 1, 1, 2, 2, 1, 1, 8]
def baseStart_511050 : Nat := 118140960795 + 511050 * 2 ^ 59
def prefixEnd_511050 : Nat := 4983230072969 + 3 ^ 40 * 511050 * 2
def baseEnd_511050 : Nat := 174942858986887165483153

theorem tailTrace_511050 : CollatzResearch.WordTrace tailWord_511050 prefixEnd_511050 174942858986887165483153 := by
  unfold tailWord_511050
  simp only [CollatzResearch.WordTrace]
  refine ⟨4659881199640151309090651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12426349865707070157575069 4659881199640151309090651)
  ·
    refine ⟨6989821799460226963635977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4659881199640151309090651 6989821799460226963635977)
    ·
      refine ⟨5242366349595170222726983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6989821799460226963635977 5242366349595170222726983)
      ·
        refine ⟨7863549524392755334090475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5242366349595170222726983 7863549524392755334090475)
        ·
          refine ⟨11795324286589133001135713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7863549524392755334090475 11795324286589133001135713)
          ·
            refine ⟨8846493214941849750851785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11795324286589133001135713 8846493214941849750851785)
            ·
              refine ⟨6634869911206387313138839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8846493214941849750851785 6634869911206387313138839)
              ·
                refine ⟨9952304866809580969708259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6634869911206387313138839 9952304866809580969708259)
                ·
                  refine ⟨14928457300214371454562389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9952304866809580969708259 14928457300214371454562389)
                  ·
                    refine ⟨174942858986887165483153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 14928457300214371454562389 174942858986887165483153)
                    ·
                      rfl

theorem cell22_511050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 2, 1, 1, 8].length) (baseStart_511050 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_511050 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_511050 prefixEnd_511050 := by exact prefixLift 511050
  have htrace : WordTrace (prefixWord ++ tailWord_511050) baseStart_511050 baseEnd_511050 := by
    simpa [prefixWord, tailWord_511050, baseEnd_511050] using wordTrace_append hprefix tailTrace_511050
  have hstable : (prefixWord ++ tailWord_511050).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_511050).length < 2 ^ (prefixWord ++ tailWord_511050).sum := by decide
  have hdescent : baseEnd_511050 < baseStart_511050 := by decide
  rcases family_descends (prefixWord ++ tailWord_511050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_511082 : List Nat := [3, 1, 3, 2, 2, 1, 1, 2, 7]
def baseStart_511082 : Nat := 118140960795 + 511082 * 2 ^ 59
def prefixEnd_511082 : Nat := 4983230072969 + 3 ^ 40 * 511082 * 2
def baseEnd_511082 : Nat := 58317937746949916227685

theorem tailTrace_511082 : CollatzResearch.WordTrace tailWord_511082 prefixEnd_511082 58317937746949916227685 := by
  unfold tailWord_511082
  simp only [CollatzResearch.WordTrace]
  refine ⟨4660172983611168675381875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12427127956296449801018333 4660172983611168675381875)
  ·
    refine ⟨6990259475416753013072813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4660172983611168675381875 6990259475416753013072813)
    ·
      refine ⟨2621347303281282379902305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6990259475416753013072813 2621347303281282379902305)
      ·
        refine ⟨1966010477460961784926729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2621347303281282379902305 1966010477460961784926729)
        ·
          refine ⟨1474507858095721338695047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1966010477460961784926729 1474507858095721338695047)
          ·
            refine ⟨2211761787143582008042571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1474507858095721338695047 2211761787143582008042571)
            ·
              refine ⟨3317642680715373012063857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2211761787143582008042571 3317642680715373012063857)
              ·
                refine ⟨2488232010536529759047893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3317642680715373012063857 2488232010536529759047893)
                ·
                  refine ⟨58317937746949916227685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2488232010536529759047893 58317937746949916227685)
                  ·
                    rfl

theorem cell22_511082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 1, 2, 7].length) (baseStart_511082 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_511082 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_511082 prefixEnd_511082 := by exact prefixLift 511082
  have htrace : WordTrace (prefixWord ++ tailWord_511082) baseStart_511082 baseEnd_511082 := by
    simpa [prefixWord, tailWord_511082, baseEnd_511082] using wordTrace_append hprefix tailTrace_511082
  have hstable : (prefixWord ++ tailWord_511082).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_511082).length < 2 ^ (prefixWord ++ tailWord_511082).sum := by decide
  have hdescent : baseEnd_511082 < baseStart_511082 := by decide
  rcases family_descends (prefixWord ++ tailWord_511082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_511161 : List Nat := [1, 2, 1, 4, 1, 3, 4, 2, 4]
def baseStart_511161 : Nat := 118140960795 + 511161 * 2 ^ 59
def prefixEnd_511161 : Nat := 4983230072969 + 3 ^ 40 * 511161 * 2
def baseEnd_511161 : Nat := 58326952185106625319271

theorem tailTrace_511161 : CollatzResearch.WordTrace tailWord_511161 prefixEnd_511161 58326952185106625319271 := by
  unfold tailWord_511161
  simp only [CollatzResearch.WordTrace]
  refine ⟨18643573301158471193653337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12429048867438980795768891 18643573301158471193653337)
  ·
    refine ⟨13982679975868853395240003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18643573301158471193653337 13982679975868853395240003)
    ·
      refine ⟨20974019963803280092860005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13982679975868853395240003 20974019963803280092860005)
      ·
        refine ⟨3932628743213115017411251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20974019963803280092860005 3932628743213115017411251)
        ·
          refine ⟨5898943114819672526116877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3932628743213115017411251 5898943114819672526116877)
          ·
            refine ⟨2212103668057377197293829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5898943114819672526116877 2212103668057377197293829)
            ·
              refine ⟨414769437760758224492593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2212103668057377197293829 414769437760758224492593)
              ·
                refine ⟨311077078320568668369445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 414769437760758224492593 311077078320568668369445)
                ·
                  refine ⟨58326952185106625319271, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 311077078320568668369445 58326952185106625319271)
                  ·
                    rfl

theorem cell22_511161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 4, 2, 4].length) (baseStart_511161 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_511161 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_511161 prefixEnd_511161 := by exact prefixLift 511161
  have htrace : WordTrace (prefixWord ++ tailWord_511161) baseStart_511161 baseEnd_511161 := by
    simpa [prefixWord, tailWord_511161, baseEnd_511161] using wordTrace_append hprefix tailTrace_511161
  have hstable : (prefixWord ++ tailWord_511161).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_511161).length < 2 ^ (prefixWord ++ tailWord_511161).sum := by decide
  have hdescent : baseEnd_511161 < baseStart_511161 := by decide
  rcases family_descends (prefixWord ++ tailWord_511161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_511328 : List Nat := [2, 1, 1, 3, 4, 2, 2, 2, 2, 3]
def baseStart_511328 : Nat := 118140960795 + 511328 * 2 ^ 59
def prefixEnd_511328 : Nat := 4983230072969 + 3 ^ 40 * 511328 * 2
def baseEnd_511328 : Nat := 175038024068187107032301

theorem tailTrace_511328 : CollatzResearch.WordTrace tailWord_511328 prefixEnd_511328 175038024068187107032301 := by
  unfold tailWord_511328
  simp only [CollatzResearch.WordTrace]
  refine ⟨9324832145776729357491319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12433109527702305809988425 9324832145776729357491319)
  ·
    refine ⟨13987248218665094036236979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9324832145776729357491319 13987248218665094036236979)
    ·
      refine ⟨20980872327997641054355469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13987248218665094036236979 20980872327997641054355469)
      ·
        refine ⟨7867827122999115395383301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20980872327997641054355469 7867827122999115395383301)
        ·
          refine ⟨1475217585562334136634369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7867827122999115395383301 1475217585562334136634369)
          ·
            refine ⟨1106413189171750602475777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1475217585562334136634369 1106413189171750602475777)
            ·
              refine ⟨829809891878812951856833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1106413189171750602475777 829809891878812951856833)
              ·
                refine ⟨622357418909109713892625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 829809891878812951856833 622357418909109713892625)
                ·
                  refine ⟨466768064181832285419469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 622357418909109713892625 466768064181832285419469)
                  ·
                    refine ⟨175038024068187107032301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 466768064181832285419469 175038024068187107032301)
                    ·
                      rfl

theorem cell22_511328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 2, 2, 2, 2, 3].length) (baseStart_511328 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_511328 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_511328 prefixEnd_511328 := by exact prefixLift 511328
  have htrace : WordTrace (prefixWord ++ tailWord_511328) baseStart_511328 baseEnd_511328 := by
    simpa [prefixWord, tailWord_511328, baseEnd_511328] using wordTrace_append hprefix tailTrace_511328
  have hstable : (prefixWord ++ tailWord_511328).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_511328).length < 2 ^ (prefixWord ++ tailWord_511328).sum := by decide
  have hdescent : baseEnd_511328 < baseStart_511328 := by decide
  rcases family_descends (prefixWord ++ tailWord_511328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_511341 : List Nat := [1, 5, 1, 1, 1, 5, 1, 7]
def baseStart_511341 : Nat := 118140960795 + 511341 * 2 ^ 59
def prefixEnd_511341 : Nat := 4983230072969 + 3 ^ 40 * 511341 * 2
def baseEnd_511341 : Nat := 19449163803762156273029

theorem tailTrace_511341 : CollatzResearch.WordTrace tailWord_511341 prefixEnd_511341 19449163803762156273029 := by
  unfold tailWord_511341
  simp only [CollatzResearch.WordTrace]
  refine ⟨18650138440506361935205877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12433425627004241290137251 18650138440506361935205877)
  ·
    refine ⟨1748450478797471431425551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 18650138440506361935205877 1748450478797471431425551)
    ·
      refine ⟨2622675718196207147138327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1748450478797471431425551 2622675718196207147138327)
      ·
        refine ⟨3934013577294310720707491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2622675718196207147138327 3934013577294310720707491)
        ·
          refine ⟨5901020365941466081061237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3934013577294310720707491 5901020365941466081061237)
          ·
            refine ⟨553220659307012445099491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 5901020365941466081061237 553220659307012445099491)
            ·
              refine ⟨829830988960518667649237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 553220659307012445099491 829830988960518667649237)
              ·
                refine ⟨19449163803762156273029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 829830988960518667649237 19449163803762156273029)
                ·
                  rfl

theorem cell22_511341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 5, 1, 7].length) (baseStart_511341 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_511341 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_511341 prefixEnd_511341 := by exact prefixLift 511341
  have htrace : WordTrace (prefixWord ++ tailWord_511341) baseStart_511341 baseEnd_511341 := by
    simpa [prefixWord, tailWord_511341, baseEnd_511341] using wordTrace_append hprefix tailTrace_511341
  have hstable : (prefixWord ++ tailWord_511341).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_511341).length < 2 ^ (prefixWord ++ tailWord_511341).sum := by decide
  have hdescent : baseEnd_511341 < baseStart_511341 := by decide
  rcases family_descends (prefixWord ++ tailWord_511341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_511356 : List Nat := [2, 2, 2, 1, 1, 1, 5, 2, 3, 3]
def baseStart_511356 : Nat := 118140960795 + 511356 * 2 ^ 59
def prefixEnd_511356 : Nat := 4983230072969 + 3 ^ 40 * 511356 * 2
def baseEnd_511356 : Nat := 175047609040404367332215

theorem tailTrace_511356 : CollatzResearch.WordTrace tailWord_511356 prefixEnd_511356 175047609040404367332215 := by
  unfold tailWord_511356
  simp only [CollatzResearch.WordTrace]
  refine ⟨9325342767726009748500961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12433790356968012998001281 9325342767726009748500961)
  ·
    refine ⟨6994007075794507311375721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9325342767726009748500961 6994007075794507311375721)
    ·
      refine ⟨5245505306845880483531791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6994007075794507311375721 5245505306845880483531791)
      ·
        refine ⟨7868257960268820725297687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5245505306845880483531791 7868257960268820725297687)
        ·
          refine ⟨11802386940403231087946531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7868257960268820725297687 11802386940403231087946531)
          ·
            refine ⟨17703580410604846631919797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11802386940403231087946531 17703580410604846631919797)
            ·
              refine ⟨1659710663494204371742481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 17703580410604846631919797 1659710663494204371742481)
              ·
                refine ⟨1244782997620653278806861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1659710663494204371742481 1244782997620653278806861)
                ·
                  refine ⟨466793624107744979552573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1244782997620653278806861 466793624107744979552573)
                  ·
                    refine ⟨175047609040404367332215, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 466793624107744979552573 175047609040404367332215)
                    ·
                      rfl

theorem cell22_511356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 5, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 5, 2, 3, 3].length) (baseStart_511356 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_511356 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_511356 prefixEnd_511356 := by exact prefixLift 511356
  have htrace : WordTrace (prefixWord ++ tailWord_511356) baseStart_511356 baseEnd_511356 := by
    simpa [prefixWord, tailWord_511356, baseEnd_511356] using wordTrace_append hprefix tailTrace_511356
  have hstable : (prefixWord ++ tailWord_511356).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_511356).length < 2 ^ (prefixWord ++ tailWord_511356).sum := by decide
  have hdescent : baseEnd_511356 < baseStart_511356 := by decide
  rcases family_descends (prefixWord ++ tailWord_511356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_511416 : List Nat := [2, 1, 2, 1, 2, 2, 3, 4, 1, 4]
def baseStart_511416 : Nat := 118140960795 + 511416 * 2 ^ 59
def prefixEnd_511416 : Nat := 4983230072969 + 3 ^ 40 * 511416 * 2
def baseEnd_511416 : Nat := 175068148266584210832031

theorem tailTrace_511416 : CollatzResearch.WordTrace tailWord_511416 prefixEnd_511416 175068148266584210832031 := by
  unfold tailWord_511416
  simp only [CollatzResearch.WordTrace]
  refine ⟨9326436957617324872093051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12435249276823099829457401 9326436957617324872093051)
  ·
    refine ⟨13989655436425987308139577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9326436957617324872093051 13989655436425987308139577)
    ·
      refine ⟨10492241577319490481104683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13989655436425987308139577 10492241577319490481104683)
      ·
        refine ⟨15738362365979235721657025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10492241577319490481104683 15738362365979235721657025)
        ·
          refine ⟨11803771774484426791242769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15738362365979235721657025 11803771774484426791242769)
          ·
            refine ⟨8852828830863320093432077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11803771774484426791242769 8852828830863320093432077)
            ·
              refine ⟨3319810811573745035037029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8852828830863320093432077 3319810811573745035037029)
              ·
                refine ⟨622464527170077194069443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3319810811573745035037029 622464527170077194069443)
                ·
                  refine ⟨933696790755115791104165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 622464527170077194069443 933696790755115791104165)
                  ·
                    refine ⟨175068148266584210832031, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 933696790755115791104165 175068148266584210832031)
                    ·
                      rfl

theorem cell22_511416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 3, 4, 1, 4].length) (baseStart_511416 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_511416 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_511416 prefixEnd_511416 := by exact prefixLift 511416
  have htrace : WordTrace (prefixWord ++ tailWord_511416) baseStart_511416 baseEnd_511416 := by
    simpa [prefixWord, tailWord_511416, baseEnd_511416] using wordTrace_append hprefix tailTrace_511416
  have hstable : (prefixWord ++ tailWord_511416).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_511416).length < 2 ^ (prefixWord ++ tailWord_511416).sum := by decide
  have hdescent : baseEnd_511416 < baseStart_511416 := by decide
  rcases family_descends (prefixWord ++ tailWord_511416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_511478 : List Nat := [5, 1, 1, 1, 2, 2, 1, 3, 2, 4]
def baseStart_511478 : Nat := 118140960795 + 511478 * 2 ^ 59
def prefixEnd_511478 : Nat := 4983230072969 + 3 ^ 40 * 511478 * 2
def baseEnd_511478 : Nat := 175089372133636715781841

theorem tailTrace_511478 : CollatzResearch.WordTrace tailWord_511478 prefixEnd_511478 175089372133636715781841 := by
  unfold tailWord_511478
  simp only [CollatzResearch.WordTrace]
  refine ⟨1165945952563127145808943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 12436756827340022888628725 1165945952563127145808943)
  ·
    refine ⟨1748918928844690718713415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1165945952563127145808943 1748918928844690718713415)
    ·
      refine ⟨2623378393267036078070123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1748918928844690718713415 2623378393267036078070123)
      ·
        refine ⟨3935067589900554117105185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2623378393267036078070123 3935067589900554117105185)
        ·
          refine ⟨2951300692425415587828889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3935067589900554117105185 2951300692425415587828889)
          ·
            refine ⟨2213475519319061690871667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2951300692425415587828889 2213475519319061690871667)
            ·
              refine ⟨3320213278978592536307501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2213475519319061690871667 3320213278978592536307501)
              ·
                refine ⟨1245079979616972201115313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3320213278978592536307501 1245079979616972201115313)
                ·
                  refine ⟨933809984712729150836485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1245079979616972201115313 933809984712729150836485)
                  ·
                    refine ⟨175089372133636715781841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 933809984712729150836485 175089372133636715781841)
                    ·
                      rfl

theorem cell22_511478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 1, 3, 2, 4].length) (baseStart_511478 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_511478 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_511478 prefixEnd_511478 := by exact prefixLift 511478
  have htrace : WordTrace (prefixWord ++ tailWord_511478) baseStart_511478 baseEnd_511478 := by
    simpa [prefixWord, tailWord_511478, baseEnd_511478] using wordTrace_append hprefix tailTrace_511478
  have hstable : (prefixWord ++ tailWord_511478).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_511478).length < 2 ^ (prefixWord ++ tailWord_511478).sum := by decide
  have hdescent : baseEnd_511478 < baseStart_511478 := by decide
  rcases family_descends (prefixWord ++ tailWord_511478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_511491 : List Nat := [1, 1, 1, 3, 2, 1, 2, 1, 7, 3]
def baseStart_511491 : Nat := 118140960795 + 511491 * 2 ^ 59
def prefixEnd_511491 : Nat := 4983230072969 + 3 ^ 40 * 511491 * 2
def baseEnd_511491 : Nat := 175093822299309015206801

theorem tailTrace_511491 : CollatzResearch.WordTrace tailWord_511491 prefixEnd_511491 175093822299309015206801 := by
  unfold tailWord_511491
  simp only [CollatzResearch.WordTrace]
  refine ⟨18655609389962937553166327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12437072926641958368777551 18655609389962937553166327)
  ·
    refine ⟨27983414084944406329749491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18655609389962937553166327 27983414084944406329749491)
    ·
      refine ⟨41975121127416609494624237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27983414084944406329749491 41975121127416609494624237)
      ·
        refine ⟨15740670422781228560484089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41975121127416609494624237 15740670422781228560484089)
        ·
          refine ⟨11805502817085921420363067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15740670422781228560484089 11805502817085921420363067)
          ·
            refine ⟨17708254225628882130544601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11805502817085921420363067 17708254225628882130544601)
            ·
              refine ⟨13281190669221661597908451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17708254225628882130544601 13281190669221661597908451)
              ·
                refine ⟨19921786003832492396862677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13281190669221661597908451 19921786003832492396862677)
                ·
                  refine ⟨466916859464824040551469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19921786003832492396862677 466916859464824040551469)
                  ·
                    refine ⟨175093822299309015206801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 466916859464824040551469 175093822299309015206801)
                    ·
                      rfl

theorem cell22_511491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 1, 7, 3].length) (baseStart_511491 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_511491 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_511491 prefixEnd_511491 := by exact prefixLift 511491
  have htrace : WordTrace (prefixWord ++ tailWord_511491) baseStart_511491 baseEnd_511491 := by
    simpa [prefixWord, tailWord_511491, baseEnd_511491] using wordTrace_append hprefix tailTrace_511491
  have hstable : (prefixWord ++ tailWord_511491).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_511491).length < 2 ^ (prefixWord ++ tailWord_511491).sum := by decide
  have hdescent : baseEnd_511491 < baseStart_511491 := by decide
  rcases family_descends (prefixWord ++ tailWord_511491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_511600 : List Nat := [2, 1, 1, 1, 6, 1, 3, 3, 4]
def baseStart_511600 : Nat := 118140960795 + 511600 * 2 ^ 59
def prefixEnd_511600 : Nat := 4983230072969 + 3 ^ 40 * 511600 * 2
def baseEnd_511600 : Nat := 58377045075623021410489

theorem tailTrace_511600 : CollatzResearch.WordTrace tailWord_511600 prefixEnd_511600 58377045075623021410489 := by
  unfold tailWord_511600
  simp only [CollatzResearch.WordTrace]
  refine ⟨9329792473284024584442127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12439723297712032779256169 9329792473284024584442127)
  ·
    refine ⟨13994688709926036876663191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9329792473284024584442127 13994688709926036876663191)
    ·
      refine ⟨20992033064889055314994787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13994688709926036876663191 20992033064889055314994787)
      ·
        refine ⟨31488049597333582972492181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20992033064889055314994787 31488049597333582972492181)
        ·
          refine ⟨1476002324875011701835571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 31488049597333582972492181 1476002324875011701835571)
          ·
            refine ⟨2214003487312517552753357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1476002324875011701835571 2214003487312517552753357)
            ·
              refine ⟨830251307742194082282509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2214003487312517552753357 830251307742194082282509)
              ·
                refine ⟨311344240403322780855941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 830251307742194082282509 311344240403322780855941)
                ·
                  refine ⟨58377045075623021410489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 311344240403322780855941 58377045075623021410489)
                  ·
                    rfl

theorem cell22_511600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 3, 3, 4].length) (baseStart_511600 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_511600 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_511600 prefixEnd_511600 := by exact prefixLift 511600
  have htrace : WordTrace (prefixWord ++ tailWord_511600) baseStart_511600 baseEnd_511600 := by
    simpa [prefixWord, tailWord_511600, baseEnd_511600] using wordTrace_append hprefix tailTrace_511600
  have hstable : (prefixWord ++ tailWord_511600).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_511600).length < 2 ^ (prefixWord ++ tailWord_511600).sum := by decide
  have hdescent : baseEnd_511600 < baseStart_511600 := by decide
  rcases family_descends (prefixWord ++ tailWord_511600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_511613 : List Nat := [1, 4, 1, 1, 4, 1, 1, 1, 4, 4]
def baseStart_511613 : Nat := 118140960795 + 511613 * 2 ^ 59
def prefixEnd_511613 : Nat := 4983230072969 + 3 ^ 40 * 511613 * 2
def baseEnd_511613 : Nat := 175135585392541363656427

theorem tailTrace_511613 : CollatzResearch.WordTrace tailWord_511613 prefixEnd_511613 175135585392541363656427 := by
  unfold tailWord_511613
  simp only [CollatzResearch.WordTrace]
  refine ⟨18660059095520952389107493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12440039397013968259404995 18660059095520952389107493)
  ·
    refine ⟨3498761080410178572957655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18660059095520952389107493 3498761080410178572957655)
    ·
      refine ⟨5248141620615267859436483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3498761080410178572957655 5248141620615267859436483)
      ·
        refine ⟨7872212430922901789154725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5248141620615267859436483 7872212430922901789154725)
        ·
          refine ⟨1476039830798044085466511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7872212430922901789154725 1476039830798044085466511)
          ·
            refine ⟨2214059746197066128199767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1476039830798044085466511 2214059746197066128199767)
            ·
              refine ⟨3321089619295599192299651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2214059746197066128199767 3321089619295599192299651)
              ·
                refine ⟨4981634428943398788449477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3321089619295599192299651 4981634428943398788449477)
                ·
                  refine ⟨934056455426887272834277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4981634428943398788449477 934056455426887272834277)
                  ·
                    refine ⟨175135585392541363656427, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 934056455426887272834277 175135585392541363656427)
                    ·
                      rfl

theorem cell22_511613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 1, 1, 4, 4].length) (baseStart_511613 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_511613 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_511613 prefixEnd_511613 := by exact prefixLift 511613
  have htrace : WordTrace (prefixWord ++ tailWord_511613) baseStart_511613 baseEnd_511613 := by
    simpa [prefixWord, tailWord_511613, baseEnd_511613] using wordTrace_append hprefix tailTrace_511613
  have hstable : (prefixWord ++ tailWord_511613).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_511613).length < 2 ^ (prefixWord ++ tailWord_511613).sum := by decide
  have hdescent : baseEnd_511613 < baseStart_511613 := by decide
  rcases family_descends (prefixWord ++ tailWord_511613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_511617 : List Nat := [1, 2, 4, 2, 1, 3, 3, 2, 4]
def baseStart_511617 : Nat := 118140960795 + 511617 * 2 ^ 59
def prefixEnd_511617 : Nat := 4983230072969 + 3 ^ 40 * 511617 * 2
def baseEnd_511617 : Nat := 58378984891428895518805

theorem tailTrace_511617 : CollatzResearch.WordTrace tailWord_511617 prefixEnd_511617 58378984891428895518805 := by
  unfold tailWord_511617
  simp only [CollatzResearch.WordTrace]
  refine ⟨18660204987506461072253105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12440136658337640714835403 18660204987506461072253105)
  ·
    refine ⟨13995153740629845804189829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18660204987506461072253105 13995153740629845804189829)
    ·
      refine ⟨2624091326368096088285593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13995153740629845804189829 2624091326368096088285593)
      ·
        refine ⟨1968068494776072066214195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2624091326368096088285593 1968068494776072066214195)
        ·
          refine ⟨2952102742164108099321293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1968068494776072066214195 2952102742164108099321293)
          ·
            refine ⟨1107038528311540537245485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2952102742164108099321293 1107038528311540537245485)
            ·
              refine ⟨415139448116827701467057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1107038528311540537245485 415139448116827701467057)
              ·
                refine ⟨311354586087620776100293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 415139448116827701467057 311354586087620776100293)
                ·
                  refine ⟨58378984891428895518805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 311354586087620776100293 58378984891428895518805)
                  ·
                    rfl

theorem cell22_511617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 3, 3, 2, 4].length) (baseStart_511617 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_511617 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_511617 prefixEnd_511617 := by exact prefixLift 511617
  have htrace : WordTrace (prefixWord ++ tailWord_511617) baseStart_511617 baseEnd_511617 := by
    simpa [prefixWord, tailWord_511617, baseEnd_511617] using wordTrace_append hprefix tailTrace_511617
  have hstable : (prefixWord ++ tailWord_511617).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_511617).length < 2 ^ (prefixWord ++ tailWord_511617).sum := by decide
  have hdescent : baseEnd_511617 < baseStart_511617 := by decide
  rcases family_descends (prefixWord ++ tailWord_511617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_511641 : List Nat := [1, 2, 1, 2, 1, 2, 2, 1, 4, 6]
def baseStart_511641 : Nat := 118140960795 + 511641 * 2 ^ 59
def prefixEnd_511641 : Nat := 4983230072969 + 3 ^ 40 * 511641 * 2
def baseEnd_511641 : Nat := 175145170364758623956341

theorem tailTrace_511641 : CollatzResearch.WordTrace tailWord_511641 prefixEnd_511641 175145170364758623956341 := by
  unfold tailWord_511641
  simp only [CollatzResearch.WordTrace]
  refine ⟨18661080339419513171126777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12440720226279675447417851 18661080339419513171126777)
  ·
    refine ⟨13995810254564634878345083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18661080339419513171126777 13995810254564634878345083)
    ·
      refine ⟨20993715381846952317517625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13995810254564634878345083 20993715381846952317517625)
      ·
        refine ⟨15745286536385214238138219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20993715381846952317517625 15745286536385214238138219)
        ·
          refine ⟨23617929804577821357207329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15745286536385214238138219 23617929804577821357207329)
          ·
            refine ⟨17713447353433366017905497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23617929804577821357207329 17713447353433366017905497)
            ·
              refine ⟨13285085515075024513429123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17713447353433366017905497 13285085515075024513429123)
              ·
                refine ⟨19927628272612536770143685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13285085515075024513429123 19927628272612536770143685)
                ·
                  refine ⟨3736430301114850644401941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19927628272612536770143685 3736430301114850644401941)
                  ·
                    refine ⟨175145170364758623956341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3736430301114850644401941 175145170364758623956341)
                    ·
                      rfl

theorem cell22_511641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 1, 4, 6].length) (baseStart_511641 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_511641 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_511641 prefixEnd_511641 := by exact prefixLift 511641
  have htrace : WordTrace (prefixWord ++ tailWord_511641) baseStart_511641 baseEnd_511641 := by
    simpa [prefixWord, tailWord_511641, baseEnd_511641] using wordTrace_append hprefix tailTrace_511641
  have hstable : (prefixWord ++ tailWord_511641).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_511641).length < 2 ^ (prefixWord ++ tailWord_511641).sum := by decide
  have hdescent : baseEnd_511641 < baseStart_511641 := by decide
  rcases family_descends (prefixWord ++ tailWord_511641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_511647 : List Nat := [1, 1, 2, 7, 1, 1, 2, 1, 2, 4]
def baseStart_511647 : Nat := 118140960795 + 511647 * 2 ^ 59
def prefixEnd_511647 : Nat := 4983230072969 + 3 ^ 40 * 511647 * 2
def baseEnd_511647 : Nat := 175147224287376608306323

theorem tailTrace_511647 : CollatzResearch.WordTrace tailWord_511647 prefixEnd_511647 175147224287376608306323 := by
  unfold tailWord_511647
  simp only [CollatzResearch.WordTrace]
  refine ⟨18661299177397776195845195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12440866118265184130563463 18661299177397776195845195)
  ·
    refine ⟨27991948766096664293767793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18661299177397776195845195 27991948766096664293767793)
    ·
      refine ⟨20993961574572498220325845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27991948766096664293767793 20993961574572498220325845)
      ·
        refine ⟨492045974404042927038887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 20993961574572498220325845 492045974404042927038887)
        ·
          refine ⟨738068961606064390558331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 492045974404042927038887 738068961606064390558331)
          ·
            refine ⟨1107103442409096585837497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 738068961606064390558331 1107103442409096585837497)
            ·
              refine ⟨830327581806822439378123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1107103442409096585837497 830327581806822439378123)
              ·
                refine ⟨1245491372710233659067185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 830327581806822439378123 1245491372710233659067185)
                ·
                  refine ⟨934118529532675244300389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1245491372710233659067185 934118529532675244300389)
                  ·
                    refine ⟨175147224287376608306323, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 934118529532675244300389 175147224287376608306323)
                    ·
                      rfl

theorem cell22_511647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 1, 2, 1, 2, 4].length) (baseStart_511647 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_511647 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_511647 prefixEnd_511647 := by exact prefixLift 511647
  have htrace : WordTrace (prefixWord ++ tailWord_511647) baseStart_511647 baseEnd_511647 := by
    simpa [prefixWord, tailWord_511647, baseEnd_511647] using wordTrace_append hprefix tailTrace_511647
  have hstable : (prefixWord ++ tailWord_511647).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_511647).length < 2 ^ (prefixWord ++ tailWord_511647).sum := by decide
  have hdescent : baseEnd_511647 < baseStart_511647 := by decide
  rcases family_descends (prefixWord ++ tailWord_511647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_511673 : List Nat := [1, 2, 1, 4, 1, 1, 3, 4, 5]
def baseStart_511673 : Nat := 118140960795 + 511673 * 2 ^ 59
def prefixEnd_511673 : Nat := 4983230072969 + 3 ^ 40 * 511673 * 2
def baseEnd_511673 : Nat := 58385374872907069052081

theorem tailTrace_511673 : CollatzResearch.WordTrace tailWord_511673 prefixEnd_511673 58385374872907069052081 := by
  unfold tailWord_511673
  simp only [CollatzResearch.WordTrace]
  refine ⟨18662247475303582636291673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12441498316869055090861115 18662247475303582636291673)
  ·
    refine ⟨13996685606477686977218755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18662247475303582636291673 13996685606477686977218755)
    ·
      refine ⟨20995028409716530465828133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13996685606477686977218755 20995028409716530465828133)
      ·
        refine ⟨3936567826821849462342775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20995028409716530465828133 3936567826821849462342775)
        ·
          refine ⟨5904851740232774193514163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3936567826821849462342775 5904851740232774193514163)
          ·
            refine ⟨8857277610349161290271245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5904851740232774193514163 8857277610349161290271245)
            ·
              refine ⟨3321479103880935483851717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8857277610349161290271245 3321479103880935483851717)
              ·
                refine ⟨622777331977675403222197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3321479103880935483851717 622777331977675403222197)
                ·
                  refine ⟨58385374872907069052081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 622777331977675403222197 58385374872907069052081)
                  ·
                    rfl

theorem cell22_511673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 3, 4, 5].length) (baseStart_511673 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_511673 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_511673 prefixEnd_511673 := by exact prefixLift 511673
  have htrace : WordTrace (prefixWord ++ tailWord_511673) baseStart_511673 baseEnd_511673 := by
    simpa [prefixWord, tailWord_511673, baseEnd_511673] using wordTrace_append hprefix tailTrace_511673
  have hstable : (prefixWord ++ tailWord_511673).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_511673).length < 2 ^ (prefixWord ++ tailWord_511673).sum := by decide
  have hdescent : baseEnd_511673 < baseStart_511673 := by decide
  rcases family_descends (prefixWord ++ tailWord_511673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_511677 : List Nat := [1, 4, 1, 2, 1, 2, 3, 4, 1, 3]
def baseStart_511677 : Nat := 118140960795 + 511677 * 2 ^ 59
def prefixEnd_511677 : Nat := 4983230072969 + 3 ^ 40 * 511677 * 2
def baseEnd_511677 : Nat := 175157493900466530056231

theorem tailTrace_511677 : CollatzResearch.WordTrace tailWord_511677 prefixEnd_511677 175157493900466530056231 := by
  unfold tailWord_511677
  simp only [CollatzResearch.WordTrace]
  refine ⟨18662393367289091319437285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12441595578192727546291523 18662393367289091319437285)
  ·
    refine ⟨3499198756366704622394491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18662393367289091319437285 3499198756366704622394491)
    ·
      refine ⟨5248798134550056933591737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3499198756366704622394491 5248798134550056933591737)
      ·
        refine ⟨3936598600912542700193803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5248798134550056933591737 3936598600912542700193803)
        ·
          refine ⟨5904897901368814050290705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3936598600912542700193803 5904897901368814050290705)
          ·
            refine ⟨4428673426026610537718029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5904897901368814050290705 4428673426026610537718029)
            ·
              refine ⟨1660752534759978951644261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4428673426026610537718029 1660752534759978951644261)
              ·
                refine ⟨311391100267496053433299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1660752534759978951644261 311391100267496053433299)
                ·
                  refine ⟨467086650401244080149949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 311391100267496053433299 467086650401244080149949)
                  ·
                    refine ⟨175157493900466530056231, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 467086650401244080149949 175157493900466530056231)
                    ·
                      rfl

theorem cell22_511677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 3, 4, 1, 3].length) (baseStart_511677 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_511677 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_511677 prefixEnd_511677 := by exact prefixLift 511677
  have htrace : WordTrace (prefixWord ++ tailWord_511677) baseStart_511677 baseEnd_511677 := by
    simpa [prefixWord, tailWord_511677, baseEnd_511677] using wordTrace_append hprefix tailTrace_511677
  have hstable : (prefixWord ++ tailWord_511677).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_511677).length < 2 ^ (prefixWord ++ tailWord_511677).sum := by decide
  have hdescent : baseEnd_511677 < baseStart_511677 := by decide
  rcases family_descends (prefixWord ++ tailWord_511677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_511688 : List Nat := [2, 1, 3, 1, 2, 2, 3, 1, 2, 5]
def baseStart_511688 : Nat := 118140960795 + 511688 * 2 ^ 59
def prefixEnd_511688 : Nat := 4983230072969 + 3 ^ 40 * 511688 * 2
def baseEnd_511688 : Nat := 175161259425266168031197

theorem tailTrace_511688 : CollatzResearch.WordTrace tailWord_511688 prefixEnd_511688 175161259425266168031197 := by
  unfold tailWord_511688
  simp only [CollatzResearch.WordTrace]
  refine ⟨9331397285124620099043859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12441863046832826798725145 9331397285124620099043859)
  ·
    refine ⟨13997095927686930148565789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9331397285124620099043859 13997095927686930148565789)
    ·
      refine ⟨5248910972882598805712171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13997095927686930148565789 5248910972882598805712171)
      ·
        refine ⟨7873366459323898208568257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5248910972882598805712171 7873366459323898208568257)
        ·
          refine ⟨5905024844492923656426193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7873366459323898208568257 5905024844492923656426193)
          ·
            refine ⟨4428768633369692742319645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5905024844492923656426193 4428768633369692742319645)
            ·
              refine ⟨1660788237513634778369867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4428768633369692742319645 1660788237513634778369867)
              ·
                refine ⟨2491182356270452167554801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1660788237513634778369867 2491182356270452167554801)
                ·
                  refine ⟨1868386767202839125666101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2491182356270452167554801 1868386767202839125666101)
                  ·
                    refine ⟨175161259425266168031197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1868386767202839125666101 175161259425266168031197)
                    ·
                      rfl

theorem cell22_511688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 3, 1, 2, 5].length) (baseStart_511688 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_511688 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_511688 prefixEnd_511688 := by exact prefixLift 511688
  have htrace : WordTrace (prefixWord ++ tailWord_511688) baseStart_511688 baseEnd_511688 := by
    simpa [prefixWord, tailWord_511688, baseEnd_511688] using wordTrace_append hprefix tailTrace_511688
  have hstable : (prefixWord ++ tailWord_511688).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_511688).length < 2 ^ (prefixWord ++ tailWord_511688).sum := by decide
  have hdescent : baseEnd_511688 < baseStart_511688 := by decide
  rcases family_descends (prefixWord ++ tailWord_511688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_511703 : List Nat := [1, 1, 3, 2, 1, 3, 1, 3, 3, 4]
def baseStart_511703 : Nat := 118140960795 + 511703 * 2 ^ 59
def prefixEnd_511703 : Nat := 4983230072969 + 3 ^ 40 * 511703 * 2
def baseEnd_511703 : Nat := 175166394231811128906151

theorem tailTrace_511703 : CollatzResearch.WordTrace tailWord_511703 prefixEnd_511703 175166394231811128906151 := by
  unfold tailWord_511703
  simp only [CollatzResearch.WordTrace]
  refine ⟨18663341665194897759883763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12442227776796598506589175 18663341665194897759883763)
  ·
    refine ⟨27995012497792346639825645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18663341665194897759883763 27995012497792346639825645)
    ·
      refine ⟨10498129686672129989934617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27995012497792346639825645 10498129686672129989934617)
      ·
        refine ⟨7873597265004097492450963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10498129686672129989934617 7873597265004097492450963)
        ·
          refine ⟨11810395897506146238676445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7873597265004097492450963 11810395897506146238676445)
          ·
            refine ⟨4428898461564804839503667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11810395897506146238676445 4428898461564804839503667)
            ·
              refine ⟨6643347692347207259255501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4428898461564804839503667 6643347692347207259255501)
              ·
                refine ⟨2491255384630202722220813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6643347692347207259255501 2491255384630202722220813)
                ·
                  refine ⟨934220769236326020832805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2491255384630202722220813 934220769236326020832805)
                  ·
                    refine ⟨175166394231811128906151, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 934220769236326020832805 175166394231811128906151)
                    ·
                      rfl

theorem cell22_511703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 1, 3, 3, 4].length) (baseStart_511703 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_511703 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_511703 prefixEnd_511703 := by exact prefixLift 511703
  have htrace : WordTrace (prefixWord ++ tailWord_511703) baseStart_511703 baseEnd_511703 := by
    simpa [prefixWord, tailWord_511703, baseEnd_511703] using wordTrace_append hprefix tailTrace_511703
  have hstable : (prefixWord ++ tailWord_511703).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_511703).length < 2 ^ (prefixWord ++ tailWord_511703).sum := by decide
  have hdescent : baseEnd_511703 < baseStart_511703 := by decide
  rcases family_descends (prefixWord ++ tailWord_511703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_511735 : List Nat := [1, 1, 3, 1, 1, 1, 6, 4, 4]
def baseStart_511735 : Nat := 118140960795 + 511735 * 2 ^ 59
def prefixEnd_511735 : Nat := 4983230072969 + 3 ^ 40 * 511735 * 2
def baseEnd_511735 : Nat := 58392449495257904035351

theorem tailTrace_511735 : CollatzResearch.WordTrace tailWord_511735 prefixEnd_511735 58392449495257904035351 := by
  unfold tailWord_511735
  simp only [CollatzResearch.WordTrace]
  refine ⟨18664508801078967225048659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12443005867385978150032439 18664508801078967225048659)
  ·
    refine ⟨27996763201618450837572989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18664508801078967225048659 27996763201618450837572989)
    ·
      refine ⟨10498786200606919064089871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27996763201618450837572989 10498786200606919064089871)
      ·
        refine ⟨15748179300910378596134807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10498786200606919064089871 15748179300910378596134807)
        ·
          refine ⟨23622268951365567894202211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15748179300910378596134807 23622268951365567894202211)
          ·
            refine ⟨35433403427048351841303317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23622268951365567894202211 35433403427048351841303317)
            ·
              refine ⟨1660940785642891492561093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 35433403427048351841303317 1660940785642891492561093)
              ·
                refine ⟨311426397308042154855205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1660940785642891492561093 311426397308042154855205)
                ·
                  refine ⟨58392449495257904035351, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 311426397308042154855205 58392449495257904035351)
                  ·
                    rfl

theorem cell22_511735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 6, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 6, 4, 4].length) (baseStart_511735 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_511735 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_511735 prefixEnd_511735 := by exact prefixLift 511735
  have htrace : WordTrace (prefixWord ++ tailWord_511735) baseStart_511735 baseEnd_511735 := by
    simpa [prefixWord, tailWord_511735, baseEnd_511735] using wordTrace_append hprefix tailTrace_511735
  have hstable : (prefixWord ++ tailWord_511735).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_511735).length < 2 ^ (prefixWord ++ tailWord_511735).sum := by decide
  have hdescent : baseEnd_511735 < baseStart_511735 := by decide
  rcases family_descends (prefixWord ++ tailWord_511735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_511780 : List Nat := [2, 3, 1, 3, 2, 3, 8]
def baseStart_511780 : Nat := 118140960795 + 511780 * 2 ^ 59
def prefixEnd_511780 : Nat := 4983230072969 + 3 ^ 40 * 511780 * 2
def baseEnd_511780 : Nat := 6488620477978096101145

theorem tailTrace_511780 : CollatzResearch.WordTrace tailWord_511780 prefixEnd_511780 6488620477978096101145 := by
  unfold tailWord_511780
  simp only [CollatzResearch.WordTrace]
  refine ⟨9333075042957969955218397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12444100057277293273624529 9333075042957969955218397)
  ·
    refine ⟨3499903141109238733206899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9333075042957969955218397 3499903141109238733206899)
    ·
      refine ⟨5249854711663858099810349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3499903141109238733206899 5249854711663858099810349)
      ·
        refine ⟨1968695516873946787428881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5249854711663858099810349 1968695516873946787428881)
        ·
          refine ⟨1476521637655460090571661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1968695516873946787428881 1476521637655460090571661)
          ·
            refine ⟨553695614120797533964373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1476521637655460090571661 553695614120797533964373)
            ·
              refine ⟨6488620477978096101145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 553695614120797533964373 6488620477978096101145)
              ·
                rfl

theorem cell22_511780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 3, 8].length) (baseStart_511780 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_511780 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_511780 prefixEnd_511780 := by exact prefixLift 511780
  have htrace : WordTrace (prefixWord ++ tailWord_511780) baseStart_511780 baseEnd_511780 := by
    simpa [prefixWord, tailWord_511780, baseEnd_511780] using wordTrace_append hprefix tailTrace_511780
  have hstable : (prefixWord ++ tailWord_511780).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_511780).length < 2 ^ (prefixWord ++ tailWord_511780).sum := by decide
  have hdescent : baseEnd_511780 < baseStart_511780 := by decide
  rcases family_descends (prefixWord ++ tailWord_511780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_511842 : List Nat := [3, 3, 2, 1, 2, 1, 1, 4, 5]
def baseStart_511842 : Nat := 118140960795 + 511842 * 2 ^ 59
def prefixEnd_511842 : Nat := 4983230072969 + 3 ^ 40 * 511842 * 2
def baseEnd_511842 : Nat := 58404658924153699893575

theorem tailTrace_511842 : CollatzResearch.WordTrace tailWord_511842 prefixEnd_511842 58404658924153699893575 := by
  unfold tailWord_511842
  simp only [CollatzResearch.WordTrace]
  refine ⟨4667102852922831124798445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12445607607794216332795853 4667102852922831124798445)
  ·
    refine ⟨1750163569846061671799417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4667102852922831124798445 1750163569846061671799417)
    ·
      refine ⟨1312622677384546253849563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1750163569846061671799417 1312622677384546253849563)
      ·
        refine ⟨1968934016076819380774345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1312622677384546253849563 1968934016076819380774345)
        ·
          refine ⟨1476700512057614535580759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1968934016076819380774345 1476700512057614535580759)
          ·
            refine ⟨2215050768086421803371139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1476700512057614535580759 2215050768086421803371139)
            ·
              refine ⟨3322576152129632705056709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2215050768086421803371139 3322576152129632705056709)
              ·
                refine ⟨622983028524306132198133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3322576152129632705056709 622983028524306132198133)
                ·
                  refine ⟨58404658924153699893575, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 622983028524306132198133 58404658924153699893575)
                  ·
                    rfl

theorem cell22_511842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 1, 4, 5].length) (baseStart_511842 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_511842 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_511842 prefixEnd_511842 := by exact prefixLift 511842
  have htrace : WordTrace (prefixWord ++ tailWord_511842) baseStart_511842 baseEnd_511842 := by
    simpa [prefixWord, tailWord_511842, baseEnd_511842] using wordTrace_append hprefix tailTrace_511842
  have hstable : (prefixWord ++ tailWord_511842).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_511842).length < 2 ^ (prefixWord ++ tailWord_511842).sum := by decide
  have hdescent : baseEnd_511842 < baseStart_511842 := by decide
  rcases family_descends (prefixWord ++ tailWord_511842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_511919 : List Nat := [1, 1, 2, 1, 2, 2, 7, 1, 2, 3]
def baseStart_511919 : Nat := 118140960795 + 511919 * 2 ^ 59
def prefixEnd_511919 : Nat := 4983230072969 + 3 ^ 40 * 511919 * 2
def baseEnd_511919 : Nat := 175240335446058565505489

theorem tailTrace_511919 : CollatzResearch.WordTrace tailWord_511919 prefixEnd_511919 175240335446058565505489 := by
  unfold tailWord_511919
  simp only [CollatzResearch.WordTrace]
  refine ⟨18671219832412366649746811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12447479888274911099831207 18671219832412366649746811)
  ·
    refine ⟨28006829748618549974620217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18671219832412366649746811 28006829748618549974620217)
    ·
      refine ⟨21005122311463912480965163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28006829748618549974620217 21005122311463912480965163)
      ·
        refine ⟨31507683467195868721447745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21005122311463912480965163 31507683467195868721447745)
        ·
          refine ⟨23630762600396901541085809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31507683467195868721447745 23630762600396901541085809)
          ·
            refine ⟨17723071950297676155814357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23630762600396901541085809 17723071950297676155814357)
            ·
              refine ⟨415384498835101784901899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 17723071950297676155814357 415384498835101784901899)
              ·
                refine ⟨623076748252652677352849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 415384498835101784901899 623076748252652677352849)
                ·
                  refine ⟨467307561189489508014637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 623076748252652677352849 467307561189489508014637)
                  ·
                    refine ⟨175240335446058565505489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 467307561189489508014637 175240335446058565505489)
                    ·
                      rfl

theorem cell22_511919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 7, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 7, 1, 2, 3].length) (baseStart_511919 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_511919 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_511919 prefixEnd_511919 := by exact prefixLift 511919
  have htrace : WordTrace (prefixWord ++ tailWord_511919) baseStart_511919 baseEnd_511919 := by
    simpa [prefixWord, tailWord_511919, baseEnd_511919] using wordTrace_append hprefix tailTrace_511919
  have hstable : (prefixWord ++ tailWord_511919).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_511919).length < 2 ^ (prefixWord ++ tailWord_511919).sum := by decide
  have hdescent : baseEnd_511919 < baseStart_511919 := by decide
  rcases family_descends (prefixWord ++ tailWord_511919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_511960 : List Nat := [2, 1, 2, 2, 2, 2, 1, 3, 7]
def baseStart_511960 : Nat := 118140960795 + 511960 * 2 ^ 59
def prefixEnd_511960 : Nat := 4983230072969 + 3 ^ 40 * 511960 * 2
def baseEnd_511960 : Nat := 58418123527982708410121

theorem tailTrace_511960 : CollatzResearch.WordTrace tailWord_511960 prefixEnd_511960 58418123527982708410121 := by
  unfold tailWord_511960
  simp only [CollatzResearch.WordTrace]
  refine ⟨9336357612631915325994667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12448476816842553767992889 9336357612631915325994667)
  ·
    refine ⟨14004536418947872988992001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9336357612631915325994667 14004536418947872988992001)
    ·
      refine ⟨10503402314210904741744001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14004536418947872988992001 10503402314210904741744001)
      ·
        refine ⟨7877551735658178556308001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10503402314210904741744001 7877551735658178556308001)
        ·
          refine ⟨5908163801743633917231001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7877551735658178556308001 5908163801743633917231001)
          ·
            refine ⟨4431122851307725437923251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5908163801743633917231001 4431122851307725437923251)
            ·
              refine ⟨6646684276961588156884877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4431122851307725437923251 6646684276961588156884877)
              ·
                refine ⟨2492506603860595558831829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6646684276961588156884877 2492506603860595558831829)
                ·
                  refine ⟨58418123527982708410121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2492506603860595558831829 58418123527982708410121)
                  ·
                    rfl

theorem cell22_511960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 1, 3, 7].length) (baseStart_511960 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_511960 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_511960 prefixEnd_511960 := by exact prefixLift 511960
  have htrace : WordTrace (prefixWord ++ tailWord_511960) baseStart_511960 baseEnd_511960 := by
    simpa [prefixWord, tailWord_511960, baseEnd_511960] using wordTrace_append hprefix tailTrace_511960
  have hstable : (prefixWord ++ tailWord_511960).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_511960).length < 2 ^ (prefixWord ++ tailWord_511960).sum := by decide
  have hdescent : baseEnd_511960 < baseStart_511960 := by decide
  rcases family_descends (prefixWord ++ tailWord_511960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_511970 : List Nat := [3, 3, 3, 1, 2, 2, 2, 1, 2, 3]
def baseStart_511970 : Nat := 118140960795 + 511970 * 2 ^ 59
def prefixEnd_511970 : Nat := 4983230072969 + 3 ^ 40 * 511970 * 2
def baseEnd_511970 : Nat := 175257793788311432480333

theorem tailTrace_511970 : CollatzResearch.WordTrace tailWord_511970 prefixEnd_511970 175257793788311432480333 := by
  unfold tailWord_511970
  simp only [CollatzResearch.WordTrace]
  refine ⟨4668269988806900589963341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12448719970151734906568909 4668269988806900589963341)
  ·
    refine ⟨1750601245802587721236253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4668269988806900589963341 1750601245802587721236253)
    ·
      refine ⟨656475467175970395463595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1750601245802587721236253 656475467175970395463595)
      ·
        refine ⟨984713200763955593195393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 656475467175970395463595 984713200763955593195393)
        ·
          refine ⟨738534900572966694896545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 984713200763955593195393 738534900572966694896545)
          ·
            refine ⟨553901175429725021172409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 738534900572966694896545 553901175429725021172409)
            ·
              refine ⟨415425881572293765879307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 553901175429725021172409 415425881572293765879307)
              ·
                refine ⟨623138822358440648818961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 415425881572293765879307 623138822358440648818961)
                ·
                  refine ⟨467354116768830486614221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 623138822358440648818961 467354116768830486614221)
                  ·
                    refine ⟨175257793788311432480333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 467354116768830486614221 175257793788311432480333)
                    ·
                      rfl

theorem cell22_511970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 2, 2, 1, 2, 3].length) (baseStart_511970 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_511970 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_511970 prefixEnd_511970 := by exact prefixLift 511970
  have htrace : WordTrace (prefixWord ++ tailWord_511970) baseStart_511970 baseEnd_511970 := by
    simpa [prefixWord, tailWord_511970, baseEnd_511970] using wordTrace_append hprefix tailTrace_511970
  have hstable : (prefixWord ++ tailWord_511970).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_511970).length < 2 ^ (prefixWord ++ tailWord_511970).sum := by decide
  have hdescent : baseEnd_511970 < baseStart_511970 := by decide
  rcases family_descends (prefixWord ++ tailWord_511970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_512037 : List Nat := [1, 3, 1, 2, 2, 3, 1, 3, 1, 5]
def baseStart_512037 : Nat := 118140960795 + 512037 * 2 ^ 59
def prefixEnd_512037 : Nat := 4983230072969 + 3 ^ 40 * 512037 * 2
def baseEnd_512037 : Nat := 175280729257545591055127

theorem tailTrace_512037 : CollatzResearch.WordTrace tailWord_512037 prefixEnd_512037 175280729257545591055127 := by
  unfold tailWord_512037
  simp only [CollatzResearch.WordTrace]
  refine ⟨18675523645984872802542365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12450349097323248535028243 18675523645984872802542365)
  ·
    refine ⟨7003321367244327300953387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18675523645984872802542365 7003321367244327300953387)
    ·
      refine ⟨10504982050866490951430081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7003321367244327300953387 10504982050866490951430081)
      ·
        refine ⟨7878736538149868213572561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10504982050866490951430081 7878736538149868213572561)
        ·
          refine ⟨5909052403612401160179421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7878736538149868213572561 5909052403612401160179421)
          ·
            refine ⟨2215894651354650435067283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5909052403612401160179421 2215894651354650435067283)
            ·
              refine ⟨3323841977031975652600925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2215894651354650435067283 3323841977031975652600925)
              ·
                refine ⟨1246440741386990869725347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3323841977031975652600925 1246440741386990869725347)
                ·
                  refine ⟨1869661112080486304588021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1246440741386990869725347 1869661112080486304588021)
                  ·
                    refine ⟨175280729257545591055127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1869661112080486304588021 175280729257545591055127)
                    ·
                      rfl

theorem cell22_512037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 1, 3, 1, 5].length) (baseStart_512037 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_512037 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_512037 prefixEnd_512037 := by exact prefixLift 512037
  have htrace : WordTrace (prefixWord ++ tailWord_512037) baseStart_512037 baseEnd_512037 := by
    simpa [prefixWord, tailWord_512037, baseEnd_512037] using wordTrace_append hprefix tailTrace_512037
  have hstable : (prefixWord ++ tailWord_512037).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_512037).length < 2 ^ (prefixWord ++ tailWord_512037).sum := by decide
  have hdescent : baseEnd_512037 < baseStart_512037 := by decide
  rcases family_descends (prefixWord ++ tailWord_512037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_512054 : List Nat := [5, 1, 2, 1, 1, 1, 1, 4, 1, 5]
def baseStart_512054 : Nat := 118140960795 + 512054 * 2 ^ 59
def prefixEnd_512054 : Nat := 4983230072969 + 3 ^ 40 * 512054 * 2
def baseEnd_512054 : Nat := 175286548704963213380075

theorem tailTrace_512054 : CollatzResearch.WordTrace tailWord_512054 prefixEnd_512054 175286548704963213380075 := by
  unfold tailWord_512054
  simp only [CollatzResearch.WordTrace]
  refine ⟨1167258980432705294119451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 12450762457948856470607477 1167258980432705294119451)
  ·
    refine ⟨1750888470649057941179177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1167258980432705294119451 1750888470649057941179177)
    ·
      refine ⟨1313166352986793455884383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1750888470649057941179177 1313166352986793455884383)
      ·
        refine ⟨1969749529480190183826575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1313166352986793455884383 1969749529480190183826575)
        ·
          refine ⟨2954624294220285275739863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1969749529480190183826575 2954624294220285275739863)
          ·
            refine ⟨4431936441330427913609795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2954624294220285275739863 4431936441330427913609795)
            ·
              refine ⟨6647904661995641870414693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4431936441330427913609795 6647904661995641870414693)
              ·
                refine ⟨1246482124124182850702755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6647904661995641870414693 1246482124124182850702755)
                ·
                  refine ⟨1869723186186274276054133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1246482124124182850702755 1869723186186274276054133)
                  ·
                    refine ⟨175286548704963213380075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1869723186186274276054133 175286548704963213380075)
                    ·
                      rfl

theorem cell22_512054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 1, 4, 1, 5].length) (baseStart_512054 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_512054 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_512054 prefixEnd_512054 := by exact prefixLift 512054
  have htrace : WordTrace (prefixWord ++ tailWord_512054) baseStart_512054 baseEnd_512054 := by
    simpa [prefixWord, tailWord_512054, baseEnd_512054] using wordTrace_append hprefix tailTrace_512054
  have hstable : (prefixWord ++ tailWord_512054).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_512054).length < 2 ^ (prefixWord ++ tailWord_512054).sum := by decide
  have hdescent : baseEnd_512054 < baseStart_512054 := by decide
  rcases family_descends (prefixWord ++ tailWord_512054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_512056 : List Nat := [2, 1, 2, 1, 6, 1, 2, 3, 4]
def baseStart_512056 : Nat := 118140960795 + 512056 * 2 ^ 59
def prefixEnd_512056 : Nat := 4983230072969 + 3 ^ 40 * 512056 * 2
def baseEnd_512056 : Nat := 58429077781945291610023

theorem tailTrace_512056 : CollatzResearch.WordTrace tailWord_512056 prefixEnd_512056 58429077781945291610023 := by
  unfold tailWord_512056
  simp only [CollatzResearch.WordTrace]
  refine ⟨9338108316458019523742011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12450811088610692698322681 9338108316458019523742011)
  ·
    refine ⟨14007162474687029285613017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9338108316458019523742011 14007162474687029285613017)
    ·
      refine ⟨10505371856015271964209763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14007162474687029285613017 10505371856015271964209763)
      ·
        refine ⟨15758057784022907946314645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10505371856015271964209763 15758057784022907946314645)
        ·
          refine ⟨738658958626073809983499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 15758057784022907946314645 738658958626073809983499)
          ·
            refine ⟨1107988437939110714975249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 738658958626073809983499 1107988437939110714975249)
            ·
              refine ⟨830991328454333036231437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1107988437939110714975249 830991328454333036231437)
              ·
                refine ⟨311621748170374888586789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 830991328454333036231437 311621748170374888586789)
                ·
                  refine ⟨58429077781945291610023, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 311621748170374888586789 58429077781945291610023)
                  ·
                    rfl

theorem cell22_512056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 1, 2, 3, 4].length) (baseStart_512056 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_512056 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_512056 prefixEnd_512056 := by exact prefixLift 512056
  have htrace : WordTrace (prefixWord ++ tailWord_512056) baseStart_512056 baseEnd_512056 := by
    simpa [prefixWord, tailWord_512056, baseEnd_512056] using wordTrace_append hprefix tailTrace_512056
  have hstable : (prefixWord ++ tailWord_512056).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_512056).length < 2 ^ (prefixWord ++ tailWord_512056).sum := by decide
  have hdescent : baseEnd_512056 < baseStart_512056 := by decide
  rcases family_descends (prefixWord ++ tailWord_512056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_512086 : List Nat := [5, 2, 2, 1, 1, 1, 1, 2, 1, 6]
def baseStart_512086 : Nat := 118140960795 + 512086 * 2 ^ 59
def prefixEnd_512086 : Nat := 4983230072969 + 3 ^ 40 * 512086 * 2
def baseEnd_512086 : Nat := 175297502958925796579977

theorem tailTrace_512086 : CollatzResearch.WordTrace tailWord_512086 prefixEnd_512086 175297502958925796579977 := by
  unfold tailWord_512086
  simp only [CollatzResearch.WordTrace]
  refine ⟨1167331926425459635692257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 12451540548538236114050741 1167331926425459635692257)
  ·
    refine ⟨875498944819094726769193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1167331926425459635692257 875498944819094726769193)
    ·
      refine ⟨656624208614321045076895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 875498944819094726769193 656624208614321045076895)
      ·
        refine ⟨984936312921481567615343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 656624208614321045076895 984936312921481567615343)
        ·
          refine ⟨1477404469382222351423015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 984936312921481567615343 1477404469382222351423015)
          ·
            refine ⟨2216106704073333527134523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1477404469382222351423015 2216106704073333527134523)
            ·
              refine ⟨3324160056110000290701785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2216106704073333527134523 3324160056110000290701785)
              ·
                refine ⟨2493120042082500218026339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3324160056110000290701785 2493120042082500218026339)
                ·
                  refine ⟨3739680063123750327039509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2493120042082500218026339 3739680063123750327039509)
                  ·
                    refine ⟨175297502958925796579977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3739680063123750327039509 175297502958925796579977)
                    ·
                      rfl

theorem cell22_512086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 1, 2, 1, 6].length) (baseStart_512086 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_512086 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_512086 prefixEnd_512086 := by exact prefixLift 512086
  have htrace : WordTrace (prefixWord ++ tailWord_512086) baseStart_512086 baseEnd_512086 := by
    simpa [prefixWord, tailWord_512086, baseEnd_512086] using wordTrace_append hprefix tailTrace_512086
  have hstable : (prefixWord ++ tailWord_512086).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_512086).length < 2 ^ (prefixWord ++ tailWord_512086).sum := by decide
  have hdescent : baseEnd_512086 < baseStart_512086 := by decide
  rcases family_descends (prefixWord ++ tailWord_512086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_512099 : List Nat := [1, 1, 1, 5, 1, 1, 4, 2, 3, 3]
def baseStart_512099 : Nat := 118140960795 + 512099 * 2 ^ 59
def prefixEnd_512099 : Nat := 4983230072969 + 3 ^ 40 * 512099 * 2
def baseEnd_512099 : Nat := 175301953124598096004937

theorem tailTrace_512099 : CollatzResearch.WordTrace tailWord_512099 prefixEnd_512099 175301953124598096004937 := by
  unfold tailWord_512099
  simp only [CollatzResearch.WordTrace]
  refine ⟨18677784971760257391299351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12451856647840171594199567 18677784971760257391299351)
  ·
    refine ⟨28016677457640386086949027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18677784971760257391299351 28016677457640386086949027)
    ·
      refine ⟨42025016186460579130423541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28016677457640386086949027 42025016186460579130423541)
      ·
        refine ⟨3939845267480679293477207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 42025016186460579130423541 3939845267480679293477207)
        ·
          refine ⟨5909767901221018940215811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3939845267480679293477207 5909767901221018940215811)
          ·
            refine ⟨8864651851831528410323717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5909767901221018940215811 8864651851831528410323717)
            ·
              refine ⟨1662122222218411576935697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8864651851831528410323717 1662122222218411576935697)
              ·
                refine ⟨1246591666663808682701773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1662122222218411576935697 1246591666663808682701773)
                ·
                  refine ⟨467471874998928256013165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1246591666663808682701773 467471874998928256013165)
                  ·
                    refine ⟨175301953124598096004937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 467471874998928256013165 175301953124598096004937)
                    ·
                      rfl

theorem cell22_512099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 4, 2, 3, 3].length) (baseStart_512099 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_512099 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_512099 prefixEnd_512099 := by exact prefixLift 512099
  have htrace : WordTrace (prefixWord ++ tailWord_512099) baseStart_512099 baseEnd_512099 := by
    simpa [prefixWord, tailWord_512099, baseEnd_512099] using wordTrace_append hprefix tailTrace_512099
  have hstable : (prefixWord ++ tailWord_512099).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_512099).length < 2 ^ (prefixWord ++ tailWord_512099).sum := by decide
  have hdescent : baseEnd_512099 < baseStart_512099 := by decide
  rcases family_descends (prefixWord ++ tailWord_512099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
