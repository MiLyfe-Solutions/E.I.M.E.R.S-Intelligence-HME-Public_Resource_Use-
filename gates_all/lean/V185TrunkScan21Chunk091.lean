import V185TrunkScan21Chunk090

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental

namespace V185TrunkScan21Incremental

def tailWord_1102759 : List Nat := [1, 1, 6, 1, 4, 1, 7]
def baseStart_1102759 : Nat := 118140960795 + 1102759 * 2 ^ 59
def prefixEnd_1102759 : Nat := 4983230072969 + 3 ^ 40 * 1102759 * 2
def baseEnd_1102759 : Nat := 27962736447978083162519

theorem tailTrace_1102759 : CollatzResearch.WordTrace tailWord_1102759 prefixEnd_1102759 27962736447978083162519 := by
  unfold tailWord_1102759
  simp only [CollatzResearch.WordTrace]
  refine ⟨40220925011899954088095331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26813950007933302725396887 40220925011899954088095331)
  ·
    refine ⟨60331387517849931132142997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40220925011899954088095331 60331387517849931132142997)
    ·
      refine ⟨2828033789899215521819203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 60331387517849931132142997 2828033789899215521819203)
      ·
        refine ⟨4242050684848823282728805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2828033789899215521819203 4242050684848823282728805)
        ·
          refine ⟨795384503409154365511651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4242050684848823282728805 795384503409154365511651)
          ·
            refine ⟨1193076755113731548267477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 795384503409154365511651 1193076755113731548267477)
            ·
              refine ⟨27962736447978083162519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1193076755113731548267477 27962736447978083162519)
              ·
                rfl

theorem cell21_1102759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 4, 1, 7].length) (baseStart_1102759 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1102759 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1102759 prefixEnd_1102759 := by exact prefixLift 1102759
  have htrace : WordTrace (prefixWord ++ tailWord_1102759) baseStart_1102759 baseEnd_1102759 := by
    simpa [prefixWord, tailWord_1102759, baseEnd_1102759] using wordTrace_append hprefix tailTrace_1102759
  have hstable : (prefixWord ++ tailWord_1102759).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1102759).length < 2 ^ (prefixWord ++ tailWord_1102759).sum := by decide
  have hdescent : baseEnd_1102759 < baseStart_1102759 := by decide
  rcases family_descends (prefixWord ++ tailWord_1102759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1102818 : List Nat := [3, 3, 3, 1, 1, 10]
def baseStart_1102818 : Nat := 118140960795 + 1102818 * 2 ^ 59
def prefixEnd_1102818 : Nat := 4983230072969 + 3 ^ 40 * 1102818 * 2
def baseEnd_1102818 : Nat := 9321410838356731739971

theorem tailTrace_1102818 : CollatzResearch.WordTrace tailWord_1102818 prefixEnd_1102818 9321410838356731739971 := by
  unfold tailWord_1102818
  simp only [CollatzResearch.WordTrace]
  refine ⟨10055769229671551791123277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26815384612457471442995405 10055769229671551791123277)
  ·
    refine ⟨3770913461126831921671229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10055769229671551791123277 3770913461126831921671229)
    ·
      refine ⟨1414092547922561970626711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3770913461126831921671229 1414092547922561970626711)
      ·
        refine ⟨2121138821883842955940067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1414092547922561970626711 2121138821883842955940067)
        ·
          refine ⟨3181708232825764433910101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2121138821883842955940067 3181708232825764433910101)
          ·
            refine ⟨9321410838356731739971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 3181708232825764433910101 9321410838356731739971)
            ·
              rfl

theorem cell21_1102818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 10].length) (baseStart_1102818 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1102818 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1102818 prefixEnd_1102818 := by exact prefixLift 1102818
  have htrace : WordTrace (prefixWord ++ tailWord_1102818) baseStart_1102818 baseEnd_1102818 := by
    simpa [prefixWord, tailWord_1102818, baseEnd_1102818] using wordTrace_append hprefix tailTrace_1102818
  have hstable : (prefixWord ++ tailWord_1102818).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1102818).length < 2 ^ (prefixWord ++ tailWord_1102818).sum := by decide
  have hdescent : baseEnd_1102818 < baseStart_1102818 := by decide
  rcases family_descends (prefixWord ++ tailWord_1102818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1102821 : List Nat := [1, 3, 1, 6, 1, 1, 2, 2, 4]
def baseStart_1102821 : Nat := 118140960795 + 1102821 * 2 ^ 59
def prefixEnd_1102821 : Nat := 4983230072969 + 3 ^ 40 * 1102821 * 2
def baseEnd_1102821 : Nat := 251678777276504418429211

theorem tailTrace_1102821 : CollatzResearch.WordTrace tailWord_1102821 prefixEnd_1102821 251678777276504418429211 := by
  unfold tailWord_1102821
  simp only [CollatzResearch.WordTrace]
  refine ⟨40223186337675338676852317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26815457558450225784568211 40223186337675338676852317)
  ·
    refine ⟨15083694876628252003819619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40223186337675338676852317 15083694876628252003819619)
    ·
      refine ⟨22625542314942378005729429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15083694876628252003819619 22625542314942378005729429)
      ·
        refine ⟨1060572296012923969018567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 22625542314942378005729429 1060572296012923969018567)
        ·
          refine ⟨1590858444019385953527851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1060572296012923969018567 1590858444019385953527851)
          ·
            refine ⟨2386287666029078930291777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1590858444019385953527851 2386287666029078930291777)
            ·
              refine ⟨1789715749521809197718833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2386287666029078930291777 1789715749521809197718833)
              ·
                refine ⟨1342286812141356898289125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1789715749521809197718833 1342286812141356898289125)
                ·
                  refine ⟨251678777276504418429211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1342286812141356898289125 251678777276504418429211)
                  ·
                    rfl

theorem cell21_1102821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 1, 2, 2, 4].length) (baseStart_1102821 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1102821 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1102821 prefixEnd_1102821 := by exact prefixLift 1102821
  have htrace : WordTrace (prefixWord ++ tailWord_1102821) baseStart_1102821 baseEnd_1102821 := by
    simpa [prefixWord, tailWord_1102821, baseEnd_1102821] using wordTrace_append hprefix tailTrace_1102821
  have hstable : (prefixWord ++ tailWord_1102821).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1102821).length < 2 ^ (prefixWord ++ tailWord_1102821).sum := by decide
  have hdescent : baseEnd_1102821 < baseStart_1102821 := by decide
  rcases family_descends (prefixWord ++ tailWord_1102821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1102880 : List Nat := [2, 1, 1, 7, 1, 1, 1, 1, 6]
def baseStart_1102880 : Nat := 118140960795 + 1102880 * 2 ^ 59
def prefixEnd_1102880 : Nat := 4983230072969 + 3 ^ 40 * 1102880 * 2
def baseEnd_1102880 : Nat := 251692241880333426945757

theorem tailTrace_1102880 : CollatzResearch.WordTrace tailWord_1102880 prefixEnd_1102880 251692241880333426945757 := by
  unfold tailWord_1102880
  simp only [CollatzResearch.WordTrace]
  refine ⟨20112669122230795876625047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26816892162974394502166729 20112669122230795876625047)
  ·
    refine ⟨30169003683346193814937571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20112669122230795876625047 30169003683346193814937571)
    ·
      refine ⟨45253505525019290722406357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30169003683346193814937571 45253505525019290722406357)
      ·
        refine ⟨1060629035742639626306399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 45253505525019290722406357 1060629035742639626306399)
        ·
          refine ⟨1590943553613959439459599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1060629035742639626306399 1590943553613959439459599)
          ·
            refine ⟨2386415330420939159189399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1590943553613959439459599 2386415330420939159189399)
            ·
              refine ⟨3579622995631408738784099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2386415330420939159189399 3579622995631408738784099)
              ·
                refine ⟨5369434493447113108176149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3579622995631408738784099 5369434493447113108176149)
                ·
                  refine ⟨251692241880333426945757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5369434493447113108176149 251692241880333426945757)
                  ·
                    rfl

theorem cell21_1102880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 1, 1, 1, 6].length) (baseStart_1102880 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1102880 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1102880 prefixEnd_1102880 := by exact prefixLift 1102880
  have htrace : WordTrace (prefixWord ++ tailWord_1102880) baseStart_1102880 baseEnd_1102880 := by
    simpa [prefixWord, tailWord_1102880, baseEnd_1102880] using wordTrace_append hprefix tailTrace_1102880
  have hstable : (prefixWord ++ tailWord_1102880).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1102880).length < 2 ^ (prefixWord ++ tailWord_1102880).sum := by decide
  have hdescent : baseEnd_1102880 < baseStart_1102880 := by decide
  rcases family_descends (prefixWord ++ tailWord_1102880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1102908 : List Nat := [2, 2, 2, 2, 2, 2, 2, 2, 5]
def baseStart_1102908 : Nat := 118140960795 + 1102908 * 2 ^ 59
def prefixEnd_1102908 : Nat := 4983230072969 + 3 ^ 40 * 1102908 * 2
def baseEnd_1102908 : Nat := 251698631861811600479033

theorem tailTrace_1102908 : CollatzResearch.WordTrace tailWord_1102908 prefixEnd_1102908 251698631861811600479033 := by
  unfold tailWord_1102908
  simp only [CollatzResearch.WordTrace]
  refine ⟨20113179744180076267634689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26817572992240101690179585 20113179744180076267634689)
  ·
    refine ⟨15084884808135057200726017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20113179744180076267634689 15084884808135057200726017)
    ·
      refine ⟨11313663606101292900544513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15084884808135057200726017 11313663606101292900544513)
      ·
        refine ⟨8485247704575969675408385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11313663606101292900544513 8485247704575969675408385)
        ·
          refine ⟨6363935778431977256556289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8485247704575969675408385 6363935778431977256556289)
          ·
            refine ⟨4772951833823982942417217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6363935778431977256556289 4772951833823982942417217)
            ·
              refine ⟨3579713875367987206812913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4772951833823982942417217 3579713875367987206812913)
              ·
                refine ⟨2684785406525990405109685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3579713875367987206812913 2684785406525990405109685)
                ·
                  refine ⟨251698631861811600479033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2684785406525990405109685 251698631861811600479033)
                  ·
                    rfl

theorem cell21_1102908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 2, 2, 5].length) (baseStart_1102908 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1102908 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1102908 prefixEnd_1102908 := by exact prefixLift 1102908
  have htrace : WordTrace (prefixWord ++ tailWord_1102908) baseStart_1102908 baseEnd_1102908 := by
    simpa [prefixWord, tailWord_1102908, baseEnd_1102908] using wordTrace_append hprefix tailTrace_1102908
  have hstable : (prefixWord ++ tailWord_1102908).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1102908).length < 2 ^ (prefixWord ++ tailWord_1102908).sum := by decide
  have hdescent : baseEnd_1102908 < baseStart_1102908 := by decide
  rcases family_descends (prefixWord ++ tailWord_1102908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1102922 : List Nat := [3, 1, 2, 1, 1, 2, 3, 2, 6]
def baseStart_1102922 : Nat := 118140960795 + 1102922 * 2 ^ 59
def prefixEnd_1102922 : Nat := 4983230072969 + 3 ^ 40 * 1102922 * 2
def baseEnd_1102922 : Nat := 251701826852550687245671

theorem tailTrace_1102922 : CollatzResearch.WordTrace tailWord_1102922 prefixEnd_1102922 251701826852550687245671 := by
  unfold tailWord_1102922
  simp only [CollatzResearch.WordTrace]
  refine ⟨10056717527577358231569755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26817913406872955284186013 10056717527577358231569755)
  ·
    refine ⟨15085076291366037347354633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10056717527577358231569755 15085076291366037347354633)
    ·
      refine ⟨11313807218524528010515975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15085076291366037347354633 11313807218524528010515975)
      ·
        refine ⟨16970710827786792015773963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11313807218524528010515975 16970710827786792015773963)
        ·
          refine ⟨25456066241680188023660945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16970710827786792015773963 25456066241680188023660945)
          ·
            refine ⟨19092049681260141017745709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25456066241680188023660945 19092049681260141017745709)
            ·
              refine ⟨7159518630472552881654641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19092049681260141017745709 7159518630472552881654641)
              ·
                refine ⟨5369638972854414661240981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7159518630472552881654641 5369638972854414661240981)
                ·
                  refine ⟨251701826852550687245671, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5369638972854414661240981 251701826852550687245671)
                  ·
                    rfl

theorem cell21_1102922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 3, 2, 6].length) (baseStart_1102922 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1102922 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1102922 prefixEnd_1102922 := by exact prefixLift 1102922
  have htrace : WordTrace (prefixWord ++ tailWord_1102922) baseStart_1102922 baseEnd_1102922 := by
    simpa [prefixWord, tailWord_1102922, baseEnd_1102922] using wordTrace_append hprefix tailTrace_1102922
  have hstable : (prefixWord ++ tailWord_1102922).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1102922).length < 2 ^ (prefixWord ++ tailWord_1102922).sum := by decide
  have hdescent : baseEnd_1102922 < baseStart_1102922 := by decide
  rcases family_descends (prefixWord ++ tailWord_1102922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1102953 : List Nat := [1, 2, 1, 1, 1, 7, 2, 6]
def baseStart_1102953 : Nat := 118140960795 + 1102953 * 2 ^ 59
def prefixEnd_1102953 : Nat := 4983230072969 + 3 ^ 40 * 1102953 * 2
def baseEnd_1102953 : Nat := 83902967158300507409647

theorem tailTrace_1102953 : CollatzResearch.WordTrace tailWord_1102953 prefixEnd_1102953 83902967158300507409647 := by
  unfold tailWord_1102953
  simp only [CollatzResearch.WordTrace]
  refine ⟨40228000773197125220657513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26818667182131416813771675 40228000773197125220657513)
  ·
    refine ⟨30171000579897843915493135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40228000773197125220657513 30171000579897843915493135)
    ·
      refine ⟨45256500869846765873239703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30171000579897843915493135 45256500869846765873239703)
      ·
        refine ⟨67884751304770148809859555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45256500869846765873239703 67884751304770148809859555)
        ·
          refine ⟨101827126957155223214789333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67884751304770148809859555 101827126957155223214789333)
          ·
            refine ⟨2386573288058325544096625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 101827126957155223214789333 2386573288058325544096625)
            ·
              refine ⟨1789929966043744158072469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2386573288058325544096625 1789929966043744158072469)
              ·
                refine ⟨83902967158300507409647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1789929966043744158072469 83902967158300507409647)
                ·
                  rfl

theorem cell21_1102953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 7, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 7, 2, 6].length) (baseStart_1102953 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1102953 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1102953 prefixEnd_1102953 := by exact prefixLift 1102953
  have htrace : WordTrace (prefixWord ++ tailWord_1102953) baseStart_1102953 baseEnd_1102953 := by
    simpa [prefixWord, tailWord_1102953, baseEnd_1102953] using wordTrace_append hprefix tailTrace_1102953
  have hstable : (prefixWord ++ tailWord_1102953).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1102953).length < 2 ^ (prefixWord ++ tailWord_1102953).sum := by decide
  have hdescent : baseEnd_1102953 < baseStart_1102953 := by decide
  rcases family_descends (prefixWord ++ tailWord_1102953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1102967 : List Nat := [1, 1, 3, 1, 1, 4, 2, 1, 7]
def baseStart_1102967 : Nat := 118140960795 + 1102967 * 2 ^ 59
def prefixEnd_1102967 : Nat := 4983230072969 + 3 ^ 40 * 1102967 * 2
def baseEnd_1102967 : Nat := 251712096465640608995579

theorem tailTrace_1102967 : CollatzResearch.WordTrace tailWord_1102967 prefixEnd_1102967 251712096465640608995579 := by
  unfold tailWord_1102967
  simp only [CollatzResearch.WordTrace]
  refine ⟨40228511395146405611667155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26819007596764270407778103 40228511395146405611667155)
  ·
    refine ⟨60342767092719608417500733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40228511395146405611667155 60342767092719608417500733)
    ·
      refine ⟨22628537659769853156562775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 60342767092719608417500733 22628537659769853156562775)
      ·
        refine ⟨33942806489654779734844163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22628537659769853156562775 33942806489654779734844163)
        ·
          refine ⟨50914209734482169602266245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33942806489654779734844163 50914209734482169602266245)
          ·
            refine ⟨9546414325215406800424921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 50914209734482169602266245 9546414325215406800424921)
            ·
              refine ⟨7159810743911555100318691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9546414325215406800424921 7159810743911555100318691)
              ·
                refine ⟨10739716115867332650478037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7159810743911555100318691 10739716115867332650478037)
                ·
                  refine ⟨251712096465640608995579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10739716115867332650478037 251712096465640608995579)
                  ·
                    rfl

theorem cell21_1102967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 2, 1, 7].length) (baseStart_1102967 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1102967 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1102967 prefixEnd_1102967 := by exact prefixLift 1102967
  have htrace : WordTrace (prefixWord ++ tailWord_1102967) baseStart_1102967 baseEnd_1102967 := by
    simpa [prefixWord, tailWord_1102967, baseEnd_1102967] using wordTrace_append hprefix tailTrace_1102967
  have hstable : (prefixWord ++ tailWord_1102967).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1102967).length < 2 ^ (prefixWord ++ tailWord_1102967).sum := by decide
  have hdescent : baseEnd_1102967 < baseStart_1102967 := by decide
  rcases family_descends (prefixWord ++ tailWord_1102967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1103105 : List Nat := [1, 2, 4, 1, 1, 5, 7]
def baseStart_1103105 : Nat := 118140960795 + 1103105 * 2 ^ 59
def prefixEnd_1103105 : Nat := 4983230072969 + 3 ^ 40 * 1103105 * 2
def baseEnd_1103105 : Nat := 27971509993975892855033

theorem tailTrace_1103105 : CollatzResearch.WordTrace tailWord_1103105 prefixEnd_1103105 27971509993975892855033 := by
  unfold tailWord_1103105
  simp only [CollatzResearch.WordTrace]
  refine ⟨40233544668646455180190769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26822363112430970120127179 40233544668646455180190769)
  ·
    refine ⟨30175158501484841385143077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40233544668646455180190769 30175158501484841385143077)
    ·
      refine ⟨5657842219028407759714327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 30175158501484841385143077 5657842219028407759714327)
      ·
        refine ⟨8486763328542611639571491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5657842219028407759714327 8486763328542611639571491)
        ·
          refine ⟨12730144992813917459357237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8486763328542611639571491 12730144992813917459357237)
          ·
            refine ⟨1193451093076304761814741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 12730144992813917459357237 1193451093076304761814741)
            ·
              refine ⟨27971509993975892855033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1193451093076304761814741 27971509993975892855033)
              ·
                rfl

theorem cell21_1103105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 5, 7].length) (baseStart_1103105 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1103105 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1103105 prefixEnd_1103105 := by exact prefixLift 1103105
  have htrace : WordTrace (prefixWord ++ tailWord_1103105) baseStart_1103105 baseEnd_1103105 := by
    simpa [prefixWord, tailWord_1103105, baseEnd_1103105] using wordTrace_append hprefix tailTrace_1103105
  have hstable : (prefixWord ++ tailWord_1103105).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1103105).length < 2 ^ (prefixWord ++ tailWord_1103105).sum := by decide
  have hdescent : baseEnd_1103105 < baseStart_1103105 := by decide
  rcases family_descends (prefixWord ++ tailWord_1103105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1103164 : List Nat := [2, 2, 2, 2, 1, 12]
def baseStart_1103164 : Nat := 118140960795 + 1103164 * 2 ^ 59
def prefixEnd_1103164 : Nat := 4983230072969 + 3 ^ 40 * 1103164 * 2
def baseEnd_1103164 : Nat := 9324335353689334970809

theorem tailTrace_1103164 : CollatzResearch.WordTrace tailWord_1103164 prefixEnd_1103164 9324335353689334970809 := by
  unfold tailWord_1103164
  simp only [CollatzResearch.WordTrace]
  refine ⟨20117848287716354128294273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26823797716955138837725697 20117848287716354128294273)
  ·
    refine ⟨15088386215787265596220705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20117848287716354128294273 15088386215787265596220705)
    ·
      refine ⟨11316289661840449197165529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15088386215787265596220705 11316289661840449197165529)
      ·
        refine ⟨8487217246380336897874147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11316289661840449197165529 8487217246380336897874147)
        ·
          refine ⟨12730825869570505346811221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8487217246380336897874147 12730825869570505346811221)
          ·
            refine ⟨9324335353689334970809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 12730825869570505346811221 9324335353689334970809)
            ·
              rfl

theorem cell21_1103164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 12].length) (baseStart_1103164 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1103164 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1103164 prefixEnd_1103164 := by exact prefixLift 1103164
  have htrace : WordTrace (prefixWord ++ tailWord_1103164) baseStart_1103164 baseEnd_1103164 := by
    simpa [prefixWord, tailWord_1103164, baseEnd_1103164] using wordTrace_append hprefix tailTrace_1103164
  have hstable : (prefixWord ++ tailWord_1103164).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1103164).length < 2 ^ (prefixWord ++ tailWord_1103164).sum := by decide
  have hdescent : baseEnd_1103164 < baseStart_1103164 := by decide
  rcases family_descends (prefixWord ++ tailWord_1103164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1103167 : List Nat := [1, 1, 2, 2, 4, 3, 2, 2, 4]
def baseStart_1103167 : Nat := 118140960795 + 1103167 * 2 ^ 59
def prefixEnd_1103167 : Nat := 4983230072969 + 3 ^ 40 * 1103167 * 2
def baseEnd_1103167 : Nat := 251757739190484705661837

theorem tailTrace_1103167 : CollatzResearch.WordTrace tailWord_1103167 prefixEnd_1103167 251757739190484705661837 := by
  unfold tailWord_1103167
  simp only [CollatzResearch.WordTrace]
  refine ⟨40235805994421839768947755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26823870662947893179298503 40235805994421839768947755)
  ·
    refine ⟨60353708991632759653421633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40235805994421839768947755 60353708991632759653421633)
    ·
      refine ⟨45265281743724569740066225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60353708991632759653421633 45265281743724569740066225)
      ·
        refine ⟨33948961307793427305049669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45265281743724569740066225 33948961307793427305049669)
        ·
          refine ⟨6365430245211267619696813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 33948961307793427305049669 6365430245211267619696813)
          ·
            refine ⟨2387036341954225357386305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6365430245211267619696813 2387036341954225357386305)
            ·
              refine ⟨1790277256465669018039729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2387036341954225357386305 1790277256465669018039729)
              ·
                refine ⟨1342707942349251763529797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1790277256465669018039729 1342707942349251763529797)
                ·
                  refine ⟨251757739190484705661837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1342707942349251763529797 251757739190484705661837)
                  ·
                    rfl

theorem cell21_1103167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 3, 2, 2, 4].length) (baseStart_1103167 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1103167 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1103167 prefixEnd_1103167 := by exact prefixLift 1103167
  have htrace : WordTrace (prefixWord ++ tailWord_1103167) baseStart_1103167 baseEnd_1103167 := by
    simpa [prefixWord, tailWord_1103167, baseEnd_1103167] using wordTrace_append hprefix tailTrace_1103167
  have hstable : (prefixWord ++ tailWord_1103167).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1103167).length < 2 ^ (prefixWord ++ tailWord_1103167).sum := by decide
  have hdescent : baseEnd_1103167 < baseStart_1103167 := by decide
  rcases family_descends (prefixWord ++ tailWord_1103167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1103243 : List Nat := [1, 1, 1, 1, 4, 3, 5, 1, 4]
def baseStart_1103243 : Nat := 118140960795 + 1103243 * 2 ^ 59
def prefixEnd_1103243 : Nat := 4983230072969 + 3 ^ 40 * 1103243 * 2
def baseEnd_1103243 : Nat := 251775083425925462395015

theorem tailTrace_1103243 : CollatzResearch.WordTrace tailWord_1103243 prefixEnd_1103243 251775083425925462395015 := by
  unfold tailWord_1103243
  simp only [CollatzResearch.WordTrace]
  refine ⟨40238577942146504748714383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26825718628097669832476255 40238577942146504748714383)
  ·
    refine ⟨60357866913219757123071575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40238577942146504748714383 60357866913219757123071575)
    ·
      refine ⟨90536800369829635684607363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60357866913219757123071575 90536800369829635684607363)
      ·
        refine ⟨135805200554744453526911045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90536800369829635684607363 135805200554744453526911045)
        ·
          refine ⟨25463475104014585036295821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 135805200554744453526911045 25463475104014585036295821)
          ·
            refine ⟨9548803164005469388610933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25463475104014585036295821 9548803164005469388610933)
            ·
              refine ⟨895200296625512755182275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 9548803164005469388610933 895200296625512755182275)
              ·
                refine ⟨1342800444938269132773413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 895200296625512755182275 1342800444938269132773413)
                ·
                  refine ⟨251775083425925462395015, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1342800444938269132773413 251775083425925462395015)
                  ·
                    rfl

theorem cell21_1103243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 5, 1, 4].length) (baseStart_1103243 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1103243 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1103243 prefixEnd_1103243 := by exact prefixLift 1103243
  have htrace : WordTrace (prefixWord ++ tailWord_1103243) baseStart_1103243 baseEnd_1103243 := by
    simpa [prefixWord, tailWord_1103243, baseEnd_1103243] using wordTrace_append hprefix tailTrace_1103243
  have hstable : (prefixWord ++ tailWord_1103243).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1103243).length < 2 ^ (prefixWord ++ tailWord_1103243).sum := by decide
  have hdescent : baseEnd_1103243 < baseStart_1103243 := by decide
  rcases family_descends (prefixWord ++ tailWord_1103243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1103257 : List Nat := [1, 2, 1, 2, 1, 5, 4, 5]
def baseStart_1103257 : Nat := 118140960795 + 1103257 * 2 ^ 59
def prefixEnd_1103257 : Nat := 4983230072969 + 3 ^ 40 * 1103257 * 2
def baseEnd_1103257 : Nat := 83926092805554849720551

theorem tailTrace_1103257 : CollatzResearch.WordTrace tailWord_1103257 prefixEnd_1103257 83926092805554849720551 := by
  unfold tailWord_1103257
  simp only [CollatzResearch.WordTrace]
  refine ⟨40239088564095785139724025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26826059042730523426482683 40239088564095785139724025)
  ·
    refine ⟨30179316423071838854793019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40239088564095785139724025 30179316423071838854793019)
    ·
      refine ⟨45268974634607758282189529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30179316423071838854793019 45268974634607758282189529)
      ·
        refine ⟨33951730975955818711642147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45268974634607758282189529 33951730975955818711642147)
        ·
          refine ⟨50927596463933728067463221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33951730975955818711642147 50927596463933728067463221)
          ·
            refine ⟨4774462168493787006324677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 50927596463933728067463221 4774462168493787006324677)
            ·
              refine ⟨895211656592585063685877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4774462168493787006324677 895211656592585063685877)
              ·
                refine ⟨83926092805554849720551, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 895211656592585063685877 83926092805554849720551)
                ·
                  rfl

theorem cell21_1103257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 4, 5].length) (baseStart_1103257 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1103257 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1103257 prefixEnd_1103257 := by exact prefixLift 1103257
  have htrace : WordTrace (prefixWord ++ tailWord_1103257) baseStart_1103257 baseEnd_1103257 := by
    simpa [prefixWord, tailWord_1103257, baseEnd_1103257] using wordTrace_append hprefix tailTrace_1103257
  have hstable : (prefixWord ++ tailWord_1103257).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1103257).length < 2 ^ (prefixWord ++ tailWord_1103257).sum := by decide
  have hdescent : baseEnd_1103257 < baseStart_1103257 := by decide
  rcases family_descends (prefixWord ++ tailWord_1103257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1103288 : List Nat := [2, 1, 2, 1, 2, 2, 2, 6, 3]
def baseStart_1103288 : Nat := 118140960795 + 1103288 * 2 ^ 59
def prefixEnd_1103288 : Nat := 4983230072969 + 3 ^ 40 * 1103288 * 2
def baseEnd_1103288 : Nat := 251785353039015384144923

theorem tailTrace_1103288 : CollatzResearch.WordTrace tailWord_1103288 prefixEnd_1103288 251785353039015384144923 := by
  unfold tailWord_1103288
  simp only [CollatzResearch.WordTrace]
  refine ⟨20120109613491738717051259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26826812817988984956068345 20120109613491738717051259)
  ·
    refine ⟨30180164420237608075576889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20120109613491738717051259 30180164420237608075576889)
    ·
      refine ⟨22635123315178206056682667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30180164420237608075576889 22635123315178206056682667)
      ·
        refine ⟨33952684972767309085024001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22635123315178206056682667 33952684972767309085024001)
        ·
          refine ⟨25464513729575481813768001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33952684972767309085024001 25464513729575481813768001)
          ·
            refine ⟨19098385297181611360326001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25464513729575481813768001 19098385297181611360326001)
            ·
              refine ⟨14323788972886208520244501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19098385297181611360326001 14323788972886208520244501)
              ·
                refine ⟨671427608104041024386461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 14323788972886208520244501 671427608104041024386461)
                ·
                  refine ⟨251785353039015384144923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 671427608104041024386461 251785353039015384144923)
                  ·
                    rfl

theorem cell21_1103288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 2, 6, 3].length) (baseStart_1103288 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1103288 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1103288 prefixEnd_1103288 := by exact prefixLift 1103288
  have htrace : WordTrace (prefixWord ++ tailWord_1103288) baseStart_1103288 baseEnd_1103288 := by
    simpa [prefixWord, tailWord_1103288, baseEnd_1103288] using wordTrace_append hprefix tailTrace_1103288
  have hstable : (prefixWord ++ tailWord_1103288).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1103288).length < 2 ^ (prefixWord ++ tailWord_1103288).sum := by decide
  have hdescent : baseEnd_1103288 < baseStart_1103288 := by decide
  rcases family_descends (prefixWord ++ tailWord_1103288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1103350 : List Nat := [5, 1, 1, 1, 2, 4, 1, 6]
def baseStart_1103350 : Nat := 118140960795 + 1103350 * 2 ^ 59
def prefixEnd_1103350 : Nat := 4983230072969 + 3 ^ 40 * 1103350 * 2
def baseEnd_1103350 : Nat := 83933167427905684703821

theorem tailTrace_1103350 : CollatzResearch.WordTrace tailWord_1103350 prefixEnd_1103350 83933167427905684703821 := by
  unfold tailWord_1103350
  simp only [CollatzResearch.WordTrace]
  refine ⟨2515155034547428876428719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 26828320368505908015239669 2515155034547428876428719)
  ·
    refine ⟨3772732551821143314643079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2515155034547428876428719 3772732551821143314643079)
    ·
      refine ⟨5659098827731714971964619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3772732551821143314643079 5659098827731714971964619)
      ·
        refine ⟨8488648241597572457946929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5659098827731714971964619 8488648241597572457946929)
        ·
          refine ⟨6366486181198179343460197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8488648241597572457946929 6366486181198179343460197)
          ·
            refine ⟨1193716158974658626898787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6366486181198179343460197 1193716158974658626898787)
            ·
              refine ⟨1790574238461987940348181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1193716158974658626898787 1790574238461987940348181)
              ·
                refine ⟨83933167427905684703821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1790574238461987940348181 83933167427905684703821)
                ·
                  rfl

theorem cell21_1103350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 4, 1, 6].length) (baseStart_1103350 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1103350 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1103350 prefixEnd_1103350 := by exact prefixLift 1103350
  have htrace : WordTrace (prefixWord ++ tailWord_1103350) baseStart_1103350 baseEnd_1103350 := by
    simpa [prefixWord, tailWord_1103350, baseEnd_1103350] using wordTrace_append hprefix tailTrace_1103350
  have hstable : (prefixWord ++ tailWord_1103350).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1103350).length < 2 ^ (prefixWord ++ tailWord_1103350).sum := by decide
  have hdescent : baseEnd_1103350 < baseStart_1103350 := by decide
  rcases family_descends (prefixWord ++ tailWord_1103350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1103381 : List Nat := [1, 3, 2, 1, 3, 3, 2, 3, 3]
def baseStart_1103381 : Nat := 118140960795 + 1103381 * 2 ^ 59
def prefixEnd_1103381 : Nat := 4983230072969 + 3 ^ 40 * 1103381 * 2
def baseEnd_1103381 : Nat := 251806576906067889094733

theorem tailTrace_1103381 : CollatzResearch.WordTrace tailWord_1103381 prefixEnd_1103381 251806576906067889094733 := by
  unfold tailWord_1103381
  simp only [CollatzResearch.WordTrace]
  refine ⟨40243611215646554317237997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26829074143764369544825331 40243611215646554317237997)
  ·
    refine ⟨15091354205867457868964249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40243611215646554317237997 15091354205867457868964249)
    ·
      refine ⟨11318515654400593401723187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15091354205867457868964249 11318515654400593401723187)
      ·
        refine ⟨16977773481600890102584781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11318515654400593401723187 16977773481600890102584781)
        ·
          refine ⟨6366665055600333788469293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16977773481600890102584781 6366665055600333788469293)
          ·
            refine ⟨2387499395850125170675985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6366665055600333788469293 2387499395850125170675985)
            ·
              refine ⟨1790624546887593878006989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2387499395850125170675985 1790624546887593878006989)
              ·
                refine ⟨671484205082847704252621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1790624546887593878006989 671484205082847704252621)
                ·
                  refine ⟨251806576906067889094733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 671484205082847704252621 251806576906067889094733)
                  ·
                    rfl

theorem cell21_1103381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 3, 2, 3, 3].length) (baseStart_1103381 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1103381 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1103381 prefixEnd_1103381 := by exact prefixLift 1103381
  have htrace : WordTrace (prefixWord ++ tailWord_1103381) baseStart_1103381 baseEnd_1103381 := by
    simpa [prefixWord, tailWord_1103381, baseEnd_1103381] using wordTrace_append hprefix tailTrace_1103381
  have hstable : (prefixWord ++ tailWord_1103381).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1103381).length < 2 ^ (prefixWord ++ tailWord_1103381).sum := by decide
  have hdescent : baseEnd_1103381 < baseStart_1103381 := by decide
  rcases family_descends (prefixWord ++ tailWord_1103381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1103423 : List Nat := [1, 1, 2, 2, 3, 3, 2, 2, 5]
def baseStart_1103423 : Nat := 118140960795 + 1103423 * 2 ^ 59
def prefixEnd_1103423 : Nat := 4983230072969 + 3 ^ 40 * 1103423 * 2
def baseEnd_1103423 : Nat := 251816161878285149394647

theorem tailTrace_1103423 : CollatzResearch.WordTrace tailWord_1103423 prefixEnd_1103423 251816161878285149394647 := by
  unfold tailWord_1103423
  simp only [CollatzResearch.WordTrace]
  refine ⟨40245143081494395490266923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26830095387662930326844615 40245143081494395490266923)
  ·
    refine ⟨60367714622241593235400385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40245143081494395490266923 60367714622241593235400385)
    ·
      refine ⟨45275785966681194926550289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60367714622241593235400385 45275785966681194926550289)
      ·
        refine ⟨33956839475010896194912717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45275785966681194926550289 33956839475010896194912717)
        ·
          refine ⟨12733814803129086073092269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33956839475010896194912717 12733814803129086073092269)
          ·
            refine ⟨4775180551173407277409601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12733814803129086073092269 4775180551173407277409601)
            ·
              refine ⟨3581385413380055458057201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4775180551173407277409601 3581385413380055458057201)
              ·
                refine ⟨2686039060035041593542901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3581385413380055458057201 2686039060035041593542901)
                ·
                  refine ⟨251816161878285149394647, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2686039060035041593542901 251816161878285149394647)
                  ·
                    rfl

theorem cell21_1103423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 2, 2, 5].length) (baseStart_1103423 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1103423 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1103423 prefixEnd_1103423 := by exact prefixLift 1103423
  have htrace : WordTrace (prefixWord ++ tailWord_1103423) baseStart_1103423 baseEnd_1103423 := by
    simpa [prefixWord, tailWord_1103423, baseEnd_1103423] using wordTrace_append hprefix tailTrace_1103423
  have hstable : (prefixWord ++ tailWord_1103423).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1103423).length < 2 ^ (prefixWord ++ tailWord_1103423).sum := by decide
  have hdescent : baseEnd_1103423 < baseStart_1103423 := by decide
  rcases family_descends (prefixWord ++ tailWord_1103423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1103457 : List Nat := [1, 2, 3, 1, 1, 3, 5, 2, 3]
def baseStart_1103457 : Nat := 118140960795 + 1103457 * 2 ^ 59
def prefixEnd_1103457 : Nat := 4983230072969 + 3 ^ 40 * 1103457 * 2
def baseEnd_1103457 : Nat := 251823921141508645827911

theorem tailTrace_1103457 : CollatzResearch.WordTrace tailWord_1103457 prefixEnd_1103457 251823921141508645827911 := by
  unfold tailWord_1103457
  simp only [CollatzResearch.WordTrace]
  refine ⟨40246383163371219297004625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26830922108914146198003083 40246383163371219297004625)
  ·
    refine ⟨30184787372528414472753469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40246383163371219297004625 30184787372528414472753469)
    ·
      refine ⟨11319295264698155427282551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30184787372528414472753469 11319295264698155427282551)
      ·
        refine ⟨16978942897047233140923827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11319295264698155427282551 16978942897047233140923827)
        ·
          refine ⟨25468414345570849711385741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16978942897047233140923827 25468414345570849711385741)
          ·
            refine ⟨9550655379589068641769653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25468414345570849711385741 9550655379589068641769653)
            ·
              refine ⟨895373941836475185165905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 9550655379589068641769653 895373941836475185165905)
              ·
                refine ⟨671530456377356388874429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 895373941836475185165905 671530456377356388874429)
                ·
                  refine ⟨251823921141508645827911, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 671530456377356388874429 251823921141508645827911)
                  ·
                    rfl

theorem cell21_1103457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 5, 2, 3].length) (baseStart_1103457 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1103457 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1103457 prefixEnd_1103457 := by exact prefixLift 1103457
  have htrace : WordTrace (prefixWord ++ tailWord_1103457) baseStart_1103457 baseEnd_1103457 := by
    simpa [prefixWord, tailWord_1103457, baseEnd_1103457] using wordTrace_append hprefix tailTrace_1103457
  have hstable : (prefixWord ++ tailWord_1103457).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1103457).length < 2 ^ (prefixWord ++ tailWord_1103457).sum := by decide
  have hdescent : baseEnd_1103457 < baseStart_1103457 := by decide
  rcases family_descends (prefixWord ++ tailWord_1103457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1103508 : List Nat := [2, 4, 2, 2, 3, 1, 2, 2, 3]
def baseStart_1103508 : Nat := 118140960795 + 1103508 * 2 ^ 59
def prefixEnd_1103508 : Nat := 4983230072969 + 3 ^ 40 * 1103508 * 2
def baseEnd_1103508 : Nat := 251835560036343890477807

theorem tailTrace_1103508 : CollatzResearch.WordTrace tailWord_1103508 prefixEnd_1103508 251835560036343890477807 := by
  unfold tailWord_1103508
  simp only [CollatzResearch.WordTrace]
  refine ⟨20124121643093227503555589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26832162190790970004740785 20124121643093227503555589)
  ·
    refine ⟨3773272808079980156916673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 20124121643093227503555589 3773272808079980156916673)
    ·
      refine ⟨2829954606059985117687505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3773272808079980156916673 2829954606059985117687505)
      ·
        refine ⟨2122465954544988838265629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2829954606059985117687505 2122465954544988838265629)
        ·
          refine ⟨795924732954370814349611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2122465954544988838265629 795924732954370814349611)
          ·
            refine ⟨1193887099431556221524417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 795924732954370814349611 1193887099431556221524417)
            ·
              refine ⟨895415324573667166143313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1193887099431556221524417 895415324573667166143313)
              ·
                refine ⟨671561493430250374607485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 895415324573667166143313 671561493430250374607485)
                ·
                  refine ⟨251835560036343890477807, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 671561493430250374607485 251835560036343890477807)
                  ·
                    rfl

theorem cell21_1103508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 3, 1, 2, 2, 3].length) (baseStart_1103508 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1103508 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1103508 prefixEnd_1103508 := by exact prefixLift 1103508
  have htrace : WordTrace (prefixWord ++ tailWord_1103508) baseStart_1103508 baseEnd_1103508 := by
    simpa [prefixWord, tailWord_1103508, baseEnd_1103508] using wordTrace_append hprefix tailTrace_1103508
  have hstable : (prefixWord ++ tailWord_1103508).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1103508).length < 2 ^ (prefixWord ++ tailWord_1103508).sum := by decide
  have hdescent : baseEnd_1103508 < baseStart_1103508 := by decide
  rcases family_descends (prefixWord ++ tailWord_1103508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1103519 : List Nat := [1, 1, 2, 7, 2, 1, 1, 6]
def baseStart_1103519 : Nat := 118140960795 + 1103519 * 2 ^ 59
def prefixEnd_1103519 : Nat := 4983230072969 + 3 ^ 40 * 1103519 * 2
def baseEnd_1103519 : Nat := 83946023462070105264817

theorem tailTrace_1103519 : CollatzResearch.WordTrace tailWord_1103519 prefixEnd_1103519 83946023462070105264817 := by
  unfold tailWord_1103519
  simp only [CollatzResearch.WordTrace]
  refine ⟨40248644489146603885761611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26832429659431069257174407 40248644489146603885761611)
  ·
    refine ⟨60372966733719905828642417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40248644489146603885761611 60372966733719905828642417)
    ·
      refine ⟨45279725050289929371481813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60372966733719905828642417 45279725050289929371481813)
      ·
        refine ⟨1061243555866170219644105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 45279725050289929371481813 1061243555866170219644105)
        ·
          refine ⟨795932666899627664733079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1061243555866170219644105 795932666899627664733079)
          ·
            refine ⟨1193899000349441497099619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 795932666899627664733079 1193899000349441497099619)
            ·
              refine ⟨1790848500524162245649429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1193899000349441497099619 1790848500524162245649429)
              ·
                refine ⟨83946023462070105264817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1790848500524162245649429 83946023462070105264817)
                ·
                  rfl

theorem cell21_1103519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 2, 1, 1, 6].length) (baseStart_1103519 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1103519 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1103519 prefixEnd_1103519 := by exact prefixLift 1103519
  have htrace : WordTrace (prefixWord ++ tailWord_1103519) baseStart_1103519 baseEnd_1103519 := by
    simpa [prefixWord, tailWord_1103519, baseEnd_1103519] using wordTrace_append hprefix tailTrace_1103519
  have hstable : (prefixWord ++ tailWord_1103519).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1103519).length < 2 ^ (prefixWord ++ tailWord_1103519).sum := by decide
  have hdescent : baseEnd_1103519 < baseStart_1103519 := by decide
  rcases family_descends (prefixWord ++ tailWord_1103519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1103564 : List Nat := [2, 2, 1, 5, 2, 2, 1, 2, 4]
def baseStart_1103564 : Nat := 118140960795 + 1103564 * 2 ^ 59
def prefixEnd_1103564 : Nat := 4983230072969 + 3 ^ 40 * 1103564 * 2
def baseEnd_1103564 : Nat := 251848339999300237544359

theorem tailTrace_1103564 : CollatzResearch.WordTrace tailWord_1103564 prefixEnd_1103564 251848339999300237544359 := by
  unfold tailWord_1103564
  simp only [CollatzResearch.WordTrace]
  refine ⟨20125142886991788285574873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26833523849322384380766497 20125142886991788285574873)
  ·
    refine ⟨15093857165243841214181155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20125142886991788285574873 15093857165243841214181155)
    ·
      refine ⟨22640785747865761821271733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15093857165243841214181155 22640785747865761821271733)
      ·
        refine ⟨2122573663862415170744225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 22640785747865761821271733 2122573663862415170744225)
        ·
          refine ⟨1591930247896811378058169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2122573663862415170744225 1591930247896811378058169)
          ·
            refine ⟨1193947685922608533543627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1591930247896811378058169 1193947685922608533543627)
            ·
              refine ⟨1790921528883912800315441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1193947685922608533543627 1790921528883912800315441)
              ·
                refine ⟨1343191146662934600236581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1790921528883912800315441 1343191146662934600236581)
                ·
                  refine ⟨251848339999300237544359, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1343191146662934600236581 251848339999300237544359)
                  ·
                    rfl

theorem cell21_1103564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 2, 1, 2, 4].length) (baseStart_1103564 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1103564 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1103564 prefixEnd_1103564 := by exact prefixLift 1103564
  have htrace : WordTrace (prefixWord ++ tailWord_1103564) baseStart_1103564 baseEnd_1103564 := by
    simpa [prefixWord, tailWord_1103564, baseEnd_1103564] using wordTrace_append hprefix tailTrace_1103564
  have hstable : (prefixWord ++ tailWord_1103564).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1103564).length < 2 ^ (prefixWord ++ tailWord_1103564).sum := by decide
  have hdescent : baseEnd_1103564 < baseStart_1103564 := by decide
  rcases family_descends (prefixWord ++ tailWord_1103564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1103575 : List Nat := [1, 1, 3, 2, 1, 3, 4, 1, 5]
def baseStart_1103575 : Nat := 118140960795 + 1103575 * 2 ^ 59
def prefixEnd_1103575 : Nat := 4983230072969 + 3 ^ 40 * 1103575 * 2
def baseEnd_1103575 : Nat := 251850850349166662861003

theorem tailTrace_1103575 : CollatzResearch.WordTrace tailWord_1103575 prefixEnd_1103575 251850850349166662861003 := by
  unfold tailWord_1103575
  simp only [CollatzResearch.WordTrace]
  refine ⟨40250686976943725449800179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26833791317962483633200119 40250686976943725449800179)
  ·
    refine ⟨60376030465415588174700269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40250686976943725449800179 60376030465415588174700269)
    ·
      refine ⟨22641011424530845565512601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 60376030465415588174700269 22641011424530845565512601)
      ·
        refine ⟨16980758568398134174134451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22641011424530845565512601 16980758568398134174134451)
        ·
          refine ⟨25471137852597201261201677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16980758568398134174134451 25471137852597201261201677)
          ·
            refine ⟨9551676694723950472950629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25471137852597201261201677 9551676694723950472950629)
            ·
              refine ⟨1790939380260740713678243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9551676694723950472950629 1790939380260740713678243)
              ·
                refine ⟨2686409070391111070517365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1790939380260740713678243 2686409070391111070517365)
                ·
                  refine ⟨251850850349166662861003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2686409070391111070517365 251850850349166662861003)
                  ·
                    rfl

theorem cell21_1103575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 4, 1, 5].length) (baseStart_1103575 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1103575 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1103575 prefixEnd_1103575 := by exact prefixLift 1103575
  have htrace : WordTrace (prefixWord ++ tailWord_1103575) baseStart_1103575 baseEnd_1103575 := by
    simpa [prefixWord, tailWord_1103575, baseEnd_1103575] using wordTrace_append hprefix tailTrace_1103575
  have hstable : (prefixWord ++ tailWord_1103575).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1103575).length < 2 ^ (prefixWord ++ tailWord_1103575).sum := by decide
  have hdescent : baseEnd_1103575 < baseStart_1103575 := by decide
  rcases family_descends (prefixWord ++ tailWord_1103575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1103581 : List Nat := [1, 4, 3, 3, 1, 1, 3, 1, 4]
def baseStart_1103581 : Nat := 118140960795 + 1103581 * 2 ^ 59
def prefixEnd_1103581 : Nat := 4983230072969 + 3 ^ 40 * 1103581 * 2
def baseEnd_1103581 : Nat := 251852219630911985760991

theorem tailTrace_1103581 : CollatzResearch.WordTrace tailWord_1103581 prefixEnd_1103581 251852219630911985760991 := by
  unfold tailWord_1103581
  simp only [CollatzResearch.WordTrace]
  refine ⟨40250905814921988474518597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26833937209947992316345731 40250905814921988474518597)
  ·
    refine ⟨7547044840297872838972237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 40250905814921988474518597 7547044840297872838972237)
    ·
      refine ⟨2830141815111702314614589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7547044840297872838972237 2830141815111702314614589)
      ·
        refine ⟨1061303180666888367980471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2830141815111702314614589 1061303180666888367980471)
        ·
          refine ⟨1591954771000332551970707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1061303180666888367980471 1591954771000332551970707)
          ·
            refine ⟨2387932156500498827956061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1591954771000332551970707 2387932156500498827956061)
            ·
              refine ⟨895474558687687060483523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2387932156500498827956061 895474558687687060483523)
              ·
                refine ⟨1343211838031530590725285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 895474558687687060483523 1343211838031530590725285)
                ·
                  refine ⟨251852219630911985760991, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1343211838031530590725285 251852219630911985760991)
                  ·
                    rfl

theorem cell21_1103581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 1, 3, 1, 4].length) (baseStart_1103581 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1103581 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1103581 prefixEnd_1103581 := by exact prefixLift 1103581
  have htrace : WordTrace (prefixWord ++ tailWord_1103581) baseStart_1103581 baseEnd_1103581 := by
    simpa [prefixWord, tailWord_1103581, baseEnd_1103581] using wordTrace_append hprefix tailTrace_1103581
  have hstable : (prefixWord ++ tailWord_1103581).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1103581).length < 2 ^ (prefixWord ++ tailWord_1103581).sum := by decide
  have hdescent : baseEnd_1103581 < baseStart_1103581 := by decide
  rcases family_descends (prefixWord ++ tailWord_1103581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1103606 : List Nat := [5, 1, 1, 1, 1, 3, 1, 2, 6]
def baseStart_1103606 : Nat := 118140960795 + 1103606 * 2 ^ 59
def prefixEnd_1103606 : Nat := 4983230072969 + 3 ^ 40 * 1103606 * 2
def baseEnd_1103606 : Nat := 251857924971517497844273

theorem tailTrace_1103606 : CollatzResearch.WordTrace tailWord_1103606 prefixEnd_1103606 251857924971517497844273 := by
  unfold tailWord_1103606
  simp only [CollatzResearch.WordTrace]
  refine ⟨2515738602489463609011167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 26834545093220945162785781 2515738602489463609011167)
  ·
    refine ⟨3773607903734195413516751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2515738602489463609011167 3773607903734195413516751)
    ·
      refine ⟨5660411855601293120275127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3773607903734195413516751 5660411855601293120275127)
      ·
        refine ⟨8490617783401939680412691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5660411855601293120275127 8490617783401939680412691)
        ·
          refine ⟨12735926675102909520619037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8490617783401939680412691 12735926675102909520619037)
          ·
            refine ⟨4775972503163591070232139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12735926675102909520619037 4775972503163591070232139)
            ·
              refine ⟨7163958754745386605348209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4775972503163591070232139 7163958754745386605348209)
              ·
                refine ⟨5372969066059039954011157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7163958754745386605348209 5372969066059039954011157)
                ·
                  refine ⟨251857924971517497844273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5372969066059039954011157 251857924971517497844273)
                  ·
                    rfl

theorem cell21_1103606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 1, 2, 6].length) (baseStart_1103606 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1103606 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1103606 prefixEnd_1103606 := by exact prefixLift 1103606
  have htrace : WordTrace (prefixWord ++ tailWord_1103606) baseStart_1103606 baseEnd_1103606 := by
    simpa [prefixWord, tailWord_1103606, baseEnd_1103606] using wordTrace_append hprefix tailTrace_1103606
  have hstable : (prefixWord ++ tailWord_1103606).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1103606).length < 2 ^ (prefixWord ++ tailWord_1103606).sum := by decide
  have hdescent : baseEnd_1103606 < baseStart_1103606 := by decide
  rcases family_descends (prefixWord ++ tailWord_1103606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1103620 : List Nat := [2, 3, 2, 2, 1, 2, 9]
def baseStart_1103620 : Nat := 118140960795 + 1103620 * 2 ^ 59
def prefixEnd_1103620 : Nat := 4983230072969 + 3 ^ 40 * 1103620 * 2
def baseEnd_1103620 : Nat := 27984568884695176067879

theorem tailTrace_1103620 : CollatzResearch.WordTrace tailWord_1103620 prefixEnd_1103620 27984568884695176067879 := by
  unfold tailWord_1103620
  simp only [CollatzResearch.WordTrace]
  refine ⟨20126164130890349067594157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26834885507853798756792209 20126164130890349067594157)
  ·
    refine ⟨7547311549083880900347809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20126164130890349067594157 7547311549083880900347809)
    ·
      refine ⟨5660483661812910675260857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7547311549083880900347809 5660483661812910675260857)
      ·
        refine ⟨4245362746359683006445643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5660483661812910675260857 4245362746359683006445643)
        ·
          refine ⟨6368044119539524509668465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4245362746359683006445643 6368044119539524509668465)
          ·
            refine ⟨4776033089654643382251349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6368044119539524509668465 4776033089654643382251349)
            ·
              refine ⟨27984568884695176067879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 4776033089654643382251349 27984568884695176067879)
              ·
                rfl

theorem cell21_1103620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 9].length) (baseStart_1103620 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1103620 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1103620 prefixEnd_1103620 := by exact prefixLift 1103620
  have htrace : WordTrace (prefixWord ++ tailWord_1103620) baseStart_1103620 baseEnd_1103620 := by
    simpa [prefixWord, tailWord_1103620, baseEnd_1103620] using wordTrace_append hprefix tailTrace_1103620
  have hstable : (prefixWord ++ tailWord_1103620).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1103620).length < 2 ^ (prefixWord ++ tailWord_1103620).sum := by decide
  have hdescent : baseEnd_1103620 < baseStart_1103620 := by decide
  rcases family_descends (prefixWord ++ tailWord_1103620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1103679 : List Nat := [1, 1, 2, 2, 15]
def baseStart_1103679 : Nat := 118140960795 + 1103679 * 2 ^ 59
def prefixEnd_1103679 : Nat := 4983230072969 + 3 ^ 40 * 1103679 * 2
def baseEnd_1103679 : Nat := 3109562772420809791697

theorem tailTrace_1103679 : CollatzResearch.WordTrace tailWord_1103679 prefixEnd_1103679 3109562772420809791697 := by
  unfold tailWord_1103679
  simp only [CollatzResearch.WordTrace]
  refine ⟨40254480168566951211586091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26836320112377967474390727 40254480168566951211586091)
  ·
    refine ⟨60381720252850426817379137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40254480168566951211586091 60381720252850426817379137)
    ·
      refine ⟨45286290189637820113034353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60381720252850426817379137 45286290189637820113034353)
      ·
        refine ⟨33964717642228365084775765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45286290189637820113034353 33964717642228365084775765)
        ·
          refine ⟨3109562772420809791697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 15 33964717642228365084775765 3109562772420809791697)
          ·
            rfl

theorem cell21_1103679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 15].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 15].length) (baseStart_1103679 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1103679 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1103679 prefixEnd_1103679 := by exact prefixLift 1103679
  have htrace : WordTrace (prefixWord ++ tailWord_1103679) baseStart_1103679 baseEnd_1103679 := by
    simpa [prefixWord, tailWord_1103679, baseEnd_1103679] using wordTrace_append hprefix tailTrace_1103679
  have hstable : (prefixWord ++ tailWord_1103679).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1103679).length < 2 ^ (prefixWord ++ tailWord_1103679).sum := by decide
  have hdescent : baseEnd_1103679 < baseStart_1103679 := by decide
  rcases family_descends (prefixWord ++ tailWord_1103679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1103755 : List Nat := [1, 1, 1, 1, 4, 2, 1, 10]
def baseStart_1103755 : Nat := 118140960795 + 1103755 * 2 ^ 59
def prefixEnd_1103755 : Nat := 4983230072969 + 3 ^ 40 * 1103755 * 2
def baseEnd_1103755 : Nat := 83963976267175449953545

theorem tailTrace_1103755 : CollatzResearch.WordTrace tailWord_1103755 prefixEnd_1103755 83963976267175449953545 := by
  unfold tailWord_1103755
  simp only [CollatzResearch.WordTrace]
  refine ⟨40257252116291616191352719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26838168077527744127568479 40257252116291616191352719)
  ·
    refine ⟨60385878174437424287029079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40257252116291616191352719 60385878174437424287029079)
    ·
      refine ⟨90578817261656136430543619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60385878174437424287029079 90578817261656136430543619)
      ·
        refine ⟨135868225892484204645815429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90578817261656136430543619 135868225892484204645815429)
        ·
          refine ⟨25475292354840788371090393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 135868225892484204645815429 25475292354840788371090393)
          ·
            refine ⟨19106469266130591278317795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25475292354840788371090393 19106469266130591278317795)
            ·
              refine ⟨28659703899195886917476693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19106469266130591278317795 28659703899195886917476693)
              ·
                refine ⟨83963976267175449953545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 28659703899195886917476693 83963976267175449953545)
                ·
                  rfl

theorem cell21_1103755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 10].length) (baseStart_1103755 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1103755 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1103755 prefixEnd_1103755 := by exact prefixLift 1103755
  have htrace : WordTrace (prefixWord ++ tailWord_1103755) baseStart_1103755 baseEnd_1103755 := by
    simpa [prefixWord, tailWord_1103755, baseEnd_1103755] using wordTrace_append hprefix tailTrace_1103755
  have hstable : (prefixWord ++ tailWord_1103755).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1103755).length < 2 ^ (prefixWord ++ tailWord_1103755).sum := by decide
  have hdescent : baseEnd_1103755 < baseStart_1103755 := by decide
  rcases family_descends (prefixWord ++ tailWord_1103755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1103778 : List Nat := [3, 3, 1, 2, 3, 2, 1, 3, 3]
def baseStart_1103778 : Nat := 118140960795 + 1103778 * 2 ^ 59
def prefixEnd_1103778 : Nat := 4983230072969 + 3 ^ 40 * 1103778 * 2
def baseEnd_1103778 : Nat := 251897177714883420977255

theorem tailTrace_1103778 : CollatzResearch.WordTrace tailWord_1103778 prefixEnd_1103778 251897177714883420977255 := by
  unfold tailWord_1103778
  simp only [CollatzResearch.WordTrace]
  refine ⟨10064522748802072779859997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26838727330138860746293325 10064522748802072779859997)
  ·
    refine ⟨3774196030800777292447499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10064522748802072779859997 3774196030800777292447499)
    ·
      refine ⟨5661294046201165938671249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3774196030800777292447499 5661294046201165938671249)
      ·
        refine ⟨4245970534650874454003437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5661294046201165938671249 4245970534650874454003437)
        ·
          refine ⟨1592238950494077920251289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4245970534650874454003437 1592238950494077920251289)
          ·
            refine ⟨1194179212870558440188467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1592238950494077920251289 1194179212870558440188467)
            ·
              refine ⟨1791268819305837660282701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1194179212870558440188467 1791268819305837660282701)
              ·
                refine ⟨671725807239689122606013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1791268819305837660282701 671725807239689122606013)
                ·
                  refine ⟨251897177714883420977255, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 671725807239689122606013 251897177714883420977255)
                  ·
                    rfl

theorem cell21_1103778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 2, 1, 3, 3].length) (baseStart_1103778 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1103778 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1103778 prefixEnd_1103778 := by exact prefixLift 1103778
  have htrace : WordTrace (prefixWord ++ tailWord_1103778) baseStart_1103778 baseEnd_1103778 := by
    simpa [prefixWord, tailWord_1103778, baseEnd_1103778] using wordTrace_append hprefix tailTrace_1103778
  have hstable : (prefixWord ++ tailWord_1103778).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1103778).length < 2 ^ (prefixWord ++ tailWord_1103778).sum := by decide
  have hdescent : baseEnd_1103778 < baseStart_1103778 := by decide
  rcases family_descends (prefixWord ++ tailWord_1103778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1103817 : List Nat := [1, 2, 1, 1, 2, 1, 2, 7, 4]
def baseStart_1103817 : Nat := 118140960795 + 1103817 * 2 ^ 59
def prefixEnd_1103817 : Nat := 4983230072969 + 3 ^ 40 * 1103817 * 2
def baseEnd_1103817 : Nat := 251906078046228019827175

theorem tailTrace_1103817 : CollatzResearch.WordTrace tailWord_1103817 prefixEnd_1103817 251906078046228019827175 := by
  unfold tailWord_1103817
  simp only [CollatzResearch.WordTrace]
  refine ⟨40259513442067000780109705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26839675628044667186739803 40259513442067000780109705)
  ·
    refine ⟨30194635081550250585082279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40259513442067000780109705 30194635081550250585082279)
    ·
      refine ⟨45291952622325375877623419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30194635081550250585082279 45291952622325375877623419)
      ·
        refine ⟨67937928933488063816435129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45291952622325375877623419 67937928933488063816435129)
        ·
          refine ⟨50953446700116047862326347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 67937928933488063816435129 50953446700116047862326347)
          ·
            refine ⟨76430170050174071793489521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50953446700116047862326347 76430170050174071793489521)
            ·
              refine ⟨57322627537630553845117141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 76430170050174071793489521 57322627537630553845117141)
              ·
                refine ⟨1343499082913216105744933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 57322627537630553845117141 1343499082913216105744933)
                ·
                  refine ⟨251906078046228019827175, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1343499082913216105744933 251906078046228019827175)
                  ·
                    rfl

theorem cell21_1103817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 7, 4].length) (baseStart_1103817 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1103817 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1103817 prefixEnd_1103817 := by exact prefixLift 1103817
  have htrace : WordTrace (prefixWord ++ tailWord_1103817) baseStart_1103817 baseEnd_1103817 := by
    simpa [prefixWord, tailWord_1103817, baseEnd_1103817] using wordTrace_append hprefix tailTrace_1103817
  have hstable : (prefixWord ++ tailWord_1103817).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1103817).length < 2 ^ (prefixWord ++ tailWord_1103817).sum := by decide
  have hdescent : baseEnd_1103817 < baseStart_1103817 := by decide
  rcases family_descends (prefixWord ++ tailWord_1103817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1103831 : List Nat := [1, 1, 3, 2, 1, 1, 3, 9]
def baseStart_1103831 : Nat := 118140960795 + 1103831 * 2 ^ 59
def prefixEnd_1103831 : Nat := 4983230072969 + 3 ^ 40 * 1103831 * 2
def baseEnd_1103831 : Nat := 83969757678989035531271

theorem tailTrace_1103831 : CollatzResearch.WordTrace tailWord_1103831 prefixEnd_1103831 83969757678989035531271 := by
  unfold tailWord_1103831
  simp only [CollatzResearch.WordTrace]
  refine ⟨40260024064016281171119347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26840016042677520780746231 40260024064016281171119347)
  ·
    refine ⟨60390036096024421756679021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40260024064016281171119347 60390036096024421756679021)
    ·
      refine ⟨22646263536009158158754633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 60390036096024421756679021 22646263536009158158754633)
      ·
        refine ⟨16984697652006868619065975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22646263536009158158754633 16984697652006868619065975)
        ·
          refine ⟨25477046478010302928598963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16984697652006868619065975 25477046478010302928598963)
          ·
            refine ⟨38215569717015454392898445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25477046478010302928598963 38215569717015454392898445)
            ·
              refine ⟨14330838643880795397336917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 38215569717015454392898445 14330838643880795397336917)
              ·
                refine ⟨83969757678989035531271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 14330838643880795397336917 83969757678989035531271)
                ·
                  rfl

theorem cell21_1103831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 3, 9].length) (baseStart_1103831 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1103831 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1103831 prefixEnd_1103831 := by exact prefixLift 1103831
  have htrace : WordTrace (prefixWord ++ tailWord_1103831) baseStart_1103831 baseEnd_1103831 := by
    simpa [prefixWord, tailWord_1103831, baseEnd_1103831] using wordTrace_append hprefix tailTrace_1103831
  have hstable : (prefixWord ++ tailWord_1103831).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1103831).length < 2 ^ (prefixWord ++ tailWord_1103831).sum := by decide
  have hdescent : baseEnd_1103831 < baseStart_1103831 := by decide
  rcases family_descends (prefixWord ++ tailWord_1103831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1103854 : List Nat := [4, 1, 2, 1, 3, 3, 2, 2, 3]
def baseStart_1103854 : Nat := 118140960795 + 1103854 * 2 ^ 59
def prefixEnd_1103854 : Nat := 4983230072969 + 3 ^ 40 * 1103854 * 2
def baseEnd_1103854 : Nat := 251914521950324177710433

theorem tailTrace_1103854 : CollatzResearch.WordTrace tailWord_1103854 prefixEnd_1103854 251914521950324177710433 := by
  unfold tailWord_1103854
  simp only [CollatzResearch.WordTrace]
  refine ⟨5032607867866619512400827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 26840575295288637399471077 5032607867866619512400827)
  ·
    refine ⟨7548911801799929268601241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5032607867866619512400827 7548911801799929268601241)
    ·
      refine ⟨5661683851349946951450931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7548911801799929268601241 5661683851349946951450931)
      ·
        refine ⟨8492525777024920427176397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5661683851349946951450931 8492525777024920427176397)
        ·
          refine ⟨3184697166384345160191149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8492525777024920427176397 3184697166384345160191149)
          ·
            refine ⟨1194261437394129435071681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3184697166384345160191149 1194261437394129435071681)
            ·
              refine ⟨895696078045597076303761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1194261437394129435071681 895696078045597076303761)
              ·
                refine ⟨671772058534197807227821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 895696078045597076303761 671772058534197807227821)
                ·
                  refine ⟨251914521950324177710433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 671772058534197807227821 251914521950324177710433)
                  ·
                    rfl

theorem cell21_1103854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 3, 2, 2, 3].length) (baseStart_1103854 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1103854 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1103854 prefixEnd_1103854 := by exact prefixLift 1103854
  have htrace : WordTrace (prefixWord ++ tailWord_1103854) baseStart_1103854 baseEnd_1103854 := by
    simpa [prefixWord, tailWord_1103854, baseEnd_1103854] using wordTrace_append hprefix tailTrace_1103854
  have hstable : (prefixWord ++ tailWord_1103854).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1103854).length < 2 ^ (prefixWord ++ tailWord_1103854).sum := by decide
  have hdescent : baseEnd_1103854 < baseStart_1103854 := by decide
  rcases family_descends (prefixWord ++ tailWord_1103854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1103879 : List Nat := [1, 1, 4, 3, 1, 3, 1, 2, 5]
def baseStart_1103879 : Nat := 118140960795 + 1103879 * 2 ^ 59
def prefixEnd_1103879 : Nat := 4983230072969 + 3 ^ 40 * 1103879 * 2
def baseEnd_1103879 : Nat := 251920227290929689793715

theorem tailTrace_1103879 : CollatzResearch.WordTrace tailWord_1103879 prefixEnd_1103879 251920227290929689793715 := by
  unfold tailWord_1103879
  simp only [CollatzResearch.WordTrace]
  refine ⟨40261774767842385368866691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26841183178561590245911127 40261774767842385368866691)
  ·
    refine ⟨60392662151763578053300037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40261774767842385368866691 60392662151763578053300037)
    ·
      refine ⟨11323624153455670884993757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 60392662151763578053300037 11323624153455670884993757)
      ·
        refine ⟨4246359057545876581872659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11323624153455670884993757 4246359057545876581872659)
        ·
          refine ⟨6369538586318814872808989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4246359057545876581872659 6369538586318814872808989)
          ·
            refine ⟨2388576969869555577303371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6369538586318814872808989 2388576969869555577303371)
            ·
              refine ⟨3582865454804333365955057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2388576969869555577303371 3582865454804333365955057)
              ·
                refine ⟨2687149091103250024466293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3582865454804333365955057 2687149091103250024466293)
                ·
                  refine ⟨251920227290929689793715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2687149091103250024466293 251920227290929689793715)
                  ·
                    rfl

theorem cell21_1103879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 3, 1, 2, 5].length) (baseStart_1103879 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1103879 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1103879 prefixEnd_1103879 := by exact prefixLift 1103879
  have htrace : WordTrace (prefixWord ++ tailWord_1103879) baseStart_1103879 baseEnd_1103879 := by
    simpa [prefixWord, tailWord_1103879, baseEnd_1103879] using wordTrace_append hprefix tailTrace_1103879
  have hstable : (prefixWord ++ tailWord_1103879).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1103879).length < 2 ^ (prefixWord ++ tailWord_1103879).sum := by decide
  have hdescent : baseEnd_1103879 < baseStart_1103879 := by decide
  rcases family_descends (prefixWord ++ tailWord_1103879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1103896 : List Nat := [2, 1, 2, 3, 2, 1, 4, 3, 3]
def baseStart_1103896 : Nat := 118140960795 + 1103896 * 2 ^ 59
def prefixEnd_1103896 : Nat := 4983230072969 + 3 ^ 40 * 1103896 * 2
def baseEnd_1103896 : Nat := 251924106922541438010347

theorem tailTrace_1103896 : CollatzResearch.WordTrace tailWord_1103896 prefixEnd_1103896 251924106922541438010347 := by
  unfold tailWord_1103896
  simp only [CollatzResearch.WordTrace]
  refine ⟨20131197404390398636117771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26841596539187198181490361 20131197404390398636117771)
  ·
    refine ⟨30196796106585597954176657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20131197404390398636117771 30196796106585597954176657)
    ·
      refine ⟨22647597079939198465632493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30196796106585597954176657 22647597079939198465632493)
      ·
        refine ⟨8492848904977199424612185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22647597079939198465632493 8492848904977199424612185)
        ·
          refine ⟨6369636678732899568459139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8492848904977199424612185 6369636678732899568459139)
          ·
            refine ⟨9554455018099349352688709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6369636678732899568459139 9554455018099349352688709)
            ·
              refine ⟨1791460315893628003629133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9554455018099349352688709 1791460315893628003629133)
              ·
                refine ⟨671797618460110501360925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1791460315893628003629133 671797618460110501360925)
                ·
                  refine ⟨251924106922541438010347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 671797618460110501360925 251924106922541438010347)
                  ·
                    rfl

theorem cell21_1103896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 4, 3, 3].length) (baseStart_1103896 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1103896 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1103896 prefixEnd_1103896 := by exact prefixLift 1103896
  have htrace : WordTrace (prefixWord ++ tailWord_1103896) baseStart_1103896 baseEnd_1103896 := by
    simpa [prefixWord, tailWord_1103896, baseEnd_1103896] using wordTrace_append hprefix tailTrace_1103896
  have hstable : (prefixWord ++ tailWord_1103896).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1103896).length < 2 ^ (prefixWord ++ tailWord_1103896).sum := by decide
  have hdescent : baseEnd_1103896 < baseStart_1103896 := by decide
  rcases family_descends (prefixWord ++ tailWord_1103896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1103907 : List Nat := [1, 1, 1, 4, 3, 1, 10]
def baseStart_1103907 : Nat := 118140960795 + 1103907 * 2 ^ 59
def prefixEnd_1103907 : Nat := 4983230072969 + 3 ^ 40 * 1103907 * 2
def baseEnd_1103907 : Nat := 27991846363600873702999

theorem tailTrace_1103907 : CollatzResearch.WordTrace tailWord_1103907 prefixEnd_1103907 27991846363600873702999 := by
  unfold tailWord_1103907
  simp only [CollatzResearch.WordTrace]
  refine ⟨40262796011740946150885975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26841864007827297433923983 40262796011740946150885975)
  ·
    refine ⟨60394194017611419226328963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40262796011740946150885975 60394194017611419226328963)
    ·
      refine ⟨90591291026417128839493445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60394194017611419226328963 90591291026417128839493445)
      ·
        refine ⟨16985867067453211657405021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 90591291026417128839493445 16985867067453211657405021)
        ·
          refine ⟨6369700150294954371526883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16985867067453211657405021 6369700150294954371526883)
          ·
            refine ⟨9554550225442431557290325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6369700150294954371526883 9554550225442431557290325)
            ·
              refine ⟨27991846363600873702999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 9554550225442431557290325 27991846363600873702999)
              ·
                rfl

theorem cell21_1103907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 10].length) (baseStart_1103907 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1103907 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1103907 prefixEnd_1103907 := by exact prefixLift 1103907
  have htrace : WordTrace (prefixWord ++ tailWord_1103907) baseStart_1103907 baseEnd_1103907 := by
    simpa [prefixWord, tailWord_1103907, baseEnd_1103907] using wordTrace_append hprefix tailTrace_1103907
  have hstable : (prefixWord ++ tailWord_1103907).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1103907).length < 2 ^ (prefixWord ++ tailWord_1103907).sum := by decide
  have hdescent : baseEnd_1103907 < baseStart_1103907 := by decide
  rcases family_descends (prefixWord ++ tailWord_1103907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1103958 : List Nat := [5, 2, 2, 1, 1, 3, 7]
def baseStart_1103958 : Nat := 118140960795 + 1103958 * 2 ^ 59
def prefixEnd_1103958 : Nat := 4983230072969 + 3 ^ 40 * 1103958 * 2
def baseEnd_1103958 : Nat := 27993139574138123108543

theorem tailTrace_1103958 : CollatzResearch.WordTrace tailWord_1103958 prefixEnd_1103958 27993139574138123108543 := by
  unfold tailWord_1103958
  simp only [CollatzResearch.WordTrace]
  refine ⟨2516541008409761366312033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 26843104089704121240661685 2516541008409761366312033)
  ·
    refine ⟨1887405756307321024734025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2516541008409761366312033 1887405756307321024734025)
    ·
      refine ⟨1415554317230490768550519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1887405756307321024734025 1415554317230490768550519)
      ·
        refine ⟨2123331475845736152825779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1415554317230490768550519 2123331475845736152825779)
        ·
          refine ⟨3184997213768604229238669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2123331475845736152825779 3184997213768604229238669)
          ·
            refine ⟨1194373955163226585964501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3184997213768604229238669 1194373955163226585964501)
            ·
              refine ⟨27993139574138123108543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1194373955163226585964501 27993139574138123108543)
              ·
                rfl

theorem cell21_1103958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 3, 7].length) (baseStart_1103958 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1103958 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1103958 prefixEnd_1103958 := by exact prefixLift 1103958
  have htrace : WordTrace (prefixWord ++ tailWord_1103958) baseStart_1103958 baseEnd_1103958 := by
    simpa [prefixWord, tailWord_1103958, baseEnd_1103958] using wordTrace_append hprefix tailTrace_1103958
  have hstable : (prefixWord ++ tailWord_1103958).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1103958).length < 2 ^ (prefixWord ++ tailWord_1103958).sum := by decide
  have hdescent : baseEnd_1103958 < baseStart_1103958 := by decide
  rcases family_descends (prefixWord ++ tailWord_1103958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1103969 : List Nat := [1, 2, 3, 1, 1, 2, 1, 6, 4]
def baseStart_1103969 : Nat := 118140960795 + 1103969 * 2 ^ 59
def prefixEnd_1103969 : Nat := 4983230072969 + 3 ^ 40 * 1103969 * 2
def baseEnd_1103969 : Nat := 251940766517109533293531

theorem tailTrace_1103969 : CollatzResearch.WordTrace tailWord_1103969 prefixEnd_1103969 251940766517109533293531 := by
  unfold tailWord_1103969
  simp only [CollatzResearch.WordTrace]
  refine ⟨40265057337516330739642961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26843371558344220493095307 40265057337516330739642961)
  ·
    refine ⟨30198793003137248054732221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40265057337516330739642961 30198793003137248054732221)
    ·
      refine ⟨11324547376176468020524583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30198793003137248054732221 11324547376176468020524583)
      ·
        refine ⟨16986821064264702030786875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11324547376176468020524583 16986821064264702030786875)
        ·
          refine ⟨25480231596397053046180313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16986821064264702030786875 25480231596397053046180313)
          ·
            refine ⟨19110173697297789784635235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25480231596397053046180313 19110173697297789784635235)
            ·
              refine ⟨28665260545946684676952853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19110173697297789784635235 28665260545946684676952853)
              ·
                refine ⟨1343684088091250844232165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 28665260545946684676952853 1343684088091250844232165)
                ·
                  refine ⟨251940766517109533293531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1343684088091250844232165 251940766517109533293531)
                  ·
                    rfl

theorem cell21_1103969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 6, 4].length) (baseStart_1103969 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1103969 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1103969 prefixEnd_1103969 := by exact prefixLift 1103969
  have htrace : WordTrace (prefixWord ++ tailWord_1103969) baseStart_1103969 baseEnd_1103969 := by
    simpa [prefixWord, tailWord_1103969, baseEnd_1103969] using wordTrace_append hprefix tailTrace_1103969
  have hstable : (prefixWord ++ tailWord_1103969).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1103969).length < 2 ^ (prefixWord ++ tailWord_1103969).sum := by decide
  have hdescent : baseEnd_1103969 < baseStart_1103969 := by decide
  rcases family_descends (prefixWord ++ tailWord_1103969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1103983 : List Nat := [1, 1, 2, 1, 3, 4, 1, 8]
def baseStart_1103983 : Nat := 118140960795 + 1103983 * 2 ^ 59
def prefixEnd_1103983 : Nat := 4983230072969 + 3 ^ 40 * 1103983 * 2
def baseEnd_1103983 : Nat := 83981320502616206686723

theorem tailTrace_1103983 : CollatzResearch.WordTrace tailWord_1103983 prefixEnd_1103983 83981320502616206686723 := by
  unfold tailWord_1103983
  simp only [CollatzResearch.WordTrace]
  refine ⟨40265567959465611130652603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26843711972977074087101735 40265567959465611130652603)
  ·
    refine ⟨60398351939198416695978905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40265567959465611130652603 60398351939198416695978905)
    ·
      refine ⟨45298763954398812521984179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60398351939198416695978905 45298763954398812521984179)
      ·
        refine ⟨67948145931598218782976269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45298763954398812521984179 67948145931598218782976269)
        ·
          refine ⟨25480554724349332043616101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 67948145931598218782976269 25480554724349332043616101)
          ·
            refine ⟨4777604010815499758178019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 25480554724349332043616101 4777604010815499758178019)
            ·
              refine ⟨7166406016223249637267029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4777604010815499758178019 7166406016223249637267029)
              ·
                refine ⟨83981320502616206686723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7166406016223249637267029 83981320502616206686723)
                ·
                  rfl

theorem cell21_1103983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 1, 8].length) (baseStart_1103983 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1103983 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1103983 prefixEnd_1103983 := by exact prefixLift 1103983
  have htrace : WordTrace (prefixWord ++ tailWord_1103983) baseStart_1103983 baseEnd_1103983 := by
    simpa [prefixWord, tailWord_1103983, baseEnd_1103983] using wordTrace_append hprefix tailTrace_1103983
  have hstable : (prefixWord ++ tailWord_1103983).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1103983).length < 2 ^ (prefixWord ++ tailWord_1103983).sum := by decide
  have hdescent : baseEnd_1103983 < baseStart_1103983 := by decide
  rcases family_descends (prefixWord ++ tailWord_1103983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1103986 : List Nat := [3, 2, 1, 2, 2, 3, 1, 3, 4]
def baseStart_1103986 : Nat := 118140960795 + 1103986 * 2 ^ 59
def prefixEnd_1103986 : Nat := 4983230072969 + 3 ^ 40 * 1103986 * 2
def baseEnd_1103986 : Nat := 251944646148721281510163

theorem tailTrace_1103986 : CollatzResearch.WordTrace tailWord_1103986 prefixEnd_1103986 251944646148721281510163 := by
  unfold tailWord_1103986
  simp only [CollatzResearch.WordTrace]
  refine ⟨10066419344613685660752953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26843784918969828428674541 10066419344613685660752953)
  ·
    refine ⟨7549814508460264245564715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10066419344613685660752953 7549814508460264245564715)
    ·
      refine ⟨11324721762690396368347073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7549814508460264245564715 11324721762690396368347073)
      ·
        refine ⟨8493541322017797276260305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11324721762690396368347073 8493541322017797276260305)
        ·
          refine ⟨6370155991513347957195229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8493541322017797276260305 6370155991513347957195229)
          ·
            refine ⟨2388808496817505483948211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6370155991513347957195229 2388808496817505483948211)
            ·
              refine ⟨3583212745226258225922317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2388808496817505483948211 3583212745226258225922317)
              ·
                refine ⟨1343704779459846834720869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3583212745226258225922317 1343704779459846834720869)
                ·
                  refine ⟨251944646148721281510163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1343704779459846834720869 251944646148721281510163)
                  ·
                    rfl

theorem cell21_1103986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 3, 1, 3, 4].length) (baseStart_1103986 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1103986 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1103986 prefixEnd_1103986 := by exact prefixLift 1103986
  have htrace : WordTrace (prefixWord ++ tailWord_1103986) baseStart_1103986 baseEnd_1103986 := by
    simpa [prefixWord, tailWord_1103986, baseEnd_1103986] using wordTrace_append hprefix tailTrace_1103986
  have hstable : (prefixWord ++ tailWord_1103986).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1103986).length < 2 ^ (prefixWord ++ tailWord_1103986).sum := by decide
  have hdescent : baseEnd_1103986 < baseStart_1103986 := by decide
  rcases family_descends (prefixWord ++ tailWord_1103986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1104020 : List Nat := [2, 4, 2, 3, 1, 1, 2, 2, 4]
def baseStart_1104020 : Nat := 118140960795 + 1104020 * 2 ^ 59
def prefixEnd_1104020 : Nat := 4983230072969 + 3 ^ 40 * 1104020 * 2
def baseEnd_1104020 : Nat := 251952405411944777943427

theorem tailTrace_1104020 : CollatzResearch.WordTrace tailWord_1104020 prefixEnd_1104020 251952405411944777943427 := by
  unfold tailWord_1104020
  simp only [CollatzResearch.WordTrace]
  refine ⟨20133458730165783224874757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26844611640221044299833009 20133458730165783224874757)
  ·
    refine ⟨3775023511906084354664017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 20133458730165783224874757 3775023511906084354664017)
    ·
      refine ⟨2831267633929563265998013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3775023511906084354664017 2831267633929563265998013)
      ·
        refine ⟨1061725362723586224749255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2831267633929563265998013 1061725362723586224749255)
        ·
          refine ⟨1592588044085379337123883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1061725362723586224749255 1592588044085379337123883)
          ·
            refine ⟨2388882066128069005685825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1592588044085379337123883 2388882066128069005685825)
            ·
              refine ⟨1791661549596051754264369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2388882066128069005685825 1791661549596051754264369)
              ·
                refine ⟨1343746162197038815698277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1791661549596051754264369 1343746162197038815698277)
                ·
                  refine ⟨251952405411944777943427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1343746162197038815698277 251952405411944777943427)
                  ·
                    rfl

theorem cell21_1104020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 1, 2, 2, 4].length) (baseStart_1104020 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1104020 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1104020 prefixEnd_1104020 := by exact prefixLift 1104020
  have htrace : WordTrace (prefixWord ++ tailWord_1104020) baseStart_1104020 baseEnd_1104020 := by
    simpa [prefixWord, tailWord_1104020, baseEnd_1104020] using wordTrace_append hprefix tailTrace_1104020
  have hstable : (prefixWord ++ tailWord_1104020).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1104020).length < 2 ^ (prefixWord ++ tailWord_1104020).sum := by decide
  have hdescent : baseEnd_1104020 < baseStart_1104020 := by decide
  rcases family_descends (prefixWord ++ tailWord_1104020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1104090 : List Nat := [3, 1, 1, 2, 2, 1, 3, 3, 5]
def baseStart_1104090 : Nat := 118140960795 + 1104090 * 2 ^ 59
def prefixEnd_1104090 : Nat := 4983230072969 + 3 ^ 40 * 1104090 * 2
def baseEnd_1104090 : Nat := 251968380365640211776617

theorem tailTrace_1104090 : CollatzResearch.WordTrace tailWord_1104090 prefixEnd_1104090 251968380365640211776617 := by
  unfold tailWord_1104090
  simp only [CollatzResearch.WordTrace]
  refine ⟨10067367642519492101199431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26846313713385312269865149 10067367642519492101199431)
  ·
    refine ⟨15101051463779238151799147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10067367642519492101199431 15101051463779238151799147)
    ·
      refine ⟨22651577195668857227698721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15101051463779238151799147 22651577195668857227698721)
      ·
        refine ⟨16988682896751642920774041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22651577195668857227698721 16988682896751642920774041)
        ·
          refine ⟨12741512172563732190580531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16988682896751642920774041 12741512172563732190580531)
          ·
            refine ⟨19112268258845598285870797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12741512172563732190580531 19112268258845598285870797)
            ·
              refine ⟨7167100597067099357201549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19112268258845598285870797 7167100597067099357201549)
              ·
                refine ⟨2687662723900162258950581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7167100597067099357201549 2687662723900162258950581)
                ·
                  refine ⟨251968380365640211776617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2687662723900162258950581 251968380365640211776617)
                  ·
                    rfl

theorem cell21_1104090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 3, 3, 5].length) (baseStart_1104090 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1104090 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1104090 prefixEnd_1104090 := by exact prefixLift 1104090
  have htrace : WordTrace (prefixWord ++ tailWord_1104090) baseStart_1104090 baseEnd_1104090 := by
    simpa [prefixWord, tailWord_1104090, baseEnd_1104090] using wordTrace_append hprefix tailTrace_1104090
  have hstable : (prefixWord ++ tailWord_1104090).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1104090).length < 2 ^ (prefixWord ++ tailWord_1104090).sum := by decide
  have hdescent : baseEnd_1104090 < baseStart_1104090 := by decide
  rcases family_descends (prefixWord ++ tailWord_1104090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1104124 : List Nat := [2, 2, 2, 1, 4, 1, 3, 3, 3]
def baseStart_1104124 : Nat := 118140960795 + 1104124 * 2 ^ 59
def prefixEnd_1104124 : Nat := 4983230072969 + 3 ^ 40 * 1104124 * 2
def baseEnd_1104124 : Nat := 251976139628863708209881

theorem tailTrace_1104124 : CollatzResearch.WordTrace tailWord_1104124 prefixEnd_1104124 251976139628863708209881 := by
  unfold tailWord_1104124
  simp only [CollatzResearch.WordTrace]
  refine ⟨20135355325977396105767713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26847140434636528141023617 20135355325977396105767713)
  ·
    refine ⟨15101516494483047079325785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20135355325977396105767713 15101516494483047079325785)
    ·
      refine ⟨11326137370862285309494339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15101516494483047079325785 11326137370862285309494339)
      ·
        refine ⟨16989206056293427964241509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11326137370862285309494339 16989206056293427964241509)
        ·
          refine ⟨3185476135555017743295283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16989206056293427964241509 3185476135555017743295283)
          ·
            refine ⟨4778214203332526614942925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3185476135555017743295283 4778214203332526614942925)
            ·
              refine ⟨1791830326249697480603597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4778214203332526614942925 1791830326249697480603597)
              ·
                refine ⟨671936372343636555226349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1791830326249697480603597 671936372343636555226349)
                ·
                  refine ⟨251976139628863708209881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 671936372343636555226349 251976139628863708209881)
                  ·
                    rfl

theorem cell21_1104124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 3, 3, 3].length) (baseStart_1104124 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1104124 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1104124 prefixEnd_1104124 := by exact prefixLift 1104124
  have htrace : WordTrace (prefixWord ++ tailWord_1104124) baseStart_1104124 baseEnd_1104124 := by
    simpa [prefixWord, tailWord_1104124, baseEnd_1104124] using wordTrace_append hprefix tailTrace_1104124
  have hstable : (prefixWord ++ tailWord_1104124).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1104124).length < 2 ^ (prefixWord ++ tailWord_1104124).sum := by decide
  have hdescent : baseEnd_1104124 < baseStart_1104124 := by decide
  rcases family_descends (prefixWord ++ tailWord_1104124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1104200 : List Nat := [2, 1, 3, 1, 1, 2, 6, 2, 3]
def baseStart_1104200 : Nat := 118140960795 + 1104200 * 2 ^ 59
def prefixEnd_1104200 : Nat := 4983230072969 + 3 ^ 40 * 1104200 * 2
def baseEnd_1104200 : Nat := 251993483864304464943059

theorem tailTrace_1104200 : CollatzResearch.WordTrace tailWord_1104200 prefixEnd_1104200 251993483864304464943059 := by
  unfold tailWord_1104200
  simp only [CollatzResearch.WordTrace]
  refine ⟨20136741299839728595651027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26848988399786304794201369 20136741299839728595651027)
  ·
    refine ⟨30205111949759592893476541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20136741299839728595651027 30205111949759592893476541)
    ·
      refine ⟨11326916981159847335053703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30205111949759592893476541 11326916981159847335053703)
      ·
        refine ⟨16990375471739771002580555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11326916981159847335053703 16990375471739771002580555)
        ·
          refine ⟨25485563207609656503870833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16990375471739771002580555 25485563207609656503870833)
          ·
            refine ⟨19114172405707242377903125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25485563207609656503870833 19114172405707242377903125)
            ·
              refine ⟨895976831517526986464209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 19114172405707242377903125 895976831517526986464209)
              ·
                refine ⟨671982623638145239848157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 895976831517526986464209 671982623638145239848157)
                ·
                  refine ⟨251993483864304464943059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 671982623638145239848157 251993483864304464943059)
                  ·
                    rfl

theorem cell21_1104200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 6, 2, 3].length) (baseStart_1104200 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1104200 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1104200 prefixEnd_1104200 := by exact prefixLift 1104200
  have htrace : WordTrace (prefixWord ++ tailWord_1104200) baseStart_1104200 baseEnd_1104200 := by
    simpa [prefixWord, tailWord_1104200, baseEnd_1104200] using wordTrace_append hprefix tailTrace_1104200
  have hstable : (prefixWord ++ tailWord_1104200).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1104200).length < 2 ^ (prefixWord ++ tailWord_1104200).sum := by decide
  have hdescent : baseEnd_1104200 < baseStart_1104200 := by decide
  rcases family_descends (prefixWord ++ tailWord_1104200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1104228 : List Nat := [2, 3, 1, 1, 3, 1, 5, 5]
def baseStart_1104228 : Nat := 118140960795 + 1104228 * 2 ^ 59
def prefixEnd_1104228 : Nat := 4983230072969 + 3 ^ 40 * 1104228 * 2
def baseEnd_1104228 : Nat := 83999957948594212825445

theorem tailTrace_1104228 : CollatzResearch.WordTrace tailWord_1104228 prefixEnd_1104228 83999957948594212825445 := by
  unfold tailWord_1104228
  simp only [CollatzResearch.WordTrace]
  refine ⟨20137251921789008986660669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26849669229052011982214225 20137251921789008986660669)
  ·
    refine ⟨7551469470670878369997751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20137251921789008986660669 7551469470670878369997751)
    ·
      refine ⟨11327204206006317554996627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7551469470670878369997751 11327204206006317554996627)
      ·
        refine ⟨16990806309009476332494941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11327204206006317554996627 16990806309009476332494941)
        ·
          refine ⟨6371552365878553624685603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16990806309009476332494941 6371552365878553624685603)
          ·
            refine ⟨9557328548817830437028405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6371552365878553624685603 9557328548817830437028405)
            ·
              refine ⟨895999551451671603471413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 9557328548817830437028405 895999551451671603471413)
              ·
                refine ⟨83999957948594212825445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 895999551451671603471413 83999957948594212825445)
                ·
                  rfl

theorem cell21_1104228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 5, 5].length) (baseStart_1104228 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1104228 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1104228 prefixEnd_1104228 := by exact prefixLift 1104228
  have htrace : WordTrace (prefixWord ++ tailWord_1104228) baseStart_1104228 baseEnd_1104228 := by
    simpa [prefixWord, tailWord_1104228, baseEnd_1104228] using wordTrace_append hprefix tailTrace_1104228
  have hstable : (prefixWord ++ tailWord_1104228).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1104228).length < 2 ^ (prefixWord ++ tailWord_1104228).sum := by decide
  have hdescent : baseEnd_1104228 < baseStart_1104228 := by decide
  rcases family_descends (prefixWord ++ tailWord_1104228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1104259 : List Nat := [1, 1, 1, 3, 6, 1, 2, 1, 5]
def baseStart_1104259 : Nat := 118140960795 + 1104259 * 2 ^ 59
def prefixEnd_1104259 : Nat := 4983230072969 + 3 ^ 40 * 1104259 * 2
def baseEnd_1104259 : Nat := 252006948468133473459605

theorem tailTrace_1104259 : CollatzResearch.WordTrace tailWord_1104259 prefixEnd_1104259 252006948468133473459605 := by
  unfold tailWord_1104259
  simp only [CollatzResearch.WordTrace]
  refine ⟨40275634506465710267699831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26850423004310473511799887 40275634506465710267699831)
  ·
    refine ⟨60413451759698565401549747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40275634506465710267699831 60413451759698565401549747)
    ·
      refine ⟨90620177639547848102324621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60413451759698565401549747 90620177639547848102324621)
      ·
        refine ⟨33982566614830443038371733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 90620177639547848102324621 33982566614830443038371733)
        ·
          refine ⟨1592932810070177017423675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 33982566614830443038371733 1592932810070177017423675)
          ·
            refine ⟨2389399215105265526135513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1592932810070177017423675 2389399215105265526135513)
            ·
              refine ⟨1792049411328949144601635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2389399215105265526135513 1792049411328949144601635)
              ·
                refine ⟨2688074116993423716902453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1792049411328949144601635 2688074116993423716902453)
                ·
                  refine ⟨252006948468133473459605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2688074116993423716902453 252006948468133473459605)
                  ·
                    rfl

theorem cell21_1104259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 1, 2, 1, 5].length) (baseStart_1104259 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1104259 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1104259 prefixEnd_1104259 := by exact prefixLift 1104259
  have htrace : WordTrace (prefixWord ++ tailWord_1104259) baseStart_1104259 baseEnd_1104259 := by
    simpa [prefixWord, tailWord_1104259, baseEnd_1104259] using wordTrace_append hprefix tailTrace_1104259
  have hstable : (prefixWord ++ tailWord_1104259).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1104259).length < 2 ^ (prefixWord ++ tailWord_1104259).sum := by decide
  have hdescent : baseEnd_1104259 < baseStart_1104259 := by decide
  rcases family_descends (prefixWord ++ tailWord_1104259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1104287 : List Nat := [1, 1, 2, 5, 1, 1, 3, 7]
def baseStart_1104287 : Nat := 118140960795 + 1104287 * 2 ^ 59
def prefixEnd_1104287 : Nat := 4983230072969 + 3 ^ 40 * 1104287 * 2
def baseEnd_1104287 : Nat := 84004446149870548997627

theorem tailTrace_1104287 : CollatzResearch.WordTrace tailWord_1104287 prefixEnd_1104287 84004446149870548997627 := by
  unfold tailWord_1104287
  simp only [CollatzResearch.WordTrace]
  refine ⟨40276655750364271049719115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26851103833576180699812743 40276655750364271049719115)
  ·
    refine ⟨60414983625546406574578673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40276655750364271049719115 60414983625546406574578673)
    ·
      refine ⟨45311237719159804930934005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60414983625546406574578673 45311237719159804930934005)
      ·
        refine ⟨4247928536171231712275063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 45311237719159804930934005 4247928536171231712275063)
        ·
          refine ⟨6371892804256847568412595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4247928536171231712275063 6371892804256847568412595)
          ·
            refine ⟨9557839206385271352618893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6371892804256847568412595 9557839206385271352618893)
            ·
              refine ⟨3584189702394476757232085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9557839206385271352618893 3584189702394476757232085)
              ·
                refine ⟨84004446149870548997627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3584189702394476757232085 84004446149870548997627)
                ·
                  rfl

theorem cell21_1104287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 3, 7].length) (baseStart_1104287 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1104287 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1104287 prefixEnd_1104287 := by exact prefixLift 1104287
  have htrace : WordTrace (prefixWord ++ tailWord_1104287) baseStart_1104287 baseEnd_1104287 := by
    simpa [prefixWord, tailWord_1104287, baseEnd_1104287] using wordTrace_append hprefix tailTrace_1104287
  have hstable : (prefixWord ++ tailWord_1104287).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1104287).length < 2 ^ (prefixWord ++ tailWord_1104287).sum := by decide
  have hdescent : baseEnd_1104287 < baseStart_1104287 := by decide
  rcases family_descends (prefixWord ++ tailWord_1104287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1104324 : List Nat := [2, 3, 3, 2, 2, 2, 2, 1, 4]
def baseStart_1104324 : Nat := 118140960795 + 1104324 * 2 ^ 59
def prefixEnd_1104324 : Nat := 4983230072969 + 3 ^ 40 * 1104324 * 2
def baseEnd_1104324 : Nat := 252021782353707804876139

theorem tailTrace_1104324 : CollatzResearch.WordTrace tailWord_1104324 prefixEnd_1104324 252021782353707804876139 := by
  unfold tailWord_1104324
  simp only [CollatzResearch.WordTrace]
  refine ⟨20139002625615113184408013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26852003500820150912544017 20139002625615113184408013)
  ·
    refine ⟨7552125984605667444153005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20139002625615113184408013 7552125984605667444153005)
    ·
      refine ⟨2832047244227125291557377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7552125984605667444153005 2832047244227125291557377)
      ·
        refine ⟨2124035433170343968668033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2832047244227125291557377 2124035433170343968668033)
        ·
          refine ⟨1593026574877757976501025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2124035433170343968668033 1593026574877757976501025)
          ·
            refine ⟨1194769931158318482375769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1593026574877757976501025 1194769931158318482375769)
            ·
              refine ⟨896077448368738861781827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1194769931158318482375769 896077448368738861781827)
              ·
                refine ⟨1344116172553108292672741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 896077448368738861781827 1344116172553108292672741)
                ·
                  refine ⟨252021782353707804876139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1344116172553108292672741 252021782353707804876139)
                  ·
                    rfl

theorem cell21_1104324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 2, 2, 1, 4].length) (baseStart_1104324 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1104324 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1104324 prefixEnd_1104324 := by exact prefixLift 1104324
  have htrace : WordTrace (prefixWord ++ tailWord_1104324) baseStart_1104324 baseEnd_1104324 := by
    simpa [prefixWord, tailWord_1104324, baseEnd_1104324] using wordTrace_append hprefix tailTrace_1104324
  have hstable : (prefixWord ++ tailWord_1104324).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1104324).length < 2 ^ (prefixWord ++ tailWord_1104324).sum := by decide
  have hdescent : baseEnd_1104324 < baseStart_1104324 := by decide
  rcases family_descends (prefixWord ++ tailWord_1104324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1104366 : List Nat := [4, 1, 2, 1, 2, 3, 2, 2, 4]
def baseStart_1104366 : Nat := 118140960795 + 1104366 * 2 ^ 59
def prefixEnd_1104366 : Nat := 4983230072969 + 3 ^ 40 * 1104366 * 2
def baseEnd_1104366 : Nat := 252031367325925065176053

theorem tailTrace_1104366 : CollatzResearch.WordTrace tailWord_1104366 prefixEnd_1104366 252031367325925065176053 := by
  unfold tailWord_1104366
  simp only [CollatzResearch.WordTrace]
  refine ⟨5034942139634758442730619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 26853024744718711694563301 5034942139634758442730619)
  ·
    refine ⟨7552413209452137664095929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5034942139634758442730619 7552413209452137664095929)
    ·
      refine ⟨5664309907089103248071947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7552413209452137664095929 5664309907089103248071947)
      ·
        refine ⟨8496464860633654872107921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5664309907089103248071947 8496464860633654872107921)
        ·
          refine ⟨6372348645475241154080941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8496464860633654872107921 6372348645475241154080941)
          ·
            refine ⟨2389630742053215432780353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6372348645475241154080941 2389630742053215432780353)
            ·
              refine ⟨1792223056539911574585265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2389630742053215432780353 1792223056539911574585265)
              ·
                refine ⟨1344167292404933680938949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1792223056539911574585265 1344167292404933680938949)
                ·
                  refine ⟨252031367325925065176053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1344167292404933680938949 252031367325925065176053)
                  ·
                    rfl

theorem cell21_1104366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 3, 2, 2, 4].length) (baseStart_1104366 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1104366 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1104366 prefixEnd_1104366 := by exact prefixLift 1104366
  have htrace : WordTrace (prefixWord ++ tailWord_1104366) baseStart_1104366 baseEnd_1104366 := by
    simpa [prefixWord, tailWord_1104366, baseEnd_1104366] using wordTrace_append hprefix tailTrace_1104366
  have hstable : (prefixWord ++ tailWord_1104366).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1104366).length < 2 ^ (prefixWord ++ tailWord_1104366).sum := by decide
  have hdescent : baseEnd_1104366 < baseStart_1104366 := by decide
  rcases family_descends (prefixWord ++ tailWord_1104366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1104394 : List Nat := [3, 1, 2, 2, 2, 1, 3, 2, 5]
def baseStart_1104394 : Nat := 118140960795 + 1104394 * 2 ^ 59
def prefixEnd_1104394 : Nat := 4983230072969 + 3 ^ 40 * 1104394 * 2
def baseEnd_1104394 : Nat := 252037757307403238709329

theorem tailTrace_1104394 : CollatzResearch.WordTrace tailWord_1104394 prefixEnd_1104394 252037757307403238709329 := by
  unfold tailWord_1104394
  simp only [CollatzResearch.WordTrace]
  refine ⟨10070139590244157080966059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26853705573984418882576157 10070139590244157080966059)
  ·
    refine ⟨15105209385366235621449089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10070139590244157080966059 15105209385366235621449089)
    ·
      refine ⟨11328907039024676716086817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15105209385366235621449089 11328907039024676716086817)
      ·
        refine ⟨8496680279268507537065113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11328907039024676716086817 8496680279268507537065113)
        ·
          refine ⟨6372510209451380652798835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8496680279268507537065113 6372510209451380652798835)
          ·
            refine ⟨9558765314177070979198253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6372510209451380652798835 9558765314177070979198253)
            ·
              refine ⟨3584536992816401617199345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9558765314177070979198253 3584536992816401617199345)
              ·
                refine ⟨2688402744612301212899509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3584536992816401617199345 2688402744612301212899509)
                ·
                  refine ⟨252037757307403238709329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2688402744612301212899509 252037757307403238709329)
                  ·
                    rfl

theorem cell21_1104394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 3, 2, 5].length) (baseStart_1104394 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1104394 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1104394 prefixEnd_1104394 := by exact prefixLift 1104394
  have htrace : WordTrace (prefixWord ++ tailWord_1104394) baseStart_1104394 baseEnd_1104394 := by
    simpa [prefixWord, tailWord_1104394, baseEnd_1104394] using wordTrace_append hprefix tailTrace_1104394
  have hstable : (prefixWord ++ tailWord_1104394).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1104394).length < 2 ^ (prefixWord ++ tailWord_1104394).sum := by decide
  have hdescent : baseEnd_1104394 < baseStart_1104394 := by decide
  rcases family_descends (prefixWord ++ tailWord_1104394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1104442 : List Nat := [3, 1, 1, 1, 3, 4, 3, 1, 4]
def baseStart_1104442 : Nat := 118140960795 + 1104442 * 2 ^ 59
def prefixEnd_1104442 : Nat := 4983230072969 + 3 ^ 40 * 1104442 * 2
def baseEnd_1104442 : Nat := 252048711561365821909231

theorem tailTrace_1104442 : CollatzResearch.WordTrace tailWord_1104442 prefixEnd_1104442 252048711561365821909231 := by
  unfold tailWord_1104442
  simp only [CollatzResearch.WordTrace]
  refine ⟨10070577266200683130402895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26854872709868488347741053 10070577266200683130402895)
  ·
    refine ⟨15105865899301024695604343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10070577266200683130402895 15105865899301024695604343)
    ·
      refine ⟨22658798848951537043406515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15105865899301024695604343 22658798848951537043406515)
      ·
        refine ⟨33988198273427305565109773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22658798848951537043406515 33988198273427305565109773)
        ·
          refine ⟨12745574352535239586916165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33988198273427305565109773 12745574352535239586916165)
          ·
            refine ⟨2389795191100357422546781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12745574352535239586916165 2389795191100357422546781)
            ·
              refine ⟨896173196662634033455043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2389795191100357422546781 896173196662634033455043)
              ·
                refine ⟨1344259794993951050182565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 896173196662634033455043 1344259794993951050182565)
                ·
                  refine ⟨252048711561365821909231, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1344259794993951050182565 252048711561365821909231)
                  ·
                    rfl

theorem cell21_1104442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 4, 3, 1, 4].length) (baseStart_1104442 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1104442 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1104442 prefixEnd_1104442 := by exact prefixLift 1104442
  have htrace : WordTrace (prefixWord ++ tailWord_1104442) baseStart_1104442 baseEnd_1104442 := by
    simpa [prefixWord, tailWord_1104442, baseEnd_1104442] using wordTrace_append hprefix tailTrace_1104442
  have hstable : (prefixWord ++ tailWord_1104442).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1104442).length < 2 ^ (prefixWord ++ tailWord_1104442).sum := by decide
  have hdescent : baseEnd_1104442 < baseStart_1104442 := by decide
  rcases family_descends (prefixWord ++ tailWord_1104442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1104484 : List Nat := [2, 3, 1, 1, 2, 2, 1, 3, 6]
def baseStart_1104484 : Nat := 118140960795 + 1104484 * 2 ^ 59
def prefixEnd_1104484 : Nat := 4983230072969 + 3 ^ 40 * 1104484 * 2
def baseEnd_1104484 : Nat := 252058296533583082209145

theorem tailTrace_1104484 : CollatzResearch.WordTrace tailWord_1104484 prefixEnd_1104484 252058296533583082209145 := by
  unfold tailWord_1104484
  simp only [CollatzResearch.WordTrace]
  refine ⟨20141920465325286847320253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26855893953767049129760337 20141920465325286847320253)
  ·
    refine ⟨7553220174496982567745095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20141920465325286847320253 7553220174496982567745095)
    ·
      refine ⟨11329830261745473851617643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7553220174496982567745095 11329830261745473851617643)
      ·
        refine ⟨16994745392618210777426465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11329830261745473851617643 16994745392618210777426465)
        ·
          refine ⟨12746059044463658083069849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16994745392618210777426465 12746059044463658083069849)
          ·
            refine ⟨9559544283347743562302387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12746059044463658083069849 9559544283347743562302387)
            ·
              refine ⟨14339316425021615343453581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9559544283347743562302387 14339316425021615343453581)
              ·
                refine ⟨5377243659383105753795093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14339316425021615343453581 5377243659383105753795093)
                ·
                  refine ⟨252058296533583082209145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5377243659383105753795093 252058296533583082209145)
                  ·
                    rfl

theorem cell21_1104484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 1, 3, 6].length) (baseStart_1104484 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1104484 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1104484 prefixEnd_1104484 := by exact prefixLift 1104484
  have htrace : WordTrace (prefixWord ++ tailWord_1104484) baseStart_1104484 baseEnd_1104484 := by
    simpa [prefixWord, tailWord_1104484, baseEnd_1104484] using wordTrace_append hprefix tailTrace_1104484
  have hstable : (prefixWord ++ tailWord_1104484).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1104484).length < 2 ^ (prefixWord ++ tailWord_1104484).sum := by decide
  have hdescent : baseEnd_1104484 < baseStart_1104484 := by decide
  rcases family_descends (prefixWord ++ tailWord_1104484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1104538 : List Nat := [3, 1, 1, 6, 1, 2, 2, 2, 3]
def baseStart_1104538 : Nat := 118140960795 + 1104538 * 2 ^ 59
def prefixEnd_1104538 : Nat := 4983230072969 + 3 ^ 40 * 1104538 * 2
def baseEnd_1104538 : Nat := 252070620069290988309035

theorem tailTrace_1104538 : CollatzResearch.WordTrace tailWord_1104538 prefixEnd_1104538 252070620069290988309035 := by
  unfold tailWord_1104538
  simp only [CollatzResearch.WordTrace]
  refine ⟨10071452618113735229276567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26857206981636627278070845 10071452618113735229276567)
  ·
    refine ⟨15107178927170602843914851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10071452618113735229276567 15107178927170602843914851)
    ·
      refine ⟨22660768390755904265872277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15107178927170602843914851 22660768390755904265872277)
      ·
        refine ⟨1062223518316683012462763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 22660768390755904265872277 1062223518316683012462763)
        ·
          refine ⟨1593335277475024518694145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1062223518316683012462763 1593335277475024518694145)
          ·
            refine ⟨1195001458106268389020609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1593335277475024518694145 1195001458106268389020609)
            ·
              refine ⟨896251093579701291765457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1195001458106268389020609 896251093579701291765457)
              ·
                refine ⟨672188320184775968824093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 896251093579701291765457 672188320184775968824093)
                ·
                  refine ⟨252070620069290988309035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 672188320184775968824093 252070620069290988309035)
                  ·
                    rfl

theorem cell21_1104538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 2, 2, 2, 3].length) (baseStart_1104538 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1104538 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1104538 prefixEnd_1104538 := by exact prefixLift 1104538
  have htrace : WordTrace (prefixWord ++ tailWord_1104538) baseStart_1104538 baseEnd_1104538 := by
    simpa [prefixWord, tailWord_1104538, baseEnd_1104538] using wordTrace_append hprefix tailTrace_1104538
  have hstable : (prefixWord ++ tailWord_1104538).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1104538).length < 2 ^ (prefixWord ++ tailWord_1104538).sum := by decide
  have hdescent : baseEnd_1104538 < baseStart_1104538 := by decide
  rcases family_descends (prefixWord ++ tailWord_1104538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1104566 : List Nat := [5, 1, 3, 1, 2, 1, 3, 5]
def baseStart_1104566 : Nat := 118140960795 + 1104566 * 2 ^ 59
def prefixEnd_1104566 : Nat := 4983230072969 + 3 ^ 40 * 1104566 * 2
def baseEnd_1104566 : Nat := 84025670016923053947437

theorem tailTrace_1104566 : CollatzResearch.WordTrace tailWord_1104566 prefixEnd_1104566 84025670016923053947437 := by
  unfold tailWord_1104566
  simp only [CollatzResearch.WordTrace]
  refine ⟨2517926982272093856195347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 26857887810902334466083701 2517926982272093856195347)
  ·
    refine ⟨3776890473408140784293021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2517926982272093856195347 3776890473408140784293021)
    ·
      refine ⟨1416333927528052794109883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3776890473408140784293021 1416333927528052794109883)
      ·
        refine ⟨2124500891292079191164825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1416333927528052794109883 2124500891292079191164825)
        ·
          refine ⟨1593375668469059393373619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2124500891292079191164825 1593375668469059393373619)
          ·
            refine ⟨2390063502703589090060429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1593375668469059393373619 2390063502703589090060429)
            ·
              refine ⟨896273813513845908772661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2390063502703589090060429 896273813513845908772661)
              ·
                refine ⟨84025670016923053947437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 896273813513845908772661 84025670016923053947437)
                ·
                  rfl

theorem cell21_1104566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 1, 3, 5].length) (baseStart_1104566 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1104566 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1104566 prefixEnd_1104566 := by exact prefixLift 1104566
  have htrace : WordTrace (prefixWord ++ tailWord_1104566) baseStart_1104566 baseEnd_1104566 := by
    simpa [prefixWord, tailWord_1104566, baseEnd_1104566] using wordTrace_append hprefix tailTrace_1104566
  have hstable : (prefixWord ++ tailWord_1104566).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1104566).length < 2 ^ (prefixWord ++ tailWord_1104566).sum := by decide
  have hdescent : baseEnd_1104566 < baseStart_1104566 := by decide
  rcases family_descends (prefixWord ++ tailWord_1104566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1104580 : List Nat := [2, 3, 3, 1, 1, 3, 2, 3, 3]
def baseStart_1104580 : Nat := 118140960795 + 1104580 * 2 ^ 59
def prefixEnd_1104580 : Nat := 4983230072969 + 3 ^ 40 * 1104580 * 2
def baseEnd_1104580 : Nat := 252080205041508248608949

theorem tailTrace_1104580 : CollatzResearch.WordTrace tailWord_1104580 prefixEnd_1104580 252080205041508248608949 := by
  unfold tailWord_1104580
  simp only [CollatzResearch.WordTrace]
  refine ⟨20143671169151391045067597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26858228225535188060090129 20143671169151391045067597)
  ·
    refine ⟨7553876688431771641900349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20143671169151391045067597 7553876688431771641900349)
    ·
      refine ⟨2832703758161914365712631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7553876688431771641900349 2832703758161914365712631)
      ·
        refine ⟨4249055637242871548568947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2832703758161914365712631 4249055637242871548568947)
        ·
          refine ⟨6373583455864307322853421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4249055637242871548568947 6373583455864307322853421)
          ·
            refine ⟨2390093795949115246070033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6373583455864307322853421 2390093795949115246070033)
            ·
              refine ⟨1792570346961836434552525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2390093795949115246070033 1792570346961836434552525)
              ·
                refine ⟨672213880110688662957197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1792570346961836434552525 672213880110688662957197)
                ·
                  refine ⟨252080205041508248608949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 672213880110688662957197 252080205041508248608949)
                  ·
                    rfl

theorem cell21_1104580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 3, 2, 3, 3].length) (baseStart_1104580 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1104580 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1104580 prefixEnd_1104580 := by exact prefixLift 1104580
  have htrace : WordTrace (prefixWord ++ tailWord_1104580) baseStart_1104580 baseEnd_1104580 := by
    simpa [prefixWord, tailWord_1104580, baseEnd_1104580] using wordTrace_append hprefix tailTrace_1104580
  have hstable : (prefixWord ++ tailWord_1104580).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1104580).length < 2 ^ (prefixWord ++ tailWord_1104580).sum := by decide
  have hdescent : baseEnd_1104580 < baseStart_1104580 := by decide
  rcases family_descends (prefixWord ++ tailWord_1104580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1104622 : List Nat := [4, 1, 2, 1, 1, 3, 2, 2, 5]
def baseStart_1104622 : Nat := 118140960795 + 1104622 * 2 ^ 59
def prefixEnd_1104622 : Nat := 4983230072969 + 3 ^ 40 * 1104622 * 2
def baseEnd_1104622 : Nat := 252089790013725508908863

theorem tailTrace_1104622 : CollatzResearch.WordTrace tailWord_1104622 prefixEnd_1104622 252089790013725508908863 := by
  unfold tailWord_1104622
  simp only [CollatzResearch.WordTrace]
  refine ⟨5036109275518827907895515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 26859249469433748842109413 5036109275518827907895515)
  ·
    refine ⟨7554163913278241861843273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5036109275518827907895515 7554163913278241861843273)
    ·
      refine ⟨5665622934958681396382455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7554163913278241861843273 5665622934958681396382455)
      ·
        refine ⟨8498434402438022094573683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5665622934958681396382455 8498434402438022094573683)
        ·
          refine ⟨12747651603657033141860525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8498434402438022094573683 12747651603657033141860525)
          ·
            refine ⟨4780369351371387428197697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12747651603657033141860525 4780369351371387428197697)
            ·
              refine ⟨3585277013528540571148273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4780369351371387428197697 3585277013528540571148273)
              ·
                refine ⟨2688957760146405428361205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3585277013528540571148273 2688957760146405428361205)
                ·
                  refine ⟨252089790013725508908863, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2688957760146405428361205 252089790013725508908863)
                  ·
                    rfl

theorem cell21_1104622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 2, 2, 5].length) (baseStart_1104622 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1104622 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1104622 prefixEnd_1104622 := by exact prefixLift 1104622
  have htrace : WordTrace (prefixWord ++ tailWord_1104622) baseStart_1104622 baseEnd_1104622 := by
    simpa [prefixWord, tailWord_1104622, baseEnd_1104622] using wordTrace_append hprefix tailTrace_1104622
  have hstable : (prefixWord ++ tailWord_1104622).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1104622).length < 2 ^ (prefixWord ++ tailWord_1104622).sum := by decide
  have hdescent : baseEnd_1104622 < baseStart_1104622 := by decide
  rcases family_descends (prefixWord ++ tailWord_1104622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1104636 : List Nat := [2, 2, 2, 1, 3, 2, 1, 2, 6]
def baseStart_1104636 : Nat := 118140960795 + 1104636 * 2 ^ 59
def prefixEnd_1104636 : Nat := 4983230072969 + 3 ^ 40 * 1104636 * 2
def baseEnd_1104636 : Nat := 252092985004464595675501

theorem tailTrace_1104636 : CollatzResearch.WordTrace tailWord_1104636 prefixEnd_1104636 252092985004464595675501 := by
  unfold tailWord_1104636
  simp only [CollatzResearch.WordTrace]
  refine ⟨20144692413049951827086881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26859589884066602436115841 20144692413049951827086881)
  ·
    refine ⟨15108519309787463870315161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20144692413049951827086881 15108519309787463870315161)
    ·
      refine ⟨11331389482340597902736371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15108519309787463870315161 11331389482340597902736371)
      ·
        refine ⟨16997084223510896854104557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11331389482340597902736371 16997084223510896854104557)
        ·
          refine ⟨6373906583816586320289209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16997084223510896854104557 6373906583816586320289209)
          ·
            refine ⟨4780429937862439740216907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6373906583816586320289209 4780429937862439740216907)
            ·
              refine ⟨7170644906793659610325361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4780429937862439740216907 7170644906793659610325361)
              ·
                refine ⟨5377983680095244707744021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7170644906793659610325361 5377983680095244707744021)
                ·
                  refine ⟨252092985004464595675501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5377983680095244707744021 252092985004464595675501)
                  ·
                    rfl

theorem cell21_1104636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 1, 2, 6].length) (baseStart_1104636 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1104636 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1104636 prefixEnd_1104636 := by exact prefixLift 1104636
  have htrace : WordTrace (prefixWord ++ tailWord_1104636) baseStart_1104636 baseEnd_1104636 := by
    simpa [prefixWord, tailWord_1104636, baseEnd_1104636] using wordTrace_append hprefix tailTrace_1104636
  have hstable : (prefixWord ++ tailWord_1104636).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1104636).length < 2 ^ (prefixWord ++ tailWord_1104636).sum := by decide
  have hdescent : baseEnd_1104636 < baseStart_1104636 := by decide
  rcases family_descends (prefixWord ++ tailWord_1104636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1104878 : List Nat := [4, 1, 2, 1, 13]
def baseStart_1104878 : Nat := 118140960795 + 1104878 * 2 ^ 59
def prefixEnd_1104878 : Nat := 4983230072969 + 3 ^ 40 * 1104878 * 2
def baseEnd_1104878 : Nat := 3112940897549703119033

theorem tailTrace_1104878 : CollatzResearch.WordTrace tailWord_1104878 prefixEnd_1104878 3112940897549703119033 := by
  unfold tailWord_1104878
  simp only [CollatzResearch.WordTrace]
  refine ⟨5037276411402897373060411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 26865474194148785989655525 5037276411402897373060411)
  ·
    refine ⟨7555914617104346059590617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5037276411402897373060411 7555914617104346059590617)
    ·
      refine ⟨5666935962828259544692963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7555914617104346059590617 5666935962828259544692963)
      ·
        refine ⟨8500403944242389317039445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5666935962828259544692963 8500403944242389317039445)
        ·
          refine ⟨3112940897549703119033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 13 8500403944242389317039445 3112940897549703119033)
          ·
            rfl

theorem cell21_1104878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 13].length) (baseStart_1104878 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1104878 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1104878 prefixEnd_1104878 := by exact prefixLift 1104878
  have htrace : WordTrace (prefixWord ++ tailWord_1104878) baseStart_1104878 baseEnd_1104878 := by
    simpa [prefixWord, tailWord_1104878, baseEnd_1104878] using wordTrace_append hprefix tailTrace_1104878
  have hstable : (prefixWord ++ tailWord_1104878).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1104878).length < 2 ^ (prefixWord ++ tailWord_1104878).sum := by decide
  have hdescent : baseEnd_1104878 < baseStart_1104878 := by decide
  rcases family_descends (prefixWord ++ tailWord_1104878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1104881 : List Nat := [1, 2, 2, 2, 4, 2, 2, 2, 4]
def baseStart_1104881 : Nat := 118140960795 + 1104881 * 2 ^ 59
def prefixEnd_1104881 : Nat := 4983230072969 + 3 ^ 40 * 1104881 * 2
def baseEnd_1104881 : Nat := 252148897342398614091667

theorem tailTrace_1104881 : CollatzResearch.WordTrace tailWord_1104881 prefixEnd_1104881 252148897342398614091667 := by
  unfold tailWord_1104881
  simp only [CollatzResearch.WordTrace]
  refine ⟨40298320710212310496842497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26865547140141540331228331 40298320710212310496842497)
  ·
    refine ⟨30223740532659232872631873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40298320710212310496842497 30223740532659232872631873)
    ·
      refine ⟨22667805399494424654473905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30223740532659232872631873 22667805399494424654473905)
      ·
        refine ⟨17000854049620818490855429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22667805399494424654473905 17000854049620818490855429)
        ·
          refine ⟨3187660134303903467035393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17000854049620818490855429 3187660134303903467035393)
          ·
            refine ⟨2390745100727927600276545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3187660134303903467035393 2390745100727927600276545)
            ·
              refine ⟨1793058825545945700207409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2390745100727927600276545 1793058825545945700207409)
              ·
                refine ⟨1344794119159459275155557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1793058825545945700207409 1344794119159459275155557)
                ·
                  refine ⟨252148897342398614091667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1344794119159459275155557 252148897342398614091667)
                  ·
                    rfl

theorem cell21_1104881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 2, 2, 2, 4].length) (baseStart_1104881 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1104881 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1104881 prefixEnd_1104881 := by exact prefixLift 1104881
  have htrace : WordTrace (prefixWord ++ tailWord_1104881) baseStart_1104881 baseEnd_1104881 := by
    simpa [prefixWord, tailWord_1104881, baseEnd_1104881] using wordTrace_append hprefix tailTrace_1104881
  have hstable : (prefixWord ++ tailWord_1104881).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1104881).length < 2 ^ (prefixWord ++ tailWord_1104881).sum := by decide
  have hdescent : baseEnd_1104881 < baseStart_1104881 := by decide
  rcases family_descends (prefixWord ++ tailWord_1104881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1105002 : List Nat := [3, 1, 3, 2, 2, 1, 3, 1, 5]
def baseStart_1105002 : Nat := 118140960795 + 1105002 * 2 ^ 59
def prefixEnd_1105002 : Nat := 4983230072969 + 3 ^ 40 * 1105002 * 2
def baseEnd_1105002 : Nat := 252176511190929292574753

theorem tailTrace_1105002 : CollatzResearch.WordTrace tailWord_1105002 prefixEnd_1105002 252176511190929292574753 := by
  unfold tailWord_1105002
  simp only [CollatzResearch.WordTrace]
  refine ⟨10075683485693487040499315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26868489295182632107998173 10075683485693487040499315)
  ·
    refine ⟨15113525228540230560748973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10075683485693487040499315 15113525228540230560748973)
    ·
      refine ⟨5667571960702586460280865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15113525228540230560748973 5667571960702586460280865)
      ·
        refine ⟨4250678970526939845210649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5667571960702586460280865 4250678970526939845210649)
        ·
          refine ⟨3188009227895204883907987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4250678970526939845210649 3188009227895204883907987)
          ·
            refine ⟨4782013841842807325861981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3188009227895204883907987 4782013841842807325861981)
            ·
              refine ⟨1793255190691052747198243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4782013841842807325861981 1793255190691052747198243)
              ·
                refine ⟨2689882786036579120797365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1793255190691052747198243 2689882786036579120797365)
                ·
                  refine ⟨252176511190929292574753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2689882786036579120797365 252176511190929292574753)
                  ·
                    rfl

theorem cell21_1105002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 3, 1, 5].length) (baseStart_1105002 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1105002 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1105002 prefixEnd_1105002 := by exact prefixLift 1105002
  have htrace : WordTrace (prefixWord ++ tailWord_1105002) baseStart_1105002 baseEnd_1105002 := by
    simpa [prefixWord, tailWord_1105002, baseEnd_1105002] using wordTrace_append hprefix tailTrace_1105002
  have hstable : (prefixWord ++ tailWord_1105002).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1105002).length < 2 ^ (prefixWord ++ tailWord_1105002).sum := by decide
  have hdescent : baseEnd_1105002 < baseStart_1105002 := by decide
  rcases family_descends (prefixWord ++ tailWord_1105002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1105106 : List Nat := [3, 2, 2, 2, 1, 1, 10]
def baseStart_1105106 : Nat := 118140960795 + 1105106 * 2 ^ 59
def prefixEnd_1105106 : Nat := 4983230072969 + 3 ^ 40 * 1105106 * 2
def baseEnd_1105106 : Nat := 28022249489760913649023

theorem tailTrace_1105106 : CollatzResearch.WordTrace tailWord_1105106 prefixEnd_1105106 28022249489760913649023 := by
  unfold tailWord_1105106
  simp only [CollatzResearch.WordTrace]
  refine ⟨10076631783599293480945793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26871018089598115949188781 10076631783599293480945793)
  ·
    refine ⟨7557473837699470110709345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10076631783599293480945793 7557473837699470110709345)
    ·
      refine ⟨5668105378274602583032009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7557473837699470110709345 5668105378274602583032009)
      ·
        refine ⟨4251079033705951937274007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5668105378274602583032009 4251079033705951937274007)
        ·
          refine ⟨6376618550558927905911011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4251079033705951937274007 6376618550558927905911011)
          ·
            refine ⟨9564927825838391858866517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6376618550558927905911011 9564927825838391858866517)
            ·
              refine ⟨28022249489760913649023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 9564927825838391858866517 28022249489760913649023)
              ·
                rfl

theorem cell21_1105106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 10].length) (baseStart_1105106 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1105106 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1105106 prefixEnd_1105106 := by exact prefixLift 1105106
  have htrace : WordTrace (prefixWord ++ tailWord_1105106) baseStart_1105106 baseEnd_1105106 := by
    simpa [prefixWord, tailWord_1105106, baseEnd_1105106] using wordTrace_append hprefix tailTrace_1105106
  have hstable : (prefixWord ++ tailWord_1105106).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1105106).length < 2 ^ (prefixWord ++ tailWord_1105106).sum := by decide
  have hdescent : baseEnd_1105106 < baseStart_1105106 := by decide
  rcases family_descends (prefixWord ++ tailWord_1105106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1105109 : List Nat := [1, 3, 2, 4, 1, 1, 3, 2, 4]
def baseStart_1105109 : Nat := 118140960795 + 1105109 * 2 ^ 59
def prefixEnd_1105109 : Nat := 4983230072969 + 3 ^ 40 * 1105109 * 2
def baseEnd_1105109 : Nat := 252200930048720884291201

theorem tailTrace_1105109 : CollatzResearch.WordTrace tailWord_1105109 prefixEnd_1105109 252200930048720884291201 := by
  unfold tailWord_1105109
  simp only [CollatzResearch.WordTrace]
  refine ⟨40306636553386305436142381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26871091035590870290761587 40306636553386305436142381)
  ·
    refine ⟨15114988707519864538553393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40306636553386305436142381 15114988707519864538553393)
    ·
      refine ⟨11336241530639898403915045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15114988707519864538553393 11336241530639898403915045)
      ·
        refine ⟨2125545286994980950734071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11336241530639898403915045 2125545286994980950734071)
        ·
          refine ⟨3188317930492471426101107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2125545286994980950734071 3188317930492471426101107)
          ·
            refine ⟨4782476895738707139151661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3188317930492471426101107 4782476895738707139151661)
            ·
              refine ⟨1793428835902015177181873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4782476895738707139151661 1793428835902015177181873)
              ·
                refine ⟨1345071626926511382886405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1793428835902015177181873 1345071626926511382886405)
                ·
                  refine ⟨252200930048720884291201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1345071626926511382886405 252200930048720884291201)
                  ·
                    rfl

theorem cell21_1105109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 3, 2, 4].length) (baseStart_1105109 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1105109 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1105109 prefixEnd_1105109 := by exact prefixLift 1105109
  have htrace : WordTrace (prefixWord ++ tailWord_1105109) baseStart_1105109 baseEnd_1105109 := by
    simpa [prefixWord, tailWord_1105109, baseEnd_1105109] using wordTrace_append hprefix tailTrace_1105109
  have hstable : (prefixWord ++ tailWord_1105109).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1105109).length < 2 ^ (prefixWord ++ tailWord_1105109).sum := by decide
  have hdescent : baseEnd_1105109 < baseStart_1105109 := by decide
  rcases family_descends (prefixWord ++ tailWord_1105109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1105151 : List Nat := [1, 1, 2, 2, 1, 5, 1, 2, 6]
def baseStart_1105151 : Nat := 118140960795 + 1105151 * 2 ^ 59
def prefixEnd_1105151 : Nat := 4983230072969 + 3 ^ 40 * 1105151 * 2
def baseEnd_1105151 : Nat := 252210515020938144591115

theorem tailTrace_1105151 : CollatzResearch.WordTrace tailWord_1105151 prefixEnd_1105151 252210515020938144591115 := by
  unfold tailWord_1105151
  simp only [CollatzResearch.WordTrace]
  refine ⟨40308168419234146609171307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26872112279489431072780871 40308168419234146609171307)
  ·
    refine ⟨60462252628851219913756961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40308168419234146609171307 60462252628851219913756961)
    ·
      refine ⟨45346689471638414935317721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60462252628851219913756961 45346689471638414935317721)
      ·
        refine ⟨34010017103728811201488291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45346689471638414935317721 34010017103728811201488291)
        ·
          refine ⟨51015025655593216802232437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34010017103728811201488291 51015025655593216802232437)
          ·
            refine ⟨4782658655211864075209291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 51015025655593216802232437 4782658655211864075209291)
            ·
              refine ⟨7173987982817796112813937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4782658655211864075209291 7173987982817796112813937)
              ·
                refine ⟨5380490987113347084610453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7173987982817796112813937 5380490987113347084610453)
                ·
                  refine ⟨252210515020938144591115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5380490987113347084610453 252210515020938144591115)
                  ·
                    rfl

theorem cell21_1105151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 1, 2, 6].length) (baseStart_1105151 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1105151 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1105151 prefixEnd_1105151 := by exact prefixLift 1105151
  have htrace : WordTrace (prefixWord ++ tailWord_1105151) baseStart_1105151 baseEnd_1105151 := by
    simpa [prefixWord, tailWord_1105151, baseEnd_1105151] using wordTrace_append hprefix tailTrace_1105151
  have hstable : (prefixWord ++ tailWord_1105151).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1105151).length < 2 ^ (prefixWord ++ tailWord_1105151).sum := by decide
  have hdescent : baseEnd_1105151 < baseStart_1105151 := by decide
  rcases family_descends (prefixWord ++ tailWord_1105151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1105196 : List Nat := [2, 2, 1, 1, 1, 3, 1, 3, 7]
def baseStart_1105196 : Nat := 118140960795 + 1105196 * 2 ^ 59
def prefixEnd_1105196 : Nat := 4983230072969 + 3 ^ 40 * 1105196 * 2
def baseEnd_1105196 : Nat := 252220784634028066341023

theorem tailTrace_1105196 : CollatzResearch.WordTrace tailWord_1105196 prefixEnd_1105196 252220784634028066341023 := by
  unfold tailWord_1105196
  simp only [CollatzResearch.WordTrace]
  refine ⟨20154904852035559647279721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26873206469380746196372961 20154904852035559647279721)
  ·
    refine ⟨15116178639026669735459791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20154904852035559647279721 15116178639026669735459791)
    ·
      refine ⟨22674267958540004603189687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15116178639026669735459791 22674267958540004603189687)
      ·
        refine ⟨34011401937810006904784531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22674267958540004603189687 34011401937810006904784531)
        ·
          refine ⟨51017102906715010357176797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34011401937810006904784531 51017102906715010357176797)
          ·
            refine ⟨19131413590018128883941299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 51017102906715010357176797 19131413590018128883941299)
            ·
              refine ⟨28697120385027193325911949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19131413590018128883941299 28697120385027193325911949)
              ·
                refine ⟨10761420144385197497216981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28697120385027193325911949 10761420144385197497216981)
                ·
                  refine ⟨252220784634028066341023, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10761420144385197497216981 252220784634028066341023)
                  ·
                    rfl

theorem cell21_1105196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 7].length) (baseStart_1105196 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1105196 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1105196 prefixEnd_1105196 := by exact prefixLift 1105196
  have htrace : WordTrace (prefixWord ++ tailWord_1105196) baseStart_1105196 baseEnd_1105196 := by
    simpa [prefixWord, tailWord_1105196, baseEnd_1105196] using wordTrace_append hprefix tailTrace_1105196
  have hstable : (prefixWord ++ tailWord_1105196).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1105196).length < 2 ^ (prefixWord ++ tailWord_1105196).sum := by decide
  have hdescent : baseEnd_1105196 < baseStart_1105196 := by decide
  rcases family_descends (prefixWord ++ tailWord_1105196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1105230 : List Nat := [4, 1, 1, 1, 1, 1, 5, 4, 3]
def baseStart_1105230 : Nat := 118140960795 + 1105230 * 2 ^ 59
def prefixEnd_1105230 : Nat := 4983230072969 + 3 ^ 40 * 1105230 * 2
def baseEnd_1105230 : Nat := 252228543897251562774287

theorem tailTrace_1105230 : CollatzResearch.WordTrace tailWord_1105230 prefixEnd_1105230 252228543897251562774287 := by
  unfold tailWord_1105230
  simp only [CollatzResearch.WordTrace]
  refine ⟨5038881223243492887662143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 26874033190631962067531429 5038881223243492887662143)
  ·
    refine ⟨7558321834865239331493215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5038881223243492887662143 7558321834865239331493215)
    ·
      refine ⟨11337482752297858997239823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7558321834865239331493215 11337482752297858997239823)
      ·
        refine ⟨17006224128446788495859735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11337482752297858997239823 17006224128446788495859735)
        ·
          refine ⟨25509336192670182743789603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17006224128446788495859735 25509336192670182743789603)
          ·
            refine ⟨38264004289005274115684405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25509336192670182743789603 38264004289005274115684405)
            ·
              refine ⟨3587250402094244448345413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 38264004289005274115684405 3587250402094244448345413)
              ·
                refine ⟨672609450392670834064765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3587250402094244448345413 672609450392670834064765)
                ·
                  refine ⟨252228543897251562774287, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 672609450392670834064765 252228543897251562774287)
                  ·
                    rfl

theorem cell21_1105230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 5, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 5, 4, 3].length) (baseStart_1105230 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1105230 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1105230 prefixEnd_1105230 := by exact prefixLift 1105230
  have htrace : WordTrace (prefixWord ++ tailWord_1105230) baseStart_1105230 baseEnd_1105230 := by
    simpa [prefixWord, tailWord_1105230, baseEnd_1105230] using wordTrace_append hprefix tailTrace_1105230
  have hstable : (prefixWord ++ tailWord_1105230).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1105230).length < 2 ^ (prefixWord ++ tailWord_1105230).sum := by decide
  have hdescent : baseEnd_1105230 < baseStart_1105230 := by decide
  rcases family_descends (prefixWord ++ tailWord_1105230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1105278 : List Nat := [4, 2, 3, 2, 1, 1, 1, 1, 6]
def baseStart_1105278 : Nat := 118140960795 + 1105278 * 2 ^ 59
def prefixEnd_1105278 : Nat := 4983230072969 + 3 ^ 40 * 1105278 * 2
def baseEnd_1105278 : Nat := 252239498151214145974189

theorem tailTrace_1105278 : CollatzResearch.WordTrace tailWord_1105278 prefixEnd_1105278 252239498151214145974189 := by
  unfold tailWord_1105278
  simp only [CollatzResearch.WordTrace]
  refine ⟨5039100061221755912380561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 26875200326516031532696325 5039100061221755912380561)
  ·
    refine ⟨3779325045916316934285421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5039100061221755912380561 3779325045916316934285421)
    ·
      refine ⟨1417246892218618850357033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3779325045916316934285421 1417246892218618850357033)
      ·
        refine ⟨1062935169163964137767775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1417246892218618850357033 1062935169163964137767775)
        ·
          refine ⟨1594402753745946206651663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1062935169163964137767775 1594402753745946206651663)
          ·
            refine ⟨2391604130618919309977495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1594402753745946206651663 2391604130618919309977495)
            ·
              refine ⟨3587406195928378964966243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2391604130618919309977495 3587406195928378964966243)
              ·
                refine ⟨5381109293892568447449365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3587406195928378964966243 5381109293892568447449365)
                ·
                  refine ⟨252239498151214145974189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5381109293892568447449365 252239498151214145974189)
                  ·
                    rfl

theorem cell21_1105278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 1, 1, 1, 6].length) (baseStart_1105278 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1105278 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1105278 prefixEnd_1105278 := by exact prefixLift 1105278
  have htrace : WordTrace (prefixWord ++ tailWord_1105278) baseStart_1105278 baseEnd_1105278 := by
    simpa [prefixWord, tailWord_1105278, baseEnd_1105278] using wordTrace_append hprefix tailTrace_1105278
  have hstable : (prefixWord ++ tailWord_1105278).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1105278).length < 2 ^ (prefixWord ++ tailWord_1105278).sum := by decide
  have hdescent : baseEnd_1105278 < baseStart_1105278 := by decide
  rcases family_descends (prefixWord ++ tailWord_1105278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1105340 : List Nat := [2, 2, 2, 4, 2, 1, 3, 2, 3]
def baseStart_1105340 : Nat := 118140960795 + 1105340 * 2 ^ 59
def prefixEnd_1105340 : Nat := 4983230072969 + 3 ^ 40 * 1105340 * 2
def baseEnd_1105340 : Nat := 252253647395915815940729

theorem tailTrace_1105340 : CollatzResearch.WordTrace tailWord_1105340 prefixEnd_1105340 252253647395915815940729 := by
  unfold tailWord_1105340
  simp only [CollatzResearch.WordTrace]
  refine ⟨20157530907774715943900737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26876707877032954591867649 20157530907774715943900737)
  ·
    refine ⟨15118148180831036957925553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20157530907774715943900737 15118148180831036957925553)
    ·
      refine ⟨11338611135623277718444165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15118148180831036957925553 11338611135623277718444165)
      ·
        refine ⟨2125989587929364572208281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11338611135623277718444165 2125989587929364572208281)
        ·
          refine ⟨1594492190947023429156211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2125989587929364572208281 1594492190947023429156211)
          ·
            refine ⟨2391738286420535143734317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1594492190947023429156211 2391738286420535143734317)
            ·
              refine ⟨896901857407700678900369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2391738286420535143734317 896901857407700678900369)
              ·
                refine ⟨672676393055775509175277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 896901857407700678900369 672676393055775509175277)
                ·
                  refine ⟨252253647395915815940729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 672676393055775509175277 252253647395915815940729)
                  ·
                    rfl

theorem cell21_1105340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 1, 3, 2, 3].length) (baseStart_1105340 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1105340 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1105340 prefixEnd_1105340 := by exact prefixLift 1105340
  have htrace : WordTrace (prefixWord ++ tailWord_1105340) baseStart_1105340 baseEnd_1105340 := by
    simpa [prefixWord, tailWord_1105340, baseEnd_1105340] using wordTrace_append hprefix tailTrace_1105340
  have hstable : (prefixWord ++ tailWord_1105340).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1105340).length < 2 ^ (prefixWord ++ tailWord_1105340).sum := by decide
  have hdescent : baseEnd_1105340 < baseStart_1105340 := by decide
  rcases family_descends (prefixWord ++ tailWord_1105340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1105346 : List Nat := [3, 5, 2, 1, 2, 1, 2, 1, 4]
def baseStart_1105346 : Nat := 118140960795 + 1105346 * 2 ^ 59
def prefixEnd_1105346 : Nat := 4983230072969 + 3 ^ 40 * 1105346 * 2
def baseEnd_1105346 : Nat := 252255016677661138840717

theorem tailTrace_1105346 : CollatzResearch.WordTrace tailWord_1105346 prefixEnd_1105346 252255016677661138840717 := by
  unfold tailWord_1105346
  simp only [CollatzResearch.WordTrace]
  refine ⟨10078820163381923728129973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26876853769018463275013261 10078820163381923728129973)
  ·
    refine ⟨944889390317055349512185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 10078820163381923728129973 944889390317055349512185)
    ·
      refine ⟨708667042737791512134139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 944889390317055349512185 708667042737791512134139)
      ·
        refine ⟨1063000564106687268201209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 708667042737791512134139 1063000564106687268201209)
        ·
          refine ⟨797250423080015451150907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1063000564106687268201209 797250423080015451150907)
          ·
            refine ⟨1195875634620023176726361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 797250423080015451150907 1195875634620023176726361)
            ·
              refine ⟨896906725965017382544771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1195875634620023176726361 896906725965017382544771)
              ·
                refine ⟨1345360088947526073817157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 896906725965017382544771 1345360088947526073817157)
                ·
                  refine ⟨252255016677661138840717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1345360088947526073817157 252255016677661138840717)
                  ·
                    rfl

theorem cell21_1105346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 2, 1, 2, 1, 4].length) (baseStart_1105346 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1105346 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1105346 prefixEnd_1105346 := by exact prefixLift 1105346
  have htrace : WordTrace (prefixWord ++ tailWord_1105346) baseStart_1105346 baseEnd_1105346 := by
    simpa [prefixWord, tailWord_1105346, baseEnd_1105346] using wordTrace_append hprefix tailTrace_1105346
  have hstable : (prefixWord ++ tailWord_1105346).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1105346).length < 2 ^ (prefixWord ++ tailWord_1105346).sum := by decide
  have hdescent : baseEnd_1105346 < baseStart_1105346 := by decide
  rcases family_descends (prefixWord ++ tailWord_1105346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1105393 : List Nat := [1, 2, 2, 2, 3, 11]
def baseStart_1105393 : Nat := 118140960795 + 1105393 * 2 ^ 59
def prefixEnd_1105393 : Nat := 4983230072969 + 3 ^ 40 * 1105393 * 2
def baseEnd_1105393 : Nat := 9343175656222203761381

theorem tailTrace_1105393 : CollatzResearch.WordTrace tailWord_1105393 prefixEnd_1105393 9343175656222203761381 := by
  unfold tailWord_1105393
  simp only [CollatzResearch.WordTrace]
  refine ⟨40316994884357421939480833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26877996589571614626320555 40316994884357421939480833)
  ·
    refine ⟨30237746163268066454610625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40316994884357421939480833 30237746163268066454610625)
    ·
      refine ⟨22678309622451049840957969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30237746163268066454610625 22678309622451049840957969)
      ·
        refine ⟨17008732216838287380718477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22678309622451049840957969 17008732216838287380718477)
        ·
          refine ⟨6378274581314357767769429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17008732216838287380718477 6378274581314357767769429)
          ·
            refine ⟨9343175656222203761381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 6378274581314357767769429 9343175656222203761381)
            ·
              rfl

theorem cell21_1105393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 11].length) (baseStart_1105393 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1105393 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1105393 prefixEnd_1105393 := by exact prefixLift 1105393
  have htrace : WordTrace (prefixWord ++ tailWord_1105393) baseStart_1105393 baseEnd_1105393 := by
    simpa [prefixWord, tailWord_1105393, baseEnd_1105393] using wordTrace_append hprefix tailTrace_1105393
  have hstable : (prefixWord ++ tailWord_1105393).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1105393).length < 2 ^ (prefixWord ++ tailWord_1105393).sum := by decide
  have hdescent : baseEnd_1105393 < baseStart_1105393 := by decide
  rcases family_descends (prefixWord ++ tailWord_1105393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1105478 : List Nat := [6, 1, 1, 1, 4, 1, 2, 5]
def baseStart_1105478 : Nat := 118140960795 + 1105478 * 2 ^ 59
def prefixEnd_1105478 : Nat := 4983230072969 + 3 ^ 40 * 1105478 * 2
def baseEnd_1105478 : Nat := 84095046958686080880149

theorem tailTrace_1105478 : CollatzResearch.WordTrace tailWord_1105478 prefixEnd_1105478 84095046958686080880149 := by
  unfold tailWord_1105478
  simp only [CollatzResearch.WordTrace]
  refine ⟨1260002971532796295510159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 26880063392699654304216725 1260002971532796295510159)
  ·
    refine ⟨1890004457299194443265239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1260002971532796295510159 1890004457299194443265239)
    ·
      refine ⟨2835006685948791664897859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1890004457299194443265239 2835006685948791664897859)
      ·
        refine ⟨4252510028923187497346789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2835006685948791664897859 4252510028923187497346789)
        ·
          refine ⟨797345630423097655752523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4252510028923187497346789 797345630423097655752523)
          ·
            refine ⟨1196018445634646483628785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 797345630423097655752523 1196018445634646483628785)
            ·
              refine ⟨897013834225984862721589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1196018445634646483628785 897013834225984862721589)
              ·
                refine ⟨84095046958686080880149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 897013834225984862721589 84095046958686080880149)
                ·
                  rfl

theorem cell21_1105478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 4, 1, 2, 5].length) (baseStart_1105478 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1105478 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1105478 prefixEnd_1105478 := by exact prefixLift 1105478
  have htrace : WordTrace (prefixWord ++ tailWord_1105478) baseStart_1105478 baseEnd_1105478 := by
    simpa [prefixWord, tailWord_1105478, baseEnd_1105478] using wordTrace_append hprefix tailTrace_1105478
  have hstable : (prefixWord ++ tailWord_1105478).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1105478).length < 2 ^ (prefixWord ++ tailWord_1105478).sum := by decide
  have hdescent : baseEnd_1105478 < baseStart_1105478 := by decide
  rcases family_descends (prefixWord ++ tailWord_1105478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1105531 : List Nat := [1, 1, 1, 1, 1, 4, 5, 3, 4]
def baseStart_1105531 : Nat := 118140960795 + 1105531 * 2 ^ 59
def prefixEnd_1105531 : Nat := 4983230072969 + 3 ^ 40 * 1105531 * 2
def baseEnd_1105531 : Nat := 252297236198141928257005

theorem tailTrace_1105531 : CollatzResearch.WordTrace tailWord_1105531 prefixEnd_1105531 252297236198141928257005 := by
  unfold tailWord_1105531
  simp only [CollatzResearch.WordTrace]
  refine ⟨40322028157857471508004447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26881352105238314338669631 40322028157857471508004447)
  ·
    refine ⟨60483042236786207262006671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40322028157857471508004447 60483042236786207262006671)
    ·
      refine ⟨90724563355179310893010007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60483042236786207262006671 90724563355179310893010007)
      ·
        refine ⟨136086845032768966339515011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90724563355179310893010007 136086845032768966339515011)
        ·
          refine ⟨204130267549153449509272517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 136086845032768966339515011 204130267549153449509272517)
          ·
            refine ⟨38274425165466271782988597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 204130267549153449509272517 38274425165466271782988597)
            ·
              refine ⟨3588227359262462979655181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 38274425165466271782988597 3588227359262462979655181)
              ·
                refine ⟨1345585259723423617370693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3588227359262462979655181 1345585259723423617370693)
                ·
                  refine ⟨252297236198141928257005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1345585259723423617370693 252297236198141928257005)
                  ·
                    rfl

theorem cell21_1105531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 5, 3, 4].length) (baseStart_1105531 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1105531 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1105531 prefixEnd_1105531 := by exact prefixLift 1105531
  have htrace : WordTrace (prefixWord ++ tailWord_1105531) baseStart_1105531 baseEnd_1105531 := by
    simpa [prefixWord, tailWord_1105531, baseEnd_1105531] using wordTrace_append hprefix tailTrace_1105531
  have hstable : (prefixWord ++ tailWord_1105531).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1105531).length < 2 ^ (prefixWord ++ tailWord_1105531).sum := by decide
  have hdescent : baseEnd_1105531 < baseStart_1105531 := by decide
  rcases family_descends (prefixWord ++ tailWord_1105531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1105545 : List Nat := [1, 2, 1, 1, 4, 1, 4, 7]
def baseStart_1105545 : Nat := 118140960795 + 1105545 * 2 ^ 59
def prefixEnd_1105545 : Nat := 4983230072969 + 3 ^ 40 * 1105545 * 2
def baseEnd_1105545 : Nat := 84100143729627005007881

theorem tailTrace_1105545 : CollatzResearch.WordTrace tailWord_1105545 prefixEnd_1105545 84100143729627005007881 := by
  unfold tailWord_1105545
  simp only [CollatzResearch.WordTrace]
  refine ⟨40322538779806751899014089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26881692519871167932676059 40322538779806751899014089)
  ·
    refine ⟨30241904084855063924260567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40322538779806751899014089 30241904084855063924260567)
    ·
      refine ⟨45362856127282595886390851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30241904084855063924260567 45362856127282595886390851)
      ·
        refine ⟨68044284190923893829586277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45362856127282595886390851 68044284190923893829586277)
        ·
          refine ⟨12758303285798230093047427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 68044284190923893829586277 12758303285798230093047427)
          ·
            refine ⟨19137454928697345139571141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12758303285798230093047427 19137454928697345139571141)
            ·
              refine ⟨3588272799130752213669589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19137454928697345139571141 3588272799130752213669589)
              ·
                refine ⟨84100143729627005007881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3588272799130752213669589 84100143729627005007881)
                ·
                  rfl

theorem cell21_1105545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 4, 7].length) (baseStart_1105545 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1105545 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1105545 prefixEnd_1105545 := by exact prefixLift 1105545
  have htrace : WordTrace (prefixWord ++ tailWord_1105545) baseStart_1105545 baseEnd_1105545 := by
    simpa [prefixWord, tailWord_1105545, baseEnd_1105545] using wordTrace_append hprefix tailTrace_1105545
  have hstable : (prefixWord ++ tailWord_1105545).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1105545).length < 2 ^ (prefixWord ++ tailWord_1105545).sum := by decide
  have hdescent : baseEnd_1105545 < baseStart_1105545 := by decide
  rcases family_descends (prefixWord ++ tailWord_1105545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1105697 : List Nat := [1, 2, 3, 2, 1, 3, 1, 8]
def baseStart_1105697 : Nat := 118140960795 + 1105697 * 2 ^ 59
def prefixEnd_1105697 : Nat := 4983230072969 + 3 ^ 40 * 1105697 * 2
def baseEnd_1105697 : Nat := 84111706553254176163333

theorem tailTrace_1105697 : CollatzResearch.WordTrace tailWord_1105697 prefixEnd_1105697 84111706553254176163333 := by
  unfold tailWord_1105697
  simp only [CollatzResearch.WordTrace]
  refine ⟨40328082675256081858547345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26885388450170721239031563 40328082675256081858547345)
  ·
    refine ⟨30246062006442061393910509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40328082675256081858547345 30246062006442061393910509)
    ·
      refine ⟨11342273252415773022716441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30246062006442061393910509 11342273252415773022716441)
      ·
        refine ⟨8506704939311829767037331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11342273252415773022716441 8506704939311829767037331)
        ·
          refine ⟨12760057408967744650555997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8506704939311829767037331 12760057408967744650555997)
          ·
            refine ⟨4785021528362904243958499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12760057408967744650555997 4785021528362904243958499)
            ·
              refine ⟨7177532292544356365937749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4785021528362904243958499 7177532292544356365937749)
              ·
                refine ⟨84111706553254176163333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7177532292544356365937749 84111706553254176163333)
                ·
                  rfl

theorem cell21_1105697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 1, 8].length) (baseStart_1105697 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1105697 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1105697 prefixEnd_1105697 := by exact prefixLift 1105697
  have htrace : WordTrace (prefixWord ++ tailWord_1105697) baseStart_1105697 baseEnd_1105697 := by
    simpa [prefixWord, tailWord_1105697, baseEnd_1105697] using wordTrace_append hprefix tailTrace_1105697
  have hstable : (prefixWord ++ tailWord_1105697).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1105697).length < 2 ^ (prefixWord ++ tailWord_1105697).sum := by decide
  have hdescent : baseEnd_1105697 < baseStart_1105697 := by decide
  rcases family_descends (prefixWord ++ tailWord_1105697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1105700 : List Nat := [2, 3, 1, 3, 2, 2, 1, 3, 4]
def baseStart_1105700 : Nat := 118140960795 + 1105700 * 2 ^ 59
def prefixEnd_1105700 : Nat := 4983230072969 + 3 ^ 40 * 1105700 * 2
def baseEnd_1105700 : Nat := 252335804300635189939993

theorem tailTrace_1105700 : CollatzResearch.WordTrace tailWord_1105700 prefixEnd_1105700 252335804300635189939993 := by
  unfold tailWord_1105700
  simp only [CollatzResearch.WordTrace]
  refine ⟨20164096047122606685453277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26885461396163475580604369 20164096047122606685453277)
  ·
    refine ⟨7561536017670977507044979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20164096047122606685453277 7561536017670977507044979)
    ·
      refine ⟨11342304026506466260567469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7561536017670977507044979 11342304026506466260567469)
      ·
        refine ⟨4253364009939924847712801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11342304026506466260567469 4253364009939924847712801)
        ·
          refine ⟨3190023007454943635784601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4253364009939924847712801 3190023007454943635784601)
          ·
            refine ⟨2392517255591207726838451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3190023007454943635784601 2392517255591207726838451)
            ·
              refine ⟨3588775883386811590257677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2392517255591207726838451 3588775883386811590257677)
              ·
                refine ⟨1345790956270054346346629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3588775883386811590257677 1345790956270054346346629)
                ·
                  refine ⟨252335804300635189939993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1345790956270054346346629 252335804300635189939993)
                  ·
                    rfl

theorem cell21_1105700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 2, 1, 3, 4].length) (baseStart_1105700 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1105700 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1105700 prefixEnd_1105700 := by exact prefixLift 1105700
  have htrace : WordTrace (prefixWord ++ tailWord_1105700) baseStart_1105700 baseEnd_1105700 := by
    simpa [prefixWord, tailWord_1105700, baseEnd_1105700] using wordTrace_append hprefix tailTrace_1105700
  have hstable : (prefixWord ++ tailWord_1105700).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1105700).length < 2 ^ (prefixWord ++ tailWord_1105700).sum := by decide
  have hdescent : baseEnd_1105700 < baseStart_1105700 := by decide
  rcases family_descends (prefixWord ++ tailWord_1105700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1105734 : List Nat := [6, 1, 1, 2, 1, 2, 2, 2, 4]
def baseStart_1105734 : Nat := 118140960795 + 1105734 * 2 ^ 59
def prefixEnd_1105734 : Nat := 4983230072969 + 3 ^ 40 * 1105734 * 2
def baseEnd_1105734 : Nat := 252343563563858686373257

theorem tailTrace_1105734 : CollatzResearch.WordTrace tailWord_1105734 prefixEnd_1105734 252343563563858686373257 := by
  unfold tailWord_1105734
  simp only [CollatzResearch.WordTrace]
  refine ⟨1260294755503813661801383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 26886288117414691451762837 1260294755503813661801383)
  ·
    refine ⟨1890442133255720492702075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1260294755503813661801383 1890442133255720492702075)
    ·
      refine ⟨2835663199883580739053113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1890442133255720492702075 2835663199883580739053113)
      ·
        refine ⟨2126747399912685554289835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2835663199883580739053113 2126747399912685554289835)
        ·
          refine ⟨3190121099869028331434753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2126747399912685554289835 3190121099869028331434753)
          ·
            refine ⟨2392590824901771248576065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3190121099869028331434753 2392590824901771248576065)
            ·
              refine ⟨1794443118676328436432049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2392590824901771248576065 1794443118676328436432049)
              ·
                refine ⟨1345832339007246327324037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1794443118676328436432049 1345832339007246327324037)
                ·
                  refine ⟨252343563563858686373257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1345832339007246327324037 252343563563858686373257)
                  ·
                    rfl

theorem cell21_1105734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 2, 2, 2, 4].length) (baseStart_1105734 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1105734 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1105734 prefixEnd_1105734 := by exact prefixLift 1105734
  have htrace : WordTrace (prefixWord ++ tailWord_1105734) baseStart_1105734 baseEnd_1105734 := by
    simpa [prefixWord, tailWord_1105734, baseEnd_1105734] using wordTrace_append hprefix tailTrace_1105734
  have hstable : (prefixWord ++ tailWord_1105734).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1105734).length < 2 ^ (prefixWord ++ tailWord_1105734).sum := by decide
  have hdescent : baseEnd_1105734 < baseStart_1105734 := by decide
  rcases family_descends (prefixWord ++ tailWord_1105734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1105759 : List Nat := [1, 1, 2, 3, 1, 4, 2, 3, 4]
def baseStart_1105759 : Nat := 118140960795 + 1105759 * 2 ^ 59
def prefixEnd_1105759 : Nat := 4983230072969 + 3 ^ 40 * 1105759 * 2
def baseEnd_1105759 : Nat := 252349268904464198456539

theorem tailTrace_1105759 : CollatzResearch.WordTrace tailWord_1105759 prefixEnd_1105759 252349268904464198456539 := by
  unfold tailWord_1105759
  simp only [CollatzResearch.WordTrace]
  refine ⟨40330344001031466447304331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26886896000687644298202887 40330344001031466447304331)
  ·
    refine ⟨60495516001547199670956497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40330344001031466447304331 60495516001547199670956497)
    ·
      refine ⟨45371637001160399753217373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60495516001547199670956497 45371637001160399753217373)
      ·
        refine ⟨17014363875435149907456515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 45371637001160399753217373 17014363875435149907456515)
        ·
          refine ⟨25521545813152724861184773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17014363875435149907456515 25521545813152724861184773)
          ·
            refine ⟨4785289839966135911472145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 25521545813152724861184773 4785289839966135911472145)
            ·
              refine ⟨3588967379974601933604109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4785289839966135911472145 3588967379974601933604109)
              ·
                refine ⟨1345862767490475725101541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3588967379974601933604109 1345862767490475725101541)
                ·
                  refine ⟨252349268904464198456539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1345862767490475725101541 252349268904464198456539)
                  ·
                    rfl

theorem cell21_1105759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 2, 3, 4].length) (baseStart_1105759 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1105759 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1105759 prefixEnd_1105759 := by exact prefixLift 1105759
  have htrace : WordTrace (prefixWord ++ tailWord_1105759) baseStart_1105759 baseEnd_1105759 := by
    simpa [prefixWord, tailWord_1105759, baseEnd_1105759] using wordTrace_append hprefix tailTrace_1105759
  have hstable : (prefixWord ++ tailWord_1105759).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1105759).length < 2 ^ (prefixWord ++ tailWord_1105759).sum := by decide
  have hdescent : baseEnd_1105759 < baseStart_1105759 := by decide
  rcases family_descends (prefixWord ++ tailWord_1105759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1105773 : List Nat := [1, 5, 1, 1, 1, 1, 2, 9]
def baseStart_1105773 : Nat := 118140960795 + 1105773 * 2 ^ 59
def prefixEnd_1105773 : Nat := 4983230072969 + 3 ^ 40 * 1105773 * 2
def baseEnd_1105773 : Nat := 84117487965067761741059

theorem tailTrace_1105773 : CollatzResearch.WordTrace tailWord_1105773 prefixEnd_1105773 84117487965067761741059 := by
  unfold tailWord_1105773
  simp only [CollatzResearch.WordTrace]
  refine ⟨40330854622980746838313973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26887236415320497892209315 40330854622980746838313973)
  ·
    refine ⟨3781017620904445016091935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 40330854622980746838313973 3781017620904445016091935)
    ·
      refine ⟨5671526431356667524137903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3781017620904445016091935 5671526431356667524137903)
      ·
        refine ⟨8507289647035001286206855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5671526431356667524137903 8507289647035001286206855)
        ·
          refine ⟨12760934470552501929310283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8507289647035001286206855 12760934470552501929310283)
          ·
            refine ⟨19141401705828752893965425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12760934470552501929310283 19141401705828752893965425)
            ·
              refine ⟨14356051279371564670474069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19141401705828752893965425 14356051279371564670474069)
              ·
                refine ⟨84117487965067761741059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 14356051279371564670474069 84117487965067761741059)
                ·
                  rfl

theorem cell21_1105773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 2, 9].length) (baseStart_1105773 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1105773 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1105773 prefixEnd_1105773 := by exact prefixLift 1105773
  have htrace : WordTrace (prefixWord ++ tailWord_1105773) baseStart_1105773 baseEnd_1105773 := by
    simpa [prefixWord, tailWord_1105773, baseEnd_1105773] using wordTrace_append hprefix tailTrace_1105773
  have hstable : (prefixWord ++ tailWord_1105773).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1105773).length < 2 ^ (prefixWord ++ tailWord_1105773).sum := by decide
  have hdescent : baseEnd_1105773 < baseStart_1105773 := by decide
  rcases family_descends (prefixWord ++ tailWord_1105773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1105787 : List Nat := [1, 1, 1, 1, 1, 5, 1, 1, 9]
def baseStart_1105787 : Nat := 118140960795 + 1105787 * 2 ^ 59
def prefixEnd_1105787 : Nat := 4983230072969 + 3 ^ 40 * 1105787 * 2
def baseEnd_1105787 : Nat := 252355658885942371989815

theorem tailTrace_1105787 : CollatzResearch.WordTrace tailWord_1105787 prefixEnd_1105787 252355658885942371989815 := by
  unfold tailWord_1105787
  simp only [CollatzResearch.WordTrace]
  refine ⟨40331365244930027229323615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26887576829953351486215743 40331365244930027229323615)
  ·
    refine ⟨60497047867395040843985423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40331365244930027229323615 60497047867395040843985423)
    ·
      refine ⟨90745571801092561265978135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60497047867395040843985423 90745571801092561265978135)
      ·
        refine ⟨136118357701638841898967203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90745571801092561265978135 136118357701638841898967203)
        ·
          refine ⟨204177536552458262848450805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 136118357701638841898967203 204177536552458262848450805)
          ·
            refine ⟨19141644051792962142042263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 204177536552458262848450805 19141644051792962142042263)
            ·
              refine ⟨28712466077689443213063395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19141644051792962142042263 28712466077689443213063395)
              ·
                refine ⟨43068699116534164819595093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28712466077689443213063395 43068699116534164819595093)
                ·
                  refine ⟨252355658885942371989815, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 43068699116534164819595093 252355658885942371989815)
                  ·
                    rfl

theorem cell21_1105787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 1, 9].length) (baseStart_1105787 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1105787 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1105787 prefixEnd_1105787 := by exact prefixLift 1105787
  have htrace : WordTrace (prefixWord ++ tailWord_1105787) baseStart_1105787 baseEnd_1105787 := by
    simpa [prefixWord, tailWord_1105787, baseEnd_1105787] using wordTrace_append hprefix tailTrace_1105787
  have hstable : (prefixWord ++ tailWord_1105787).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1105787).length < 2 ^ (prefixWord ++ tailWord_1105787).sum := by decide
  have hdescent : baseEnd_1105787 < baseStart_1105787 := by decide
  rcases family_descends (prefixWord ++ tailWord_1105787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1105925 : List Nat := [1, 3, 1, 1, 2, 4, 3, 6]
def baseStart_1105925 : Nat := 118140960795 + 1105925 * 2 ^ 59
def prefixEnd_1105925 : Nat := 4983230072969 + 3 ^ 40 * 1105925 * 2
def baseEnd_1105925 : Nat := 84129050788694932896511

theorem tailTrace_1105925 : CollatzResearch.WordTrace tailWord_1105925 prefixEnd_1105925 84129050788694932896511 := by
  unfold tailWord_1105925
  simp only [CollatzResearch.WordTrace]
  refine ⟨40336398518430076797847229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26890932345620051198564819 40336398518430076797847229)
  ·
    refine ⟨15126149444411278799192711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40336398518430076797847229 15126149444411278799192711)
    ·
      refine ⟨22689224166616918198789067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15126149444411278799192711 22689224166616918198789067)
      ·
        refine ⟨34033836249925377298183601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22689224166616918198789067 34033836249925377298183601)
        ·
          refine ⟨25525377187444032973637701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34033836249925377298183601 25525377187444032973637701)
          ·
            refine ⟨4786008222645756182557069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 25525377187444032973637701 4786008222645756182557069)
            ·
              refine ⟨1794753083492158568458901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4786008222645756182557069 1794753083492158568458901)
              ·
                refine ⟨84129050788694932896511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1794753083492158568458901 84129050788694932896511)
                ·
                  rfl

theorem cell21_1105925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 3, 6].length) (baseStart_1105925 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1105925 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1105925 prefixEnd_1105925 := by exact prefixLift 1105925
  have htrace : WordTrace (prefixWord ++ tailWord_1105925) baseStart_1105925 baseEnd_1105925 := by
    simpa [prefixWord, tailWord_1105925, baseEnd_1105925] using wordTrace_append hprefix tailTrace_1105925
  have hstable : (prefixWord ++ tailWord_1105925).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1105925).length < 2 ^ (prefixWord ++ tailWord_1105925).sum := by decide
  have hdescent : baseEnd_1105925 < baseStart_1105925 := by decide
  rcases family_descends (prefixWord ++ tailWord_1105925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1105939 : List Nat := [1, 1, 1, 2, 1, 4, 3, 1, 7]
def baseStart_1105939 : Nat := 118140960795 + 1105939 * 2 ^ 59
def prefixEnd_1105939 : Nat := 4983230072969 + 3 ^ 40 * 1105939 * 2
def baseEnd_1105939 : Nat := 252390347356823885456171

theorem tailTrace_1105939 : CollatzResearch.WordTrace tailWord_1105939 prefixEnd_1105939 252390347356823885456171 := by
  unfold tailWord_1105939
  simp only [CollatzResearch.WordTrace]
  refine ⟨40336909140379357188856871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26891272760252904792571247 40336909140379357188856871)
  ·
    refine ⟨60505363710569035783285307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40336909140379357188856871 60505363710569035783285307)
    ·
      refine ⟨90758045565853553674927961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60505363710569035783285307 90758045565853553674927961)
      ·
        refine ⟨68068534174390165256195971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 90758045565853553674927961 68068534174390165256195971)
        ·
          refine ⟨102102801261585247884293957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68068534174390165256195971 102102801261585247884293957)
          ·
            refine ⟨19144275236547233978305117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 102102801261585247884293957 19144275236547233978305117)
            ·
              refine ⟨7179103213705212741864419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19144275236547233978305117 7179103213705212741864419)
              ·
                refine ⟨10768654820557819112796629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7179103213705212741864419 10768654820557819112796629)
                ·
                  refine ⟨252390347356823885456171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10768654820557819112796629 252390347356823885456171)
                  ·
                    rfl

theorem cell21_1105939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 3, 1, 7].length) (baseStart_1105939 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1105939 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1105939 prefixEnd_1105939 := by exact prefixLift 1105939
  have htrace : WordTrace (prefixWord ++ tailWord_1105939) baseStart_1105939 baseEnd_1105939 := by
    simpa [prefixWord, tailWord_1105939, baseEnd_1105939] using wordTrace_append hprefix tailTrace_1105939
  have hstable : (prefixWord ++ tailWord_1105939).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1105939).length < 2 ^ (prefixWord ++ tailWord_1105939).sum := by decide
  have hdescent : baseEnd_1105939 < baseStart_1105939 := by decide
  rcases family_descends (prefixWord ++ tailWord_1105939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1105973 : List Nat := [1, 3, 3, 1, 1, 1, 4, 4, 3]
def baseStart_1105973 : Nat := 118140960795 + 1105973 * 2 ^ 59
def prefixEnd_1105973 : Nat := 4983230072969 + 3 ^ 40 * 1105973 * 2
def baseEnd_1105973 : Nat := 252398106620047381889435

theorem tailTrace_1105973 : CollatzResearch.WordTrace tailWord_1105973 prefixEnd_1105973 252398106620047381889435 := by
  unfold tailWord_1105973
  simp only [CollatzResearch.WordTrace]
  refine ⟨40338149222256180995594573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26892099481504120663729715 40338149222256180995594573)
  ·
    refine ⟨15126805958346067873347965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40338149222256180995594573 15126805958346067873347965)
    ·
      refine ⟨5672552234379775452505487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15126805958346067873347965 5672552234379775452505487)
      ·
        refine ⟨8508828351569663178758231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5672552234379775452505487 8508828351569663178758231)
        ·
          refine ⟨12763242527354494768137347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8508828351569663178758231 12763242527354494768137347)
          ·
            refine ⟨19144863791031742152206021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12763242527354494768137347 19144863791031742152206021)
            ·
              refine ⟨3589661960818451653538629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19144863791031742152206021 3589661960818451653538629)
              ·
                refine ⟨673061617653459685038493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3589661960818451653538629 673061617653459685038493)
                ·
                  refine ⟨252398106620047381889435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 673061617653459685038493 252398106620047381889435)
                  ·
                    rfl

theorem cell21_1105973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 4, 4, 3].length) (baseStart_1105973 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1105973 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1105973 prefixEnd_1105973 := by exact prefixLift 1105973
  have htrace : WordTrace (prefixWord ++ tailWord_1105973) baseStart_1105973 baseEnd_1105973 := by
    simpa [prefixWord, tailWord_1105973, baseEnd_1105973] using wordTrace_append hprefix tailTrace_1105973
  have hstable : (prefixWord ++ tailWord_1105973).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1105973).length < 2 ^ (prefixWord ++ tailWord_1105973).sum := by decide
  have hdescent : baseEnd_1105973 < baseStart_1105973 := by decide
  rcases family_descends (prefixWord ++ tailWord_1105973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1106032 : List Nat := [2, 1, 1, 1, 5, 2, 3, 1, 5]
def baseStart_1106032 : Nat := 118140960795 + 1106032 * 2 ^ 59
def prefixEnd_1106032 : Nat := 4983230072969 + 3 ^ 40 * 1106032 * 2
def baseEnd_1106032 : Nat := 252411571223876390405981

theorem tailTrace_1106032 : CollatzResearch.WordTrace tailWord_1106032 prefixEnd_1106032 252411571223876390405981 := by
  unfold tailWord_1106032
  simp only [CollatzResearch.WordTrace]
  refine ⟨20170150564521217035996175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26893534086028289381328233 20170150564521217035996175)
  ·
    refine ⟨30255225846781825553994263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20170150564521217035996175 30255225846781825553994263)
    ·
      refine ⟨45382838770172738330991395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30255225846781825553994263 45382838770172738330991395)
      ·
        refine ⟨68074258155259107496487093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45382838770172738330991395 68074258155259107496487093)
        ·
          refine ⟨6381961702055541327795665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 68074258155259107496487093 6381961702055541327795665)
          ·
            refine ⟨4786471276541655995846749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6381961702055541327795665 4786471276541655995846749)
            ·
              refine ⟨1794926728703120998442531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4786471276541655995846749 1794926728703120998442531)
              ·
                refine ⟨2692390093054681497663797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1794926728703120998442531 2692390093054681497663797)
                ·
                  refine ⟨252411571223876390405981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2692390093054681497663797 252411571223876390405981)
                  ·
                    rfl

theorem cell21_1106032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 3, 1, 5].length) (baseStart_1106032 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1106032 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1106032 prefixEnd_1106032 := by exact prefixLift 1106032
  have htrace : WordTrace (prefixWord ++ tailWord_1106032) baseStart_1106032 baseEnd_1106032 := by
    simpa [prefixWord, tailWord_1106032, baseEnd_1106032] using wordTrace_append hprefix tailTrace_1106032
  have hstable : (prefixWord ++ tailWord_1106032).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1106032).length < 2 ^ (prefixWord ++ tailWord_1106032).sum := by decide
  have hdescent : baseEnd_1106032 < baseStart_1106032 := by decide
  rcases family_descends (prefixWord ++ tailWord_1106032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1106122 : List Nat := [3, 1, 2, 1, 3, 1, 2, 2, 6]
def baseStart_1106122 : Nat := 118140960795 + 1106122 * 2 ^ 59
def prefixEnd_1106122 : Nat := 4983230072969 + 3 ^ 40 * 1106122 * 2
def baseEnd_1106122 : Nat := 252432110450056233905797

theorem tailTrace_1106122 : CollatzResearch.WordTrace tailWord_1106122 prefixEnd_1106122 252432110450056233905797 := by
  unfold tailWord_1106122
  simp only [CollatzResearch.WordTrace]
  refine ⟨10085895924679094860692155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26895722465810919628512413 10085895924679094860692155)
  ·
    refine ⟨15128843887018642291038233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10085895924679094860692155 15128843887018642291038233)
    ·
      refine ⟨11346632915263981718278675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15128843887018642291038233 11346632915263981718278675)
      ·
        refine ⟨17019949372895972577418013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11346632915263981718278675 17019949372895972577418013)
        ·
          refine ⟨6382481014835989716531755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17019949372895972577418013 6382481014835989716531755)
          ·
            refine ⟨9573721522253984574797633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6382481014835989716531755 9573721522253984574797633)
            ·
              refine ⟨7180291141690488431098225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9573721522253984574797633 7180291141690488431098225)
              ·
                refine ⟨5385218356267866323323669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7180291141690488431098225 5385218356267866323323669)
                ·
                  refine ⟨252432110450056233905797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5385218356267866323323669 252432110450056233905797)
                  ·
                    rfl

theorem cell21_1106122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 2, 2, 6].length) (baseStart_1106122 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1106122 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1106122 prefixEnd_1106122 := by exact prefixLift 1106122
  have htrace : WordTrace (prefixWord ++ tailWord_1106122) baseStart_1106122 baseEnd_1106122 := by
    simpa [prefixWord, tailWord_1106122, baseEnd_1106122] using wordTrace_append hprefix tailTrace_1106122
  have hstable : (prefixWord ++ tailWord_1106122).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1106122).length < 2 ^ (prefixWord ++ tailWord_1106122).sum := by decide
  have hdescent : baseEnd_1106122 < baseStart_1106122 := by decide
  rcases family_descends (prefixWord ++ tailWord_1106122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1106170 : List Nat := [3, 1, 1, 1, 1, 7, 2, 5]
def baseStart_1106170 : Nat := 118140960795 + 1106170 * 2 ^ 59
def prefixEnd_1106170 : Nat := 4983230072969 + 3 ^ 40 * 1106170 * 2
def baseEnd_1106170 : Nat := 84147688234672939035233

theorem tailTrace_1106170 : CollatzResearch.WordTrace tailWord_1106170 prefixEnd_1106170 84147688234672939035233 := by
  unfold tailWord_1106170
  simp only [CollatzResearch.WordTrace]
  refine ⟨10086333600635620910128991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26896889601694989093677309 10086333600635620910128991)
  ·
    refine ⟨15129500400953431365193487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10086333600635620910128991 15129500400953431365193487)
    ·
      refine ⟨22694250601430147047790231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15129500400953431365193487 22694250601430147047790231)
      ·
        refine ⟨34041375902145220571685347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22694250601430147047790231 34041375902145220571685347)
        ·
          refine ⟨51062063853217830857528021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34041375902145220571685347 51062063853217830857528021)
          ·
            refine ⟨1196767121559792910723313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 51062063853217830857528021 1196767121559792910723313)
            ·
              refine ⟨897575341169844683042485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1196767121559792910723313 897575341169844683042485)
              ·
                refine ⟨84147688234672939035233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 897575341169844683042485 84147688234672939035233)
                ·
                  rfl

theorem cell21_1106170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 7, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 7, 2, 5].length) (baseStart_1106170 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1106170 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1106170 prefixEnd_1106170 := by exact prefixLift 1106170
  have htrace : WordTrace (prefixWord ++ tailWord_1106170) baseStart_1106170 baseEnd_1106170 := by
    simpa [prefixWord, tailWord_1106170, baseEnd_1106170] using wordTrace_append hprefix tailTrace_1106170
  have hstable : (prefixWord ++ tailWord_1106170).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1106170).length < 2 ^ (prefixWord ++ tailWord_1106170).sum := by decide
  have hdescent : baseEnd_1106170 < baseStart_1106170 := by decide
  rcases family_descends (prefixWord ++ tailWord_1106170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1106305 : List Nat := [1, 2, 4, 3, 1, 2, 8]
def baseStart_1106305 : Nat := 118140960795 + 1106305 * 2 ^ 59
def prefixEnd_1106305 : Nat := 4983230072969 + 3 ^ 40 * 1106305 * 2
def baseEnd_1106305 : Nat := 28052652615920953595047

theorem tailTrace_1106305 : CollatzResearch.WordTrace tailWord_1106305 prefixEnd_1106305 28052652615920953595047 := by
  unfold tailWord_1106305
  simp only [CollatzResearch.WordTrace]
  refine ⟨40350258257053401696680369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26900172171368934464453579 40350258257053401696680369)
  ·
    refine ⟨30262693692790051272510277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40350258257053401696680369 30262693692790051272510277)
    ·
      refine ⟨5674255067398134613595677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 30262693692790051272510277 5674255067398134613595677)
      ·
        refine ⟨2127845650274300480098379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5674255067398134613595677 2127845650274300480098379)
        ·
          refine ⟨3191768475411450720147569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2127845650274300480098379 3191768475411450720147569)
          ·
            refine ⟨2393826356558588040110677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3191768475411450720147569 2393826356558588040110677)
            ·
              refine ⟨28052652615920953595047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2393826356558588040110677 28052652615920953595047)
              ·
                rfl

theorem cell21_1106305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 2, 8].length) (baseStart_1106305 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1106305 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1106305 prefixEnd_1106305 := by exact prefixLift 1106305
  have htrace : WordTrace (prefixWord ++ tailWord_1106305) baseStart_1106305 baseEnd_1106305 := by
    simpa [prefixWord, tailWord_1106305, baseEnd_1106305] using wordTrace_append hprefix tailTrace_1106305
  have hstable : (prefixWord ++ tailWord_1106305).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1106305).length < 2 ^ (prefixWord ++ tailWord_1106305).sum := by decide
  have hdescent : baseEnd_1106305 < baseStart_1106305 := by decide
  rcases family_descends (prefixWord ++ tailWord_1106305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1106353 : List Nat := [1, 2, 2, 4, 1, 2, 3, 3, 3]
def baseStart_1106353 : Nat := 118140960795 + 1106353 * 2 ^ 59
def prefixEnd_1106353 : Nat := 4983230072969 + 3 ^ 40 * 1106353 * 2
def baseEnd_1106353 : Nat := 252484827797251165555325

theorem tailTrace_1106353 : CollatzResearch.WordTrace tailWord_1106353 prefixEnd_1106353 252484827797251165555325 := by
  unfold tailWord_1106353
  simp only [CollatzResearch.WordTrace]
  refine ⟨40352008960879505894427713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26901339307253003929618475 40352008960879505894427713)
  ·
    refine ⟨30264006720659629420820785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40352008960879505894427713 30264006720659629420820785)
    ·
      refine ⟨22698005040494722065615589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30264006720659629420820785 22698005040494722065615589)
      ·
        refine ⟨4255875945092760387302923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 22698005040494722065615589 4255875945092760387302923)
        ·
          refine ⟨6383813917639140580954385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4255875945092760387302923 6383813917639140580954385)
          ·
            refine ⟨4787860438229355435715789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6383813917639140580954385 4787860438229355435715789)
            ·
              refine ⟨1795447664336008288393421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4787860438229355435715789 1795447664336008288393421)
              ·
                refine ⟨673292874126003108147533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1795447664336008288393421 673292874126003108147533)
                ·
                  refine ⟨252484827797251165555325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 673292874126003108147533 252484827797251165555325)
                  ·
                    rfl

theorem cell21_1106353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 3, 3, 3].length) (baseStart_1106353 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1106353 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1106353 prefixEnd_1106353 := by exact prefixLift 1106353
  have htrace : WordTrace (prefixWord ++ tailWord_1106353) baseStart_1106353 baseEnd_1106353 := by
    simpa [prefixWord, tailWord_1106353, baseEnd_1106353] using wordTrace_append hprefix tailTrace_1106353
  have hstable : (prefixWord ++ tailWord_1106353).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1106353).length < 2 ^ (prefixWord ++ tailWord_1106353).sum := by decide
  have hdescent : baseEnd_1106353 < baseStart_1106353 := by decide
  rcases family_descends (prefixWord ++ tailWord_1106353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1106356 : List Nat := [2, 5, 2, 2, 2, 1, 7]
def baseStart_1106356 : Nat := 118140960795 + 1106356 * 2 ^ 59
def prefixEnd_1106356 : Nat := 4983230072969 + 3 ^ 40 * 1106356 * 2
def baseEnd_1106356 : Nat := 28053945826458203000591

theorem tailTrace_1106356 : CollatzResearch.WordTrace tailWord_1106356 prefixEnd_1106356 28053945826458203000591 := by
  unfold tailWord_1106356
  simp only [CollatzResearch.WordTrace]
  refine ⟨20176059189934318703393461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26901412253245758271191281 20176059189934318703393461)
  ·
    refine ⟨1891505549056342378443137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 20176059189934318703393461 1891505549056342378443137)
    ·
      refine ⟨1418629161792256783832353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1891505549056342378443137 1418629161792256783832353)
      ·
        refine ⟨1063971871344192587874265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1418629161792256783832353 1063971871344192587874265)
        ·
          refine ⟨797978903508144440905699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1063971871344192587874265 797978903508144440905699)
          ·
            refine ⟨1196968355262216661358549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 797978903508144440905699 1196968355262216661358549)
            ·
              refine ⟨28053945826458203000591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1196968355262216661358549 28053945826458203000591)
              ·
                rfl

theorem cell21_1106356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 2, 1, 7].length) (baseStart_1106356 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1106356 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1106356 prefixEnd_1106356 := by exact prefixLift 1106356
  have htrace : WordTrace (prefixWord ++ tailWord_1106356) baseStart_1106356 baseEnd_1106356 := by
    simpa [prefixWord, tailWord_1106356, baseEnd_1106356] using wordTrace_append hprefix tailTrace_1106356
  have hstable : (prefixWord ++ tailWord_1106356).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1106356).length < 2 ^ (prefixWord ++ tailWord_1106356).sum := by decide
  have hdescent : baseEnd_1106356 < baseStart_1106356 := by decide
  rcases family_descends (prefixWord ++ tailWord_1106356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1106409 : List Nat := [1, 2, 1, 1, 1, 2, 1, 6, 6]
def baseStart_1106409 : Nat := 118140960795 + 1106409 * 2 ^ 59
def prefixEnd_1106409 : Nat := 4983230072969 + 3 ^ 40 * 1106409 * 2
def baseEnd_1106409 : Nat := 252497607760207512621877

theorem tailTrace_1106409 : CollatzResearch.WordTrace tailWord_1106409 prefixEnd_1106409 252497607760207512621877 := by
  unfold tailWord_1106409
  simp only [CollatzResearch.WordTrace]
  refine ⟨40354051448676627458466281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26902700965784418305644187 40354051448676627458466281)
  ·
    refine ⟨30265538586507470593849711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40354051448676627458466281 30265538586507470593849711)
    ·
      refine ⟨45398307879761205890774567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30265538586507470593849711 45398307879761205890774567)
      ·
        refine ⟨68097461819641808836161851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45398307879761205890774567 68097461819641808836161851)
        ·
          refine ⟨102146192729462713254242777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68097461819641808836161851 102146192729462713254242777)
          ·
            refine ⟨76609644547097034940682083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 102146192729462713254242777 76609644547097034940682083)
            ·
              refine ⟨114914466820645552411023125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 76609644547097034940682083 114914466820645552411023125)
              ·
                refine ⟨5386615632217760269266709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 114914466820645552411023125 5386615632217760269266709)
                ·
                  refine ⟨252497607760207512621877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5386615632217760269266709 252497607760207512621877)
                  ·
                    rfl

theorem cell21_1106409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 6, 6].length) (baseStart_1106409 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1106409 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1106409 prefixEnd_1106409 := by exact prefixLift 1106409
  have htrace : WordTrace (prefixWord ++ tailWord_1106409) baseStart_1106409 baseEnd_1106409 := by
    simpa [prefixWord, tailWord_1106409, baseEnd_1106409] using wordTrace_append hprefix tailTrace_1106409
  have hstable : (prefixWord ++ tailWord_1106409).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1106409).length < 2 ^ (prefixWord ++ tailWord_1106409).sum := by decide
  have hdescent : baseEnd_1106409 < baseStart_1106409 := by decide
  rcases family_descends (prefixWord ++ tailWord_1106409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1106412 : List Nat := [2, 2, 1, 1, 2, 1, 4, 5, 3]
def baseStart_1106412 : Nat := 118140960795 + 1106412 * 2 ^ 59
def prefixEnd_1106412 : Nat := 4983230072969 + 3 ^ 40 * 1106412 * 2
def baseEnd_1106412 : Nat := 252498292401080174071871

theorem tailTrace_1106412 : CollatzResearch.WordTrace tailWord_1106412 prefixEnd_1106412 252498292401080174071871 := by
  unfold tailWord_1106412
  simp only [CollatzResearch.WordTrace]
  refine ⟨20177080433832879485412745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26902773911777172647216993 20177080433832879485412745)
  ·
    refine ⟨15132810325374659614059559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20177080433832879485412745 15132810325374659614059559)
    ·
      refine ⟨22699215488061989421089339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15132810325374659614059559 22699215488061989421089339)
      ·
        refine ⟨34048823232092984131634009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22699215488061989421089339 34048823232092984131634009)
        ·
          refine ⟨25536617424069738098725507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34048823232092984131634009 25536617424069738098725507)
          ·
            refine ⟨38304926136104607148088261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25536617424069738098725507 38304926136104607148088261)
            ·
              refine ⟨7182173650519613840266549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 38304926136104607148088261 7182173650519613840266549)
              ·
                refine ⟨673328779736213797524989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7182173650519613840266549 673328779736213797524989)
                ·
                  refine ⟨252498292401080174071871, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 673328779736213797524989 252498292401080174071871)
                  ·
                    rfl

theorem cell21_1106412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 4, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 4, 5, 3].length) (baseStart_1106412 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1106412 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1106412 prefixEnd_1106412 := by exact prefixLift 1106412
  have htrace : WordTrace (prefixWord ++ tailWord_1106412) baseStart_1106412 baseEnd_1106412 := by
    simpa [prefixWord, tailWord_1106412, baseEnd_1106412] using wordTrace_append hprefix tailTrace_1106412
  have hstable : (prefixWord ++ tailWord_1106412).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1106412).length < 2 ^ (prefixWord ++ tailWord_1106412).sum := by decide
  have hdescent : baseEnd_1106412 < baseStart_1106412 := by decide
  rcases family_descends (prefixWord ++ tailWord_1106412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1106477 : List Nat := [1, 5, 4, 1, 1, 1, 1, 1, 6]
def baseStart_1106477 : Nat := 118140960795 + 1106477 * 2 ^ 59
def prefixEnd_1106477 : Nat := 4983230072969 + 3 ^ 40 * 1106477 * 2
def baseEnd_1106477 : Nat := 252513126286654505488405

theorem tailTrace_1106477 : CollatzResearch.WordTrace tailWord_1106477 prefixEnd_1106477 252513126286654505488405 := by
  unfold tailWord_1106477
  simp only [CollatzResearch.WordTrace]
  refine ⟨40356531612430275071941685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26904354408286850047961123 40356531612430275071941685)
  ·
    refine ⟨3783424838665338287994533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 40356531612430275071941685 3783424838665338287994533)
    ·
      refine ⟨709392157249750928998975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3783424838665338287994533 709392157249750928998975)
      ·
        refine ⟨1064088235874626393498463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 709392157249750928998975 1064088235874626393498463)
        ·
          refine ⟨1596132353811939590247695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1064088235874626393498463 1596132353811939590247695)
          ·
            refine ⟨2394198530717909385371543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1596132353811939590247695 2394198530717909385371543)
            ·
              refine ⟨3591297796076864078057315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2394198530717909385371543 3591297796076864078057315)
              ·
                refine ⟨5386946694115296117085973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3591297796076864078057315 5386946694115296117085973)
                ·
                  refine ⟨252513126286654505488405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5386946694115296117085973 252513126286654505488405)
                  ·
                    rfl

theorem cell21_1106477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 1, 1, 1, 6].length) (baseStart_1106477 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1106477 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1106477 prefixEnd_1106477 := by exact prefixLift 1106477
  have htrace : WordTrace (prefixWord ++ tailWord_1106477) baseStart_1106477 baseEnd_1106477 := by
    simpa [prefixWord, tailWord_1106477, baseEnd_1106477] using wordTrace_append hprefix tailTrace_1106477
  have hstable : (prefixWord ++ tailWord_1106477).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1106477).length < 2 ^ (prefixWord ++ tailWord_1106477).sum := by decide
  have hdescent : baseEnd_1106477 < baseStart_1106477 := by decide
  rcases family_descends (prefixWord ++ tailWord_1106477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1106488 : List Nat := [2, 1, 2, 1, 4, 1, 1, 6, 3]
def baseStart_1106488 : Nat := 118140960795 + 1106488 * 2 ^ 59
def prefixEnd_1106488 : Nat := 4983230072969 + 3 ^ 40 * 1106488 * 2
def baseEnd_1106488 : Nat := 252515636636520930805049

theorem tailTrace_1106488 : CollatzResearch.WordTrace tailWord_1106488 prefixEnd_1106488 252515636636520930805049 := by
  unfold tailWord_1106488
  simp only [CollatzResearch.WordTrace]
  refine ⟨20178466407695211975296059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26904621876926949300394745 20178466407695211975296059)
  ·
    refine ⟨30267699611542817962944089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20178466407695211975296059 30267699611542817962944089)
    ·
      refine ⟨22700774708657113472208067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30267699611542817962944089 22700774708657113472208067)
      ·
        refine ⟨34051162062985670208312101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22700774708657113472208067 34051162062985670208312101)
        ·
          refine ⟨6384592886809813164058519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 34051162062985670208312101 6384592886809813164058519)
          ·
            refine ⟨9576889330214719746087779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6384592886809813164058519 9576889330214719746087779)
            ·
              refine ⟨14365333995322079619131669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9576889330214719746087779 14365333995322079619131669)
              ·
                refine ⟨673375031030722482146797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 14365333995322079619131669 673375031030722482146797)
                ·
                  refine ⟨252515636636520930805049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 673375031030722482146797 252515636636520930805049)
                  ·
                    rfl

theorem cell21_1106488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 1, 6, 3].length) (baseStart_1106488 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1106488 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1106488 prefixEnd_1106488 := by exact prefixLift 1106488
  have htrace : WordTrace (prefixWord ++ tailWord_1106488) baseStart_1106488 baseEnd_1106488 := by
    simpa [prefixWord, tailWord_1106488, baseEnd_1106488] using wordTrace_append hprefix tailTrace_1106488
  have hstable : (prefixWord ++ tailWord_1106488).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1106488).length < 2 ^ (prefixWord ++ tailWord_1106488).sum := by decide
  have hdescent : baseEnd_1106488 < baseStart_1106488 := by decide
  rcases family_descends (prefixWord ++ tailWord_1106488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1106533 : List Nat := [1, 3, 1, 3, 4, 2, 7]
def baseStart_1106533 : Nat := 118140960795 + 1106533 * 2 ^ 59
def prefixEnd_1106533 : Nat := 4983230072969 + 3 ^ 40 * 1106533 * 2
def baseEnd_1106533 : Nat := 28058434027734539172773

theorem tailTrace_1106533 : CollatzResearch.WordTrace tailWord_1106533 prefixEnd_1106533 28058434027734539172773 := by
  unfold tailWord_1106533
  simp only [CollatzResearch.WordTrace]
  refine ⟨40358574100227396635980253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26905716066818264423986835 40358574100227396635980253)
  ·
    refine ⟨15134465287585273738492595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40358574100227396635980253 15134465287585273738492595)
    ·
      refine ⟨22701697931377910607738893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15134465287585273738492595 22701697931377910607738893)
      ·
        refine ⟨8513136724266716477902085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22701697931377910607738893 8513136724266716477902085)
        ·
          refine ⟨1596213135800009339606641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8513136724266716477902085 1596213135800009339606641)
          ·
            refine ⟨1197159851850007004704981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1596213135800009339606641 1197159851850007004704981)
            ·
              refine ⟨28058434027734539172773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1197159851850007004704981 28058434027734539172773)
              ·
                rfl

theorem cell21_1106533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 2, 7].length) (baseStart_1106533 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1106533 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1106533 prefixEnd_1106533 := by exact prefixLift 1106533
  have htrace : WordTrace (prefixWord ++ tailWord_1106533) baseStart_1106533 baseEnd_1106533 := by
    simpa [prefixWord, tailWord_1106533, baseEnd_1106533] using wordTrace_append hprefix tailTrace_1106533
  have hstable : (prefixWord ++ tailWord_1106533).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1106533).length < 2 ^ (prefixWord ++ tailWord_1106533).sum := by decide
  have hdescent : baseEnd_1106533 < baseStart_1106533 := by decide
  rcases family_descends (prefixWord ++ tailWord_1106533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1106550 : List Nat := [5, 1, 1, 2, 3, 1, 2, 6]
def baseStart_1106550 : Nat := 118140960795 + 1106550 * 2 ^ 59
def prefixEnd_1106550 : Nat := 4983230072969 + 3 ^ 40 * 1106550 * 2
def baseEnd_1106550 : Nat := 84176595293740866923863

theorem tailTrace_1106550 : CollatzResearch.WordTrace tailWord_1106550 prefixEnd_1106550 84176595293740866923863 := by
  unfold tailWord_1106550
  simp only [CollatzResearch.WordTrace]
  refine ⟨2522449633822863033709319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 26906129427443872359566069 2522449633822863033709319)
  ·
    refine ⟨3783674450734294550563979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2522449633822863033709319 3783674450734294550563979)
    ·
      refine ⟨5675511676101441825845969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3783674450734294550563979 5675511676101441825845969)
      ·
        refine ⟨4256633757076081369384477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5675511676101441825845969 4256633757076081369384477)
        ·
          refine ⟨1596237658903530513519179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4256633757076081369384477 1596237658903530513519179)
          ·
            refine ⟨2394356488355295770278769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1596237658903530513519179 2394356488355295770278769)
            ·
              refine ⟨1795767366266471827709077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2394356488355295770278769 1795767366266471827709077)
              ·
                refine ⟨84176595293740866923863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1795767366266471827709077 84176595293740866923863)
                ·
                  rfl

theorem cell21_1106550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 1, 2, 6].length) (baseStart_1106550 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1106550 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1106550 prefixEnd_1106550 := by exact prefixLift 1106550
  have htrace : WordTrace (prefixWord ++ tailWord_1106550) baseStart_1106550 baseEnd_1106550 := by
    simpa [prefixWord, tailWord_1106550, baseEnd_1106550] using wordTrace_append hprefix tailTrace_1106550
  have hstable : (prefixWord ++ tailWord_1106550).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1106550).length < 2 ^ (prefixWord ++ tailWord_1106550).sum := by decide
  have hdescent : baseEnd_1106550 < baseStart_1106550 := by decide
  rcases family_descends (prefixWord ++ tailWord_1106550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1106592 : List Nat := [2, 1, 1, 4, 4, 9]
def baseStart_1106592 : Nat := 118140960795 + 1106592 * 2 ^ 59
def prefixEnd_1106592 : Nat := 4983230072969 + 3 ^ 40 * 1106592 * 2
def baseEnd_1106592 : Nat := 9353310031608883743389

theorem tailTrace_1106592 : CollatzResearch.WordTrace tailWord_1106592 prefixEnd_1106592 9353310031608883743389 := by
  unfold tailWord_1106592
  simp only [CollatzResearch.WordTrace]
  refine ⟨20180363003506824856189015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26907150671342433141585353 20180363003506824856189015)
  ·
    refine ⟨30270544505260237284283523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20180363003506824856189015 30270544505260237284283523)
    ·
      refine ⟨45405816757890355926425285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30270544505260237284283523 45405816757890355926425285)
      ·
        refine ⟨8513590642104441736204741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 45405816757890355926425285 8513590642104441736204741)
        ·
          refine ⟨1596298245394582825538389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8513590642104441736204741 1596298245394582825538389)
          ·
            refine ⟨9353310031608883743389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1596298245394582825538389 9353310031608883743389)
            ·
              rfl

theorem cell21_1106592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 9].length) (baseStart_1106592 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1106592 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1106592 prefixEnd_1106592 := by exact prefixLift 1106592
  have htrace : WordTrace (prefixWord ++ tailWord_1106592) baseStart_1106592 baseEnd_1106592 := by
    simpa [prefixWord, tailWord_1106592, baseEnd_1106592] using wordTrace_append hprefix tailTrace_1106592
  have hstable : (prefixWord ++ tailWord_1106592).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1106592).length < 2 ^ (prefixWord ++ tailWord_1106592).sum := by decide
  have hdescent : baseEnd_1106592 < baseStart_1106592 := by decide
  rcases family_descends (prefixWord ++ tailWord_1106592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1106623 : List Nat := [1, 1, 2, 2, 2, 5, 1, 2, 5]
def baseStart_1106623 : Nat := 118140960795 + 1106623 * 2 ^ 59
def prefixEnd_1106623 : Nat := 4983230072969 + 3 ^ 40 * 1106623 * 2
def baseEnd_1106623 : Nat := 252546445475790696054773

theorem tailTrace_1106623 : CollatzResearch.WordTrace tailWord_1106623 prefixEnd_1106623 252546445475790696054773 := by
  unfold tailWord_1106623
  simp only [CollatzResearch.WordTrace]
  refine ⟨40361856669901342006756523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26907904446600894671171015 40361856669901342006756523)
  ·
    refine ⟨60542785004852013010134785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40361856669901342006756523 60542785004852013010134785)
    ·
      refine ⟨45407088753639009757601089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60542785004852013010134785 45407088753639009757601089)
      ·
        refine ⟨34055316565229257318200817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45407088753639009757601089 34055316565229257318200817)
        ·
          refine ⟨25541487423921942988650613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34055316565229257318200817 25541487423921942988650613)
          ·
            refine ⟨2394514445992682155185995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 25541487423921942988650613 2394514445992682155185995)
            ·
              refine ⟨3591771668989023232778993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2394514445992682155185995 3591771668989023232778993)
              ·
                refine ⟨2693828751741767424584245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3591771668989023232778993 2693828751741767424584245)
                ·
                  refine ⟨252546445475790696054773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2693828751741767424584245 252546445475790696054773)
                  ·
                    rfl

theorem cell21_1106623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 5, 1, 2, 5].length) (baseStart_1106623 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1106623 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1106623 prefixEnd_1106623 := by exact prefixLift 1106623
  have htrace : WordTrace (prefixWord ++ tailWord_1106623) baseStart_1106623 baseEnd_1106623 := by
    simpa [prefixWord, tailWord_1106623, baseEnd_1106623] using wordTrace_append hprefix tailTrace_1106623
  have hstable : (prefixWord ++ tailWord_1106623).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1106623).length < 2 ^ (prefixWord ++ tailWord_1106623).sum := by decide
  have hdescent : baseEnd_1106623 < baseStart_1106623 := by decide
  rcases family_descends (prefixWord ++ tailWord_1106623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1106671 : List Nat := [1, 1, 2, 1, 5, 3, 3, 1, 4]
def baseStart_1106671 : Nat := 118140960795 + 1106671 * 2 ^ 59
def prefixEnd_1106671 : Nat := 4983230072969 + 3 ^ 40 * 1106671 * 2
def baseEnd_1106671 : Nat := 252557399729753279254675

theorem tailTrace_1106671 : CollatzResearch.WordTrace tailWord_1106671 prefixEnd_1106671 252557399729753279254675 := by
  unfold tailWord_1106671
  simp only [CollatzResearch.WordTrace]
  refine ⟨40363607373727446204503867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26909071582484964136335911 40363607373727446204503867)
  ·
    refine ⟨60545411060591169306755801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40363607373727446204503867 60545411060591169306755801)
    ·
      refine ⟨45409058295443376980066851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60545411060591169306755801 45409058295443376980066851)
      ·
        refine ⟨68113587443165065470100277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45409058295443376980066851 68113587443165065470100277)
        ·
          refine ⟨6385648822796724887821901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 68113587443165065470100277 6385648822796724887821901)
          ·
            refine ⟨2394618308548771832933213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6385648822796724887821901 2394618308548771832933213)
            ·
              refine ⟨897981865705789437349955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2394618308548771832933213 897981865705789437349955)
              ·
                refine ⟨1346972798558684156024933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 897981865705789437349955 1346972798558684156024933)
                ·
                  refine ⟨252557399729753279254675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1346972798558684156024933 252557399729753279254675)
                  ·
                    rfl

theorem cell21_1106671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 3, 3, 1, 4].length) (baseStart_1106671 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1106671 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1106671 prefixEnd_1106671 := by exact prefixLift 1106671
  have htrace : WordTrace (prefixWord ++ tailWord_1106671) baseStart_1106671 baseEnd_1106671 := by
    simpa [prefixWord, tailWord_1106671, baseEnd_1106671] using wordTrace_append hprefix tailTrace_1106671
  have hstable : (prefixWord ++ tailWord_1106671).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1106671).length < 2 ^ (prefixWord ++ tailWord_1106671).sum := by decide
  have hdescent : baseEnd_1106671 < baseStart_1106671 := by decide
  rcases family_descends (prefixWord ++ tailWord_1106671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1106677 : List Nat := [1, 3, 6, 1, 2, 1, 2, 5]
def baseStart_1106677 : Nat := 118140960795 + 1106677 * 2 ^ 59
def prefixEnd_1106677 : Nat := 4983230072969 + 3 ^ 40 * 1106677 * 2
def baseEnd_1106677 : Nat := 84186256337166200718221

theorem tailTrace_1106677 : CollatzResearch.WordTrace tailWord_1106677 prefixEnd_1106677 84186256337166200718221 := by
  unfold tailWord_1106677
  simp only [CollatzResearch.WordTrace]
  refine ⟨40363826211705709229222285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26909217474470472819481523 40363826211705709229222285)
  ·
    refine ⟨15136434829389640960958357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40363826211705709229222285 15136434829389640960958357)
    ·
      refine ⟨709520382627639420044923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 15136434829389640960958357 709520382627639420044923)
      ·
        refine ⟨1064280573941459130067385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 709520382627639420044923 1064280573941459130067385)
        ·
          refine ⟨798210430456094347550539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1064280573941459130067385 798210430456094347550539)
          ·
            refine ⟨1197315645684141521325809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 798210430456094347550539 1197315645684141521325809)
            ·
              refine ⟨897986734263106140994357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1197315645684141521325809 897986734263106140994357)
              ·
                refine ⟨84186256337166200718221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 897986734263106140994357 84186256337166200718221)
                ·
                  rfl

theorem cell21_1106677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 2, 1, 2, 5].length) (baseStart_1106677 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1106677 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1106677 prefixEnd_1106677 := by exact prefixLift 1106677
  have htrace : WordTrace (prefixWord ++ tailWord_1106677) baseStart_1106677 baseEnd_1106677 := by
    simpa [prefixWord, tailWord_1106677, baseEnd_1106677] using wordTrace_append hprefix tailTrace_1106677
  have hstable : (prefixWord ++ tailWord_1106677).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1106677).length < 2 ^ (prefixWord ++ tailWord_1106677).sum := by decide
  have hdescent : baseEnd_1106677 < baseStart_1106677 := by decide
  rcases family_descends (prefixWord ++ tailWord_1106677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1106716 : List Nat := [2, 2, 3, 1, 1, 5, 1, 1, 5]
def baseStart_1106716 : Nat := 118140960795 + 1106716 * 2 ^ 59
def prefixEnd_1106716 : Nat := 4983230072969 + 3 ^ 40 * 1106716 * 2
def baseEnd_1106716 : Nat := 252567669342843201004583

theorem tailTrace_1106716 : CollatzResearch.WordTrace tailWord_1106716 prefixEnd_1106716 252567669342843201004583 := by
  unfold tailWord_1106716
  simp only [CollatzResearch.WordTrace]
  refine ⟨20182624329282209444946001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26910165772376279259928001 20182624329282209444946001)
  ·
    refine ⟨15136968246961657083709501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20182624329282209444946001 15136968246961657083709501)
    ·
      refine ⟨5676363092610621406391063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15136968246961657083709501 5676363092610621406391063)
      ·
        refine ⟨8514544638915932109586595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5676363092610621406391063 8514544638915932109586595)
        ·
          refine ⟨12771816958373898164379893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8514544638915932109586595 12771816958373898164379893)
          ·
            refine ⟨1197357839847552952910615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 12771816958373898164379893 1197357839847552952910615)
            ·
              refine ⟨1796036759771329429365923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1197357839847552952910615 1796036759771329429365923)
              ·
                refine ⟨2694055139656994144048885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1796036759771329429365923 2694055139656994144048885)
                ·
                  refine ⟨252567669342843201004583, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2694055139656994144048885 252567669342843201004583)
                  ·
                    rfl

theorem cell21_1106716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 5, 1, 1, 5].length) (baseStart_1106716 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1106716 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1106716 prefixEnd_1106716 := by exact prefixLift 1106716
  have htrace : WordTrace (prefixWord ++ tailWord_1106716) baseStart_1106716 baseEnd_1106716 := by
    simpa [prefixWord, tailWord_1106716, baseEnd_1106716] using wordTrace_append hprefix tailTrace_1106716
  have hstable : (prefixWord ++ tailWord_1106716).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1106716).length < 2 ^ (prefixWord ++ tailWord_1106716).sum := by decide
  have hdescent : baseEnd_1106716 < baseStart_1106716 := by decide
  rcases family_descends (prefixWord ++ tailWord_1106716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1106803 : List Nat := [1, 1, 1, 2, 2, 1, 4, 9]
def baseStart_1106803 : Nat := 118140960795 + 1106803 * 2 ^ 59
def prefixEnd_1106803 : Nat := 4983230072969 + 3 ^ 40 * 1106803 * 2
def baseEnd_1106803 : Nat := 84195841309383461018135

theorem tailTrace_1106803 : CollatzResearch.WordTrace tailWord_1106803 prefixEnd_1106803 84195841309383461018135 := by
  unfold tailWord_1106803
  simp only [CollatzResearch.WordTrace]
  refine ⟨40368421809249232748309063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26912281206166155165539375 40368421809249232748309063)
  ·
    refine ⟨60552632713873849122463595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40368421809249232748309063 60552632713873849122463595)
    ·
      refine ⟨90828949070810773683695393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60552632713873849122463595 90828949070810773683695393)
      ·
        refine ⟨68121711803108080262771545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 90828949070810773683695393 68121711803108080262771545)
        ·
          refine ⟨51091283852331060197078659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 68121711803108080262771545 51091283852331060197078659)
          ·
            refine ⟨76636925778496590295617989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51091283852331060197078659 76636925778496590295617989)
            ·
              refine ⟨14369423583468110680428373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 76636925778496590295617989 14369423583468110680428373)
              ·
                refine ⟨84195841309383461018135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 14369423583468110680428373 84195841309383461018135)
                ·
                  rfl

theorem cell21_1106803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 4, 9].length) (baseStart_1106803 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1106803 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1106803 prefixEnd_1106803 := by exact prefixLift 1106803
  have htrace : WordTrace (prefixWord ++ tailWord_1106803) baseStart_1106803 baseEnd_1106803 := by
    simpa [prefixWord, tailWord_1106803, baseEnd_1106803] using wordTrace_append hprefix tailTrace_1106803
  have hstable : (prefixWord ++ tailWord_1106803).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1106803).length < 2 ^ (prefixWord ++ tailWord_1106803).sum := by decide
  have hdescent : baseEnd_1106803 < baseStart_1106803 := by decide
  rcases family_descends (prefixWord ++ tailWord_1106803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1106823 : List Nat := [1, 1, 4, 2, 3, 3, 1, 2, 4]
def baseStart_1106823 : Nat := 118140960795 + 1106823 * 2 ^ 59
def prefixEnd_1106823 : Nat := 4983230072969 + 3 ^ 40 * 1106823 * 2
def baseEnd_1106823 : Nat := 252592088200634792721031

theorem tailTrace_1106823 : CollatzResearch.WordTrace tailWord_1106823 prefixEnd_1106823 252592088200634792721031 := by
  unfold tailWord_1106823
  simp only [CollatzResearch.WordTrace]
  refine ⟨40369151269176776164037123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26912767512784517442691415 40369151269176776164037123)
  ·
    refine ⟨60553726903765164246055685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40369151269176776164037123 60553726903765164246055685)
    ·
      refine ⟨11353823794455968296135441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 60553726903765164246055685 11353823794455968296135441)
      ·
        refine ⟨8515367845841976222101581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11353823794455968296135441 8515367845841976222101581)
        ·
          refine ⟨3193262942190741083288093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8515367845841976222101581 3193262942190741083288093)
          ·
            refine ⟨1197473603321527906233035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3193262942190741083288093 1197473603321527906233035)
            ·
              refine ⟨1796210404982291859349553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1197473603321527906233035 1796210404982291859349553)
              ·
                refine ⟨1347157803736718894512165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1796210404982291859349553 1347157803736718894512165)
                ·
                  refine ⟨252592088200634792721031, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1347157803736718894512165 252592088200634792721031)
                  ·
                    rfl

theorem cell21_1106823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 3, 1, 2, 4].length) (baseStart_1106823 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1106823 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1106823 prefixEnd_1106823 := by exact prefixLift 1106823
  have htrace : WordTrace (prefixWord ++ tailWord_1106823) baseStart_1106823 baseEnd_1106823 := by
    simpa [prefixWord, tailWord_1106823, baseEnd_1106823] using wordTrace_append hprefix tailTrace_1106823
  have hstable : (prefixWord ++ tailWord_1106823).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1106823).length < 2 ^ (prefixWord ++ tailWord_1106823).sum := by decide
  have hdescent : baseEnd_1106823 < baseStart_1106823 := by decide
  rcases family_descends (prefixWord ++ tailWord_1106823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1106958 : List Nat := [4, 1, 1, 2, 2, 2, 2, 3, 4]
def baseStart_1106958 : Nat := 118140960795 + 1106958 * 2 ^ 59
def prefixEnd_1106958 : Nat := 4983230072969 + 3 ^ 40 * 1106958 * 2
def baseEnd_1106958 : Nat := 252622897039904557970755

theorem tailTrace_1106958 : CollatzResearch.WordTrace tailWord_1106958 prefixEnd_1106958 252622897039904557970755 := by
  unfold tailWord_1106958
  simp only [CollatzResearch.WordTrace]
  refine ⟨5046759390460961777525191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 26916050082458462813467685 5046759390460961777525191)
  ·
    refine ⟨7570139085691442666287787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5046759390460961777525191 7570139085691442666287787)
    ·
      refine ⟨11355208628537163999431681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7570139085691442666287787 11355208628537163999431681)
      ·
        refine ⟨8516406471402872999573761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11355208628537163999431681 8516406471402872999573761)
        ·
          refine ⟨6387304853552154749680321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8516406471402872999573761 6387304853552154749680321)
          ·
            refine ⟨4790478640164116062260241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6387304853552154749680321 4790478640164116062260241)
            ·
              refine ⟨3592858980123087046695181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4790478640164116062260241 3592858980123087046695181)
              ·
                refine ⟨1347322117546157642510693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3592858980123087046695181 1347322117546157642510693)
                ·
                  refine ⟨252622897039904557970755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1347322117546157642510693 252622897039904557970755)
                  ·
                    rfl

theorem cell21_1106958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 2, 3, 4].length) (baseStart_1106958 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1106958 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1106958 prefixEnd_1106958 := by exact prefixLift 1106958
  have htrace : WordTrace (prefixWord ++ tailWord_1106958) baseStart_1106958 baseEnd_1106958 := by
    simpa [prefixWord, tailWord_1106958, baseEnd_1106958] using wordTrace_append hprefix tailTrace_1106958
  have hstable : (prefixWord ++ tailWord_1106958).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1106958).length < 2 ^ (prefixWord ++ tailWord_1106958).sum := by decide
  have hdescent : baseEnd_1106958 < baseStart_1106958 := by decide
  rcases family_descends (prefixWord ++ tailWord_1106958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1107169 : List Nat := [1, 2, 3, 1, 3, 3, 1, 1, 6]
def baseStart_1107169 : Nat := 118140960795 + 1107169 * 2 ^ 59
def prefixEnd_1107169 : Nat := 4983230072969 + 3 ^ 40 * 1107169 * 2
def baseEnd_1107169 : Nat := 252671050114615079953657

theorem tailTrace_1107169 : CollatzResearch.WordTrace tailWord_1107169 prefixEnd_1107169 252671050114615079953657 := by
  unfold tailWord_1107169
  simp only [CollatzResearch.WordTrace]
  refine ⟨40381770925923277256132561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26921180617282184837421707 40381770925923277256132561)
  ·
    refine ⟨30286328194442457942099421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40381770925923277256132561 30286328194442457942099421)
    ·
      refine ⟨11357373072915921728287283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30286328194442457942099421 11357373072915921728287283)
      ·
        refine ⟨17036059609373882592430925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11357373072915921728287283 17036059609373882592430925)
        ·
          refine ⟨6388522353515205972161597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17036059609373882592430925 6388522353515205972161597)
          ·
            refine ⟨2395695882568202239560599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6388522353515205972161597 2395695882568202239560599)
            ·
              refine ⟨3593543823852303359340899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2395695882568202239560599 3593543823852303359340899)
              ·
                refine ⟨5390315735778455039011349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3593543823852303359340899 5390315735778455039011349)
                ·
                  refine ⟨252671050114615079953657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5390315735778455039011349 252671050114615079953657)
                  ·
                    rfl

theorem cell21_1107169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 3, 1, 1, 6].length) (baseStart_1107169 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1107169 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1107169 prefixEnd_1107169 := by exact prefixLift 1107169
  have htrace : WordTrace (prefixWord ++ tailWord_1107169) baseStart_1107169 baseEnd_1107169 := by
    simpa [prefixWord, tailWord_1107169, baseEnd_1107169] using wordTrace_append hprefix tailTrace_1107169
  have hstable : (prefixWord ++ tailWord_1107169).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1107169).length < 2 ^ (prefixWord ++ tailWord_1107169).sum := by decide
  have hdescent : baseEnd_1107169 < baseStart_1107169 := by decide
  rcases family_descends (prefixWord ++ tailWord_1107169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1107310 : List Nat := [4, 1, 2, 4, 1, 1, 3, 5]
def baseStart_1107310 : Nat := 118140960795 + 1107310 * 2 ^ 59
def prefixEnd_1107310 : Nat := 4983230072969 + 3 ^ 40 * 1107310 * 2
def baseEnd_1107310 : Nat := 84234409411876722701123

theorem tailTrace_1107310 : CollatzResearch.WordTrace tailWord_1107310 prefixEnd_1107310 84234409411876722701123 := by
  unfold tailWord_1107310
  simp only [CollatzResearch.WordTrace]
  refine ⟨5048364202301557292126923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 26924609078941638891343589 5048364202301557292126923)
  ·
    refine ⟨7572546303452335938190385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5048364202301557292126923 7572546303452335938190385)
    ·
      refine ⟨5679409727589251953642789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7572546303452335938190385 5679409727589251953642789)
      ·
        refine ⟨1064889323922984741308023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5679409727589251953642789 1064889323922984741308023)
        ·
          refine ⟨1597333985884477111962035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1064889323922984741308023 1597333985884477111962035)
          ·
            refine ⟨2396000978826715667943053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1597333985884477111962035 2396000978826715667943053)
            ·
              refine ⟨898500367060018375478645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2396000978826715667943053 898500367060018375478645)
              ·
                refine ⟨84234409411876722701123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 898500367060018375478645 84234409411876722701123)
                ·
                  rfl

theorem cell21_1107310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 1, 3, 5].length) (baseStart_1107310 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1107310 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1107310 prefixEnd_1107310 := by exact prefixLift 1107310
  have htrace : WordTrace (prefixWord ++ tailWord_1107310) baseStart_1107310 baseEnd_1107310 := by
    simpa [prefixWord, tailWord_1107310, baseEnd_1107310] using wordTrace_append hprefix tailTrace_1107310
  have hstable : (prefixWord ++ tailWord_1107310).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1107310).length < 2 ^ (prefixWord ++ tailWord_1107310).sum := by decide
  have hdescent : baseEnd_1107310 < baseStart_1107310 := by decide
  rcases family_descends (prefixWord ++ tailWord_1107310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1107335 : List Nat := [1, 1, 4, 2, 2, 3, 8]
def baseStart_1107335 : Nat := 118140960795 + 1107335 * 2 ^ 59
def prefixEnd_1107335 : Nat := 4983230072969 + 3 ^ 40 * 1107335 * 2
def baseEnd_1107335 : Nat := 28078770397359520020739

theorem tailTrace_1107335 : CollatzResearch.WordTrace tailWord_1107335 prefixEnd_1107335 28078770397359520020739 := by
  unfold tailWord_1107335
  simp only [CollatzResearch.WordTrace]
  refine ⟨40387825443321887606675459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26925216962214591737783639 40387825443321887606675459)
  ·
    refine ⟨60581738164982831410013189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40387825443321887606675459 60581738164982831410013189)
    ·
      refine ⟨11359075905934280889377473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 60581738164982831410013189 11359075905934280889377473)
      ·
        refine ⟨8519306929450710667033105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11359075905934280889377473 8519306929450710667033105)
        ·
          refine ⟨6389480197088033000274829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8519306929450710667033105 6389480197088033000274829)
          ·
            refine ⟨2396055073908012375103061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6389480197088033000274829 2396055073908012375103061)
            ·
              refine ⟨28078770397359520020739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2396055073908012375103061 28078770397359520020739)
              ·
                rfl

theorem cell21_1107335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 3, 8].length) (baseStart_1107335 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1107335 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1107335 prefixEnd_1107335 := by exact prefixLift 1107335
  have htrace : WordTrace (prefixWord ++ tailWord_1107335) baseStart_1107335 baseEnd_1107335 := by
    simpa [prefixWord, tailWord_1107335, baseEnd_1107335] using wordTrace_append hprefix tailTrace_1107335
  have hstable : (prefixWord ++ tailWord_1107335).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1107335).length < 2 ^ (prefixWord ++ tailWord_1107335).sum := by decide
  have hdescent : baseEnd_1107335 < baseStart_1107335 := by decide
  rcases family_descends (prefixWord ++ tailWord_1107335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1107400 : List Nat := [2, 1, 3, 1, 3, 1, 5, 2, 3]
def baseStart_1107400 : Nat := 118140960795 + 1107400 * 2 ^ 59
def prefixEnd_1107400 : Nat := 4983230072969 + 3 ^ 40 * 1107400 * 2
def baseEnd_1107400 : Nat := 252723767461810011603185

theorem tailTrace_1107400 : CollatzResearch.WordTrace tailWord_1107400 prefixEnd_1107400 252723767461810011603185 := by
  unfold tailWord_1107400
  simp only [CollatzResearch.WordTrace]
  refine ⟨20195098094043201853895827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26926797458724269138527769 20195098094043201853895827)
  ·
    refine ⟨30292647141064802780843741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20195098094043201853895827 30292647141064802780843741)
    ·
      refine ⟨11359742677899301042816403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30292647141064802780843741 11359742677899301042816403)
      ·
        refine ⟨17039614016848951564224605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11359742677899301042816403 17039614016848951564224605)
        ·
          refine ⟨6389855256318356836584227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17039614016848951564224605 6389855256318356836584227)
          ·
            refine ⟨9584782884477535254876341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6389855256318356836584227 9584782884477535254876341)
            ·
              refine ⟨898573395419768930144657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 9584782884477535254876341 898573395419768930144657)
              ·
                refine ⟨673930046564826697608493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 898573395419768930144657 673930046564826697608493)
                ·
                  refine ⟨252723767461810011603185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 673930046564826697608493 252723767461810011603185)
                  ·
                    rfl

theorem cell21_1107400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 5, 2, 3].length) (baseStart_1107400 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1107400 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1107400 prefixEnd_1107400 := by exact prefixLift 1107400
  have htrace : WordTrace (prefixWord ++ tailWord_1107400) baseStart_1107400 baseEnd_1107400 := by
    simpa [prefixWord, tailWord_1107400, baseEnd_1107400] using wordTrace_append hprefix tailTrace_1107400
  have hstable : (prefixWord ++ tailWord_1107400).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1107400).length < 2 ^ (prefixWord ++ tailWord_1107400).sum := by decide
  have hdescent : baseEnd_1107400 < baseStart_1107400 := by decide
  rcases family_descends (prefixWord ++ tailWord_1107400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1107476 : List Nat := [2, 4, 3, 1, 2, 1, 1, 2, 5]
def baseStart_1107476 : Nat := 118140960795 + 1107476 * 2 ^ 59
def prefixEnd_1107476 : Nat := 4983230072969 + 3 ^ 40 * 1107476 * 2
def baseEnd_1107476 : Nat := 252741111697250768336363

theorem tailTrace_1107476 : CollatzResearch.WordTrace tailWord_1107476 prefixEnd_1107476 252741111697250768336363 := by
  unfold tailWord_1107476
  simp only [CollatzResearch.WordTrace]
  refine ⟨20196484067905534343779141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26928645423874045791705521 20196484067905534343779141)
  ·
    refine ⟨3786840762732287689458589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 20196484067905534343779141 3786840762732287689458589)
    ·
      refine ⟨1420065286024607883546971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3786840762732287689458589 1420065286024607883546971)
      ·
        refine ⟨2130097929036911825320457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1420065286024607883546971 2130097929036911825320457)
        ·
          refine ⟨1597573446777683868990343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2130097929036911825320457 1597573446777683868990343)
          ·
            refine ⟨2396360170166525803485515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1597573446777683868990343 2396360170166525803485515)
            ·
              refine ⟨3594540255249788705228273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2396360170166525803485515 3594540255249788705228273)
              ·
                refine ⟨2695905191437341528921205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3594540255249788705228273 2695905191437341528921205)
                ·
                  refine ⟨252741111697250768336363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2695905191437341528921205 252741111697250768336363)
                  ·
                    rfl

theorem cell21_1107476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 1, 1, 2, 5].length) (baseStart_1107476 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1107476 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1107476 prefixEnd_1107476 := by exact prefixLift 1107476
  have htrace : WordTrace (prefixWord ++ tailWord_1107476) baseStart_1107476 baseEnd_1107476 := by
    simpa [prefixWord, tailWord_1107476, baseEnd_1107476] using wordTrace_append hprefix tailTrace_1107476
  have hstable : (prefixWord ++ tailWord_1107476).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1107476).length < 2 ^ (prefixWord ++ tailWord_1107476).sum := by decide
  have hdescent : baseEnd_1107476 < baseStart_1107476 := by decide
  rcases family_descends (prefixWord ++ tailWord_1107476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1107639 : List Nat := [1, 1, 3, 1, 5, 1, 3, 6]
def baseStart_1107639 : Nat := 118140960795 + 1107639 * 2 ^ 59
def prefixEnd_1107639 : Nat := 4983230072969 + 3 ^ 40 * 1107639 * 2
def baseEnd_1107639 : Nat := 84259436839332902373121

theorem tailTrace_1107639 : CollatzResearch.WordTrace tailWord_1107639 prefixEnd_1107639 84259436839332902373121 := by
  unfold tailWord_1107639
  simp only [CollatzResearch.WordTrace]
  refine ⟨40398913234220547525741971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26932608822813698350494647 40398913234220547525741971)
  ·
    refine ⟨60598369851330821288612957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40398913234220547525741971 60598369851330821288612957)
    ·
      refine ⟨22724388694249057983229859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 60598369851330821288612957 22724388694249057983229859)
      ·
        refine ⟨34086583041373586974844789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22724388694249057983229859 34086583041373586974844789)
        ·
          refine ⟨3195617160128773778891699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 34086583041373586974844789 3195617160128773778891699)
          ·
            refine ⟨4793425740193160668337549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3195617160128773778891699 4793425740193160668337549)
            ·
              refine ⟨1797534652572435250626581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4793425740193160668337549 1797534652572435250626581)
              ·
                refine ⟨84259436839332902373121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1797534652572435250626581 84259436839332902373121)
                ·
                  rfl

theorem cell21_1107639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 3, 6].length) (baseStart_1107639 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1107639 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1107639 prefixEnd_1107639 := by exact prefixLift 1107639
  have htrace : WordTrace (prefixWord ++ tailWord_1107639) baseStart_1107639 baseEnd_1107639 := by
    simpa [prefixWord, tailWord_1107639, baseEnd_1107639] using wordTrace_append hprefix tailTrace_1107639
  have hstable : (prefixWord ++ tailWord_1107639).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1107639).length < 2 ^ (prefixWord ++ tailWord_1107639).sum := by decide
  have hdescent : baseEnd_1107639 < baseStart_1107639 := by decide
  rcases family_descends (prefixWord ++ tailWord_1107639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1107653 : List Nat := [1, 3, 1, 1, 1, 1, 2, 6, 5]
def baseStart_1107653 : Nat := 118140960795 + 1107653 * 2 ^ 59
def prefixEnd_1107653 : Nat := 4983230072969 + 3 ^ 40 * 1107653 * 2
def baseEnd_1107653 : Nat := 252781505508737793886001

theorem tailTrace_1107653 : CollatzResearch.WordTrace tailWord_1107653 prefixEnd_1107653 252781505508737793886001 := by
  unfold tailWord_1107653
  simp only [CollatzResearch.WordTrace]
  refine ⟨40399423856169827916751613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26932949237446551944501075 40399423856169827916751613)
  ·
    refine ⟨15149783946063685468781855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40399423856169827916751613 15149783946063685468781855)
    ·
      refine ⟨22724675919095528203172783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15149783946063685468781855 22724675919095528203172783)
      ·
        refine ⟨34087013878643292304759175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22724675919095528203172783 34087013878643292304759175)
        ·
          refine ⟨51130520817964938457138763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34087013878643292304759175 51130520817964938457138763)
          ·
            refine ⟨76695781226947407685708145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51130520817964938457138763 76695781226947407685708145)
            ·
              refine ⟨57521835920210555764281109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 76695781226947407685708145 57521835920210555764281109)
              ·
                refine ⟨2696336058759869801450677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 57521835920210555764281109 2696336058759869801450677)
                ·
                  refine ⟨252781505508737793886001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2696336058759869801450677 252781505508737793886001)
                  ·
                    rfl

theorem cell21_1107653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 6, 5].length) (baseStart_1107653 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1107653 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1107653 prefixEnd_1107653 := by exact prefixLift 1107653
  have htrace : WordTrace (prefixWord ++ tailWord_1107653) baseStart_1107653 baseEnd_1107653 := by
    simpa [prefixWord, tailWord_1107653, baseEnd_1107653] using wordTrace_append hprefix tailTrace_1107653
  have hstable : (prefixWord ++ tailWord_1107653).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1107653).length < 2 ^ (prefixWord ++ tailWord_1107653).sum := by decide
  have hdescent : baseEnd_1107653 < baseStart_1107653 := by decide
  rcases family_descends (prefixWord ++ tailWord_1107653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1107676 : List Nat := [2, 2, 5, 1, 3, 1, 1, 2, 4]
def baseStart_1107676 : Nat := 118140960795 + 1107676 * 2 ^ 59
def prefixEnd_1107676 : Nat := 4983230072969 + 3 ^ 40 * 1107676 * 2
def baseEnd_1107676 : Nat := 252786754422094865002621

theorem tailTrace_1107676 : CollatzResearch.WordTrace tailWord_1107676 prefixEnd_1107676 252786754422094865002621 := by
  unfold tailWord_1107676
  simp only [CollatzResearch.WordTrace]
  refine ⟨20200131367543251422419441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26933508490057668563225921 20200131367543251422419441)
  ·
    refine ⟨15150098525657438566814581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20200131367543251422419441 15150098525657438566814581)
    ·
      refine ⟨1420321736780384865638867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 15150098525657438566814581 1420321736780384865638867)
      ·
        refine ⟨2130482605170577298458301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1420321736780384865638867 2130482605170577298458301)
        ·
          refine ⟨798930976938966486921863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2130482605170577298458301 798930976938966486921863)
          ·
            refine ⟨1198396465408449730382795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 798930976938966486921863 1198396465408449730382795)
            ·
              refine ⟨1797594698112674595574193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1198396465408449730382795 1797594698112674595574193)
              ·
                refine ⟨1348196023584505946680645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1797594698112674595574193 1348196023584505946680645)
                ·
                  refine ⟨252786754422094865002621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1348196023584505946680645 252786754422094865002621)
                  ·
                    rfl

theorem cell21_1107676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 3, 1, 1, 2, 4].length) (baseStart_1107676 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1107676 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1107676 prefixEnd_1107676 := by exact prefixLift 1107676
  have htrace : WordTrace (prefixWord ++ tailWord_1107676) baseStart_1107676 baseEnd_1107676 := by
    simpa [prefixWord, tailWord_1107676, baseEnd_1107676] using wordTrace_append hprefix tailTrace_1107676
  have hstable : (prefixWord ++ tailWord_1107676).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1107676).length < 2 ^ (prefixWord ++ tailWord_1107676).sum := by decide
  have hdescent : baseEnd_1107676 < baseStart_1107676 := by decide
  rcases family_descends (prefixWord ++ tailWord_1107676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1107684 : List Nat := [2, 3, 1, 1, 1, 3, 3, 1, 6]
def baseStart_1107684 : Nat := 118140960795 + 1107684 * 2 ^ 59
def prefixEnd_1107684 : Nat := 4983230072969 + 3 ^ 40 * 1107684 * 2
def baseEnd_1107684 : Nat := 252788580131088628869271

theorem tailTrace_1107684 : CollatzResearch.WordTrace tailWord_1107684 prefixEnd_1107684 252788580131088628869271 := by
  unfold tailWord_1107684
  simp only [CollatzResearch.WordTrace]
  refine ⟨20200277259528760105565053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26933703012705013474086737 20200277259528760105565053)
  ·
    refine ⟨7575103972323285039586895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20200277259528760105565053 7575103972323285039586895)
    ·
      refine ⟨11362655958484927559380343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7575103972323285039586895 11362655958484927559380343)
      ·
        refine ⟨17043983937727391339070515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11362655958484927559380343 17043983937727391339070515)
        ·
          refine ⟨25565975906591087008605773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17043983937727391339070515 25565975906591087008605773)
          ·
            refine ⟨9587240964971657628227165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25565975906591087008605773 9587240964971657628227165)
            ·
              refine ⟨3595215361864371610585187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9587240964971657628227165 3595215361864371610585187)
              ·
                refine ⟨5392823042796557415877781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3595215361864371610585187 5392823042796557415877781)
                ·
                  refine ⟨252788580131088628869271, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5392823042796557415877781 252788580131088628869271)
                  ·
                    rfl

theorem cell21_1107684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 3, 1, 6].length) (baseStart_1107684 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1107684 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1107684 prefixEnd_1107684 := by exact prefixLift 1107684
  have htrace : WordTrace (prefixWord ++ tailWord_1107684) baseStart_1107684 baseEnd_1107684 := by
    simpa [prefixWord, tailWord_1107684, baseEnd_1107684] using wordTrace_append hprefix tailTrace_1107684
  have hstable : (prefixWord ++ tailWord_1107684).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1107684).length < 2 ^ (prefixWord ++ tailWord_1107684).sum := by decide
  have hdescent : baseEnd_1107684 < baseStart_1107684 := by decide
  rcases family_descends (prefixWord ++ tailWord_1107684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1107715 : List Nat := [1, 1, 1, 3, 2, 2, 6, 5]
def baseStart_1107715 : Nat := 118140960795 + 1107715 * 2 ^ 59
def prefixEnd_1107715 : Nat := 4983230072969 + 3 ^ 40 * 1107715 * 2
def baseEnd_1107715 : Nat := 84265218251146487950847

theorem tailTrace_1107715 : CollatzResearch.WordTrace tailWord_1107715 prefixEnd_1107715 84265218251146487950847 := by
  unfold tailWord_1107715
  simp only [CollatzResearch.WordTrace]
  refine ⟨40401685181945212505508599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26934456787963475003672399 40401685181945212505508599)
  ·
    refine ⟨60602527772917818758262899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40401685181945212505508599 60602527772917818758262899)
    ·
      refine ⟨90903791659376728137394349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60602527772917818758262899 90903791659376728137394349)
      ·
        refine ⟨34088921872266273051522881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 90903791659376728137394349 34088921872266273051522881)
        ·
          refine ⟨25566691404199704788642161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34088921872266273051522881 25566691404199704788642161)
          ·
            refine ⟨19175018553149778591481621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25566691404199704788642161 19175018553149778591481621)
            ·
              refine ⟨898828994678895871475701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 19175018553149778591481621 898828994678895871475701)
              ·
                refine ⟨84265218251146487950847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 898828994678895871475701 84265218251146487950847)
                ·
                  rfl

theorem cell21_1107715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 6, 5].length) (baseStart_1107715 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1107715 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1107715 prefixEnd_1107715 := by exact prefixLift 1107715
  have htrace : WordTrace (prefixWord ++ tailWord_1107715) baseStart_1107715 baseEnd_1107715 := by
    simpa [prefixWord, tailWord_1107715, baseEnd_1107715] using wordTrace_append hprefix tailTrace_1107715
  have hstable : (prefixWord ++ tailWord_1107715).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1107715).length < 2 ^ (prefixWord ++ tailWord_1107715).sum := by decide
  have hdescent : baseEnd_1107715 < baseStart_1107715 := by decide
  rcases family_descends (prefixWord ++ tailWord_1107715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1107819 : List Nat := [1, 1, 1, 1, 2, 2, 3, 2, 8]
def baseStart_1107819 : Nat := 118140960795 + 1107819 * 2 ^ 59
def prefixEnd_1107819 : Nat := 4983230072969 + 3 ^ 40 * 1107819 * 2
def baseEnd_1107819 : Nat := 252819388970358394118995

theorem tailTrace_1107819 : CollatzResearch.WordTrace tailWord_1107819 prefixEnd_1107819 252819388970358394118995 := by
  unfold tailWord_1107819
  simp only [CollatzResearch.WordTrace]
  refine ⟨40405478373568438267294511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26936985582378958844863007 40405478373568438267294511)
  ·
    refine ⟨60608217560352657400941767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40405478373568438267294511 60608217560352657400941767)
    ·
      refine ⟨90912326340528986101412651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60608217560352657400941767 90912326340528986101412651)
      ·
        refine ⟨136368489510793479152118977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90912326340528986101412651 136368489510793479152118977)
        ·
          refine ⟨102276367133095109364089233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 136368489510793479152118977 102276367133095109364089233)
          ·
            refine ⟨76707275349821332023066925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 102276367133095109364089233 76707275349821332023066925)
            ·
              refine ⟨28765228256182999508650097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 76707275349821332023066925 28765228256182999508650097)
              ·
                refine ⟨21573921192137249631487573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28765228256182999508650097 21573921192137249631487573)
                ·
                  refine ⟨252819388970358394118995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 21573921192137249631487573 252819388970358394118995)
                  ·
                    rfl

theorem cell21_1107819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 2, 8].length) (baseStart_1107819 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1107819 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1107819 prefixEnd_1107819 := by exact prefixLift 1107819
  have htrace : WordTrace (prefixWord ++ tailWord_1107819) baseStart_1107819 baseEnd_1107819 := by
    simpa [prefixWord, tailWord_1107819, baseEnd_1107819] using wordTrace_append hprefix tailTrace_1107819
  have hstable : (prefixWord ++ tailWord_1107819).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1107819).length < 2 ^ (prefixWord ++ tailWord_1107819).sum := by decide
  have hdescent : baseEnd_1107819 < baseStart_1107819 := by decide
  rcases family_descends (prefixWord ++ tailWord_1107819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1107822 : List Nat := [4, 1, 2, 3, 1, 1, 1, 1, 7]
def baseStart_1107822 : Nat := 118140960795 + 1107822 * 2 ^ 59
def prefixEnd_1107822 : Nat := 4983230072969 + 3 ^ 40 * 1107822 * 2
def baseEnd_1107822 : Nat := 252820073611231055568989

theorem tailTrace_1107822 : CollatzResearch.WordTrace tailWord_1107822 prefixEnd_1107822 252820073611231055568989 := by
  unfold tailWord_1107822
  simp only [CollatzResearch.WordTrace]
  refine ⟨5050698474069696222456715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 26937058528371713186435813 5050698474069696222456715)
  ·
    refine ⟨7576047711104544333685073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5050698474069696222456715 7576047711104544333685073)
    ·
      refine ⟨5682035783328408250263805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7576047711104544333685073 5682035783328408250263805)
      ·
        refine ⟨2130763418748153093848927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5682035783328408250263805 2130763418748153093848927)
        ·
          refine ⟨3196145128122229640773391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2130763418748153093848927 3196145128122229640773391)
          ·
            refine ⟨4794217692183344461160087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3196145128122229640773391 4794217692183344461160087)
            ·
              refine ⟨7191326538275016691740131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4794217692183344461160087 7191326538275016691740131)
              ·
                refine ⟨10786989807412525037610197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7191326538275016691740131 10786989807412525037610197)
                ·
                  refine ⟨252820073611231055568989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10786989807412525037610197 252820073611231055568989)
                  ·
                    rfl

theorem cell21_1107822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 1, 1, 7].length) (baseStart_1107822 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1107822 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1107822 prefixEnd_1107822 := by exact prefixLift 1107822
  have htrace : WordTrace (prefixWord ++ tailWord_1107822) baseStart_1107822 baseEnd_1107822 := by
    simpa [prefixWord, tailWord_1107822, baseEnd_1107822] using wordTrace_append hprefix tailTrace_1107822
  have hstable : (prefixWord ++ tailWord_1107822).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1107822).length < 2 ^ (prefixWord ++ tailWord_1107822).sum := by decide
  have hdescent : baseEnd_1107822 < baseStart_1107822 := by decide
  rcases family_descends (prefixWord ++ tailWord_1107822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1107898 : List Nat := [3, 1, 1, 1, 2, 1, 2, 7, 3]
def baseStart_1107898 : Nat := 118140960795 + 1107898 * 2 ^ 59
def prefixEnd_1107898 : Nat := 4983230072969 + 3 ^ 40 * 1107898 * 2
def baseEnd_1107898 : Nat := 252837417846671812302167

theorem tailTrace_1107898 : CollatzResearch.WordTrace tailWord_1107898 prefixEnd_1107898 252837417846671812302167 := by
  unfold tailWord_1107898
  simp only [CollatzResearch.WordTrace]
  refine ⟨10102089935070558689855087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26938906493521489839613565 10102089935070558689855087)
  ·
    refine ⟨15153134902605838034782631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10102089935070558689855087 15153134902605838034782631)
    ·
      refine ⟨22729702353908757052173947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15153134902605838034782631 22729702353908757052173947)
      ·
        refine ⟨34094553530863135578260921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22729702353908757052173947 34094553530863135578260921)
        ·
          refine ⟨25570915148147351683695691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34094553530863135578260921 25570915148147351683695691)
          ·
            refine ⟨38356372722221027525543537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25570915148147351683695691 38356372722221027525543537)
            ·
              refine ⟨28767279541665770644157653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38356372722221027525543537 28767279541665770644157653)
              ·
                refine ⟨674233114257791499472445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 28767279541665770644157653 674233114257791499472445)
                ·
                  refine ⟨252837417846671812302167, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 674233114257791499472445 252837417846671812302167)
                  ·
                    rfl

theorem cell21_1107898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 7, 3].length) (baseStart_1107898 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1107898 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1107898 prefixEnd_1107898 := by exact prefixLift 1107898
  have htrace : WordTrace (prefixWord ++ tailWord_1107898) baseStart_1107898 baseEnd_1107898 := by
    simpa [prefixWord, tailWord_1107898, baseEnd_1107898] using wordTrace_append hprefix tailTrace_1107898
  have hstable : (prefixWord ++ tailWord_1107898).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1107898).length < 2 ^ (prefixWord ++ tailWord_1107898).sum := by decide
  have hdescent : baseEnd_1107898 < baseStart_1107898 := by decide
  rcases family_descends (prefixWord ++ tailWord_1107898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1107912 : List Nat := [2, 1, 3, 1, 4, 1, 2, 1, 6]
def baseStart_1107912 : Nat := 118140960795 + 1107912 * 2 ^ 59
def prefixEnd_1107912 : Nat := 4983230072969 + 3 ^ 40 * 1107912 * 2
def baseEnd_1107912 : Nat := 252840612837410899068805

theorem tailTrace_1107912 : CollatzResearch.WordTrace tailWord_1107912 prefixEnd_1107912 252840612837410899068805 := by
  unfold tailWord_1107912
  simp only [CollatzResearch.WordTrace]
  refine ⟨20204435181115757575214995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26939246908154343433619993 20204435181115757575214995)
  ·
    refine ⟨30306652771673636362822493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20204435181115757575214995 30306652771673636362822493)
    ·
      refine ⟨11364994789377613636058435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30306652771673636362822493 11364994789377613636058435)
      ·
        refine ⟨17047492184066420454087653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11364994789377613636058435 17047492184066420454087653)
        ·
          refine ⟨3196404784512453835141435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17047492184066420454087653 3196404784512453835141435)
          ·
            refine ⟨4794607176768680752712153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3196404784512453835141435 4794607176768680752712153)
            ·
              refine ⟨3595955382576510564534115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4794607176768680752712153 3595955382576510564534115)
              ·
                refine ⟨5393933073864765846801173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3595955382576510564534115 5393933073864765846801173)
                ·
                  refine ⟨252840612837410899068805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5393933073864765846801173 252840612837410899068805)
                  ·
                    rfl

theorem cell21_1107912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 2, 1, 6].length) (baseStart_1107912 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1107912 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1107912 prefixEnd_1107912 := by exact prefixLift 1107912
  have htrace : WordTrace (prefixWord ++ tailWord_1107912) baseStart_1107912 baseEnd_1107912 := by
    simpa [prefixWord, tailWord_1107912, baseEnd_1107912] using wordTrace_append hprefix tailTrace_1107912
  have hstable : (prefixWord ++ tailWord_1107912).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1107912).length < 2 ^ (prefixWord ++ tailWord_1107912).sum := by decide
  have hdescent : baseEnd_1107912 < baseStart_1107912 := by decide
  rcases family_descends (prefixWord ++ tailWord_1107912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1107915 : List Nat := [1, 1, 1, 1, 3, 4, 5, 2, 3]
def baseStart_1107915 : Nat := 118140960795 + 1107915 * 2 ^ 59
def prefixEnd_1107915 : Nat := 4983230072969 + 3 ^ 40 * 1107915 * 2
def baseEnd_1107915 : Nat := 252841297478283560518799

theorem tailTrace_1107915 : CollatzResearch.WordTrace tailWord_1107915 prefixEnd_1107915 252841297478283560518799 := by
  unfold tailWord_1107915
  simp only [CollatzResearch.WordTrace]
  refine ⟨40408979781220646662789199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26939319854147097775192799 40408979781220646662789199)
  ·
    refine ⟨60613469671830969994183799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40408979781220646662789199 60613469671830969994183799)
    ·
      refine ⟨90920204507746454991275699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60613469671830969994183799 90920204507746454991275699)
      ·
        refine ⟨136380306761619682486913549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90920204507746454991275699 136380306761619682486913549)
        ·
          refine ⟨51142615035607380932592581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 136380306761619682486913549 51142615035607380932592581)
          ·
            refine ⟨9589240319176383924861109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 51142615035607380932592581 9589240319176383924861109)
            ·
              refine ⟨898991279922785992955729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 9589240319176383924861109 898991279922785992955729)
              ·
                refine ⟨674243459942089494716797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 898991279922785992955729 674243459942089494716797)
                ·
                  refine ⟨252841297478283560518799, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 674243459942089494716797 252841297478283560518799)
                  ·
                    rfl

theorem cell21_1107915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 5, 2, 3].length) (baseStart_1107915 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1107915 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1107915 prefixEnd_1107915 := by exact prefixLift 1107915
  have htrace : WordTrace (prefixWord ++ tailWord_1107915) baseStart_1107915 baseEnd_1107915 := by
    simpa [prefixWord, tailWord_1107915, baseEnd_1107915] using wordTrace_append hprefix tailTrace_1107915
  have hstable : (prefixWord ++ tailWord_1107915).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1107915).length < 2 ^ (prefixWord ++ tailWord_1107915).sum := by decide
  have hdescent : baseEnd_1107915 < baseStart_1107915 := by decide
  rcases family_descends (prefixWord ++ tailWord_1107915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1107929 : List Nat := [1, 2, 1, 2, 6, 1, 1, 3, 4]
def baseStart_1107929 : Nat := 118140960795 + 1107929 * 2 ^ 59
def prefixEnd_1107929 : Nat := 4983230072969 + 3 ^ 40 * 1107929 * 2
def baseEnd_1107929 : Nat := 252844492469022647285437

theorem tailTrace_1107929 : CollatzResearch.WordTrace tailWord_1107929 prefixEnd_1107929 252844492469022647285437 := by
  unfold tailWord_1107929
  simp only [CollatzResearch.WordTrace]
  refine ⟨40409490403169927053798841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26939660268779951369199227 40409490403169927053798841)
  ·
    refine ⟨30307117802377445290349131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40409490403169927053798841 30307117802377445290349131)
    ·
      refine ⟨45460676703566167935523697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30307117802377445290349131 45460676703566167935523697)
      ·
        refine ⟨34095507527674625951642773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45460676703566167935523697 34095507527674625951642773)
        ·
          refine ⟨1598226915359748091483255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 34095507527674625951642773 1598226915359748091483255)
          ·
            refine ⟨2397340373039622137224883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1598226915359748091483255 2397340373039622137224883)
            ·
              refine ⟨3596010559559433205837325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2397340373039622137224883 3596010559559433205837325)
              ·
                refine ⟨1348503959834787452188997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3596010559559433205837325 1348503959834787452188997)
                ·
                  refine ⟨252844492469022647285437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1348503959834787452188997 252844492469022647285437)
                  ·
                    rfl

theorem cell21_1107929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 1, 1, 3, 4].length) (baseStart_1107929 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1107929 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1107929 prefixEnd_1107929 := by exact prefixLift 1107929
  have htrace : WordTrace (prefixWord ++ tailWord_1107929) baseStart_1107929 baseEnd_1107929 := by
    simpa [prefixWord, tailWord_1107929, baseEnd_1107929] using wordTrace_append hprefix tailTrace_1107929
  have hstable : (prefixWord ++ tailWord_1107929).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1107929).length < 2 ^ (prefixWord ++ tailWord_1107929).sum := by decide
  have hdescent : baseEnd_1107929 < baseStart_1107929 := by decide
  rcases family_descends (prefixWord ++ tailWord_1107929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1107971 : List Nat := [1, 1, 1, 3, 2, 1, 1, 5, 6]
def baseStart_1107971 : Nat := 118140960795 + 1107971 * 2 ^ 59
def prefixEnd_1107971 : Nat := 4983230072969 + 3 ^ 40 * 1107971 * 2
def baseEnd_1107971 : Nat := 252854077441239907585351

theorem tailTrace_1107971 : CollatzResearch.WordTrace tailWord_1107971 prefixEnd_1107971 252854077441239907585351 := by
  unfold tailWord_1107971
  simp only [CollatzResearch.WordTrace]
  refine ⟨40411022269017768226827767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26940681512678512151218511 40411022269017768226827767)
  ·
    refine ⟨60616533403526652340241651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40411022269017768226827767 60616533403526652340241651)
    ·
      refine ⟨90924800105289978510362477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60616533403526652340241651 90924800105289978510362477)
      ·
        refine ⟨34096800039483741941385929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 90924800105289978510362477 34096800039483741941385929)
        ·
          refine ⟨25572600029612806456039447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34096800039483741941385929 25572600029612806456039447)
          ·
            refine ⟨38358900044419209684059171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25572600029612806456039447 38358900044419209684059171)
            ·
              refine ⟨57538350066628814526088757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38358900044419209684059171 57538350066628814526088757)
              ·
                refine ⟨5394220318746451361820821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 57538350066628814526088757 5394220318746451361820821)
                ·
                  refine ⟨252854077441239907585351, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5394220318746451361820821 252854077441239907585351)
                  ·
                    rfl

theorem cell21_1107971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 5, 6].length) (baseStart_1107971 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1107971 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1107971 prefixEnd_1107971 := by exact prefixLift 1107971
  have htrace : WordTrace (prefixWord ++ tailWord_1107971) baseStart_1107971 baseEnd_1107971 := by
    simpa [prefixWord, tailWord_1107971, baseEnd_1107971] using wordTrace_append hprefix tailTrace_1107971
  have hstable : (prefixWord ++ tailWord_1107971).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1107971).length < 2 ^ (prefixWord ++ tailWord_1107971).sum := by decide
  have hdescent : baseEnd_1107971 < baseStart_1107971 := by decide
  rcases family_descends (prefixWord ++ tailWord_1107971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1108154 : List Nat := [3, 1, 1, 1, 2, 2, 5, 6]
def baseStart_1108154 : Nat := 118140960795 + 1108154 * 2 ^ 59
def prefixEnd_1108154 : Nat := 4983230072969 + 3 ^ 40 * 1108154 * 2
def baseEnd_1108154 : Nat := 84298613511490752011659

theorem tailTrace_1108154 : CollatzResearch.WordTrace tailWord_1108154 prefixEnd_1108154 84298613511490752011659 := by
  unfold tailWord_1108154
  simp only [CollatzResearch.WordTrace]
  refine ⟨10104424206838697620184879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26945131218236526987159677 10104424206838697620184879)
  ·
    refine ⟨15156636310258046430277319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10104424206838697620184879 15156636310258046430277319)
    ·
      refine ⟨22734954465387069645415979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15156636310258046430277319 22734954465387069645415979)
      ·
        refine ⟨34102431698080604468123969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22734954465387069645415979 34102431698080604468123969)
        ·
          refine ⟨25576823773560453351092977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34102431698080604468123969 25576823773560453351092977)
          ·
            refine ⟨19182617830170340013319733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25576823773560453351092977 19182617830170340013319733)
            ·
              refine ⟨1798370421578469376248725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 19182617830170340013319733 1798370421578469376248725)
              ·
                refine ⟨84298613511490752011659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1798370421578469376248725 84298613511490752011659)
                ·
                  rfl

theorem cell21_1108154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 5, 6].length) (baseStart_1108154 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1108154 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1108154 prefixEnd_1108154 := by exact prefixLift 1108154
  have htrace : WordTrace (prefixWord ++ tailWord_1108154) baseStart_1108154 baseEnd_1108154 := by
    simpa [prefixWord, tailWord_1108154, baseEnd_1108154] using wordTrace_append hprefix tailTrace_1108154
  have hstable : (prefixWord ++ tailWord_1108154).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1108154).length < 2 ^ (prefixWord ++ tailWord_1108154).sum := by decide
  have hdescent : baseEnd_1108154 < baseStart_1108154 := by decide
  rcases family_descends (prefixWord ++ tailWord_1108154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1108188 : List Nat := [2, 2, 5, 2, 1, 1, 8]
def baseStart_1108188 : Nat := 118140960795 + 1108188 * 2 ^ 59
def prefixEnd_1108188 : Nat := 4983230072969 + 3 ^ 40 * 1108188 * 2
def baseEnd_1108188 : Nat := 28100399977521750274249

theorem tailTrace_1108188 : CollatzResearch.WordTrace tailWord_1108188 prefixEnd_1108188 28100399977521750274249 := by
  unfold tailWord_1108188
  simp only [CollatzResearch.WordTrace]
  refine ⟨20209468454615807143738609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26945957939487742858318145 20209468454615807143738609)
  ·
    refine ⟨15157101340961855357803957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20209468454615807143738609 15157101340961855357803957)
    ·
      refine ⟨1420978250715173939794121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 15157101340961855357803957 1420978250715173939794121)
      ·
        refine ⟨1065733688036380454845591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1420978250715173939794121 1065733688036380454845591)
        ·
          refine ⟨1598600532054570682268387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1065733688036380454845591 1598600532054570682268387)
          ·
            refine ⟨2397900798081856023402581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1598600532054570682268387 2397900798081856023402581)
            ·
              refine ⟨28100399977521750274249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2397900798081856023402581 28100399977521750274249)
              ·
                rfl

theorem cell21_1108188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 1, 8].length) (baseStart_1108188 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1108188 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1108188 prefixEnd_1108188 := by exact prefixLift 1108188
  have htrace : WordTrace (prefixWord ++ tailWord_1108188) baseStart_1108188 baseEnd_1108188 := by
    simpa [prefixWord, tailWord_1108188, baseEnd_1108188] using wordTrace_append hprefix tailTrace_1108188
  have hstable : (prefixWord ++ tailWord_1108188).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1108188).length < 2 ^ (prefixWord ++ tailWord_1108188).sum := by decide
  have hdescent : baseEnd_1108188 < baseStart_1108188 := by decide
  rcases family_descends (prefixWord ++ tailWord_1108188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1108202 : List Nat := [3, 1, 3, 1, 1, 2, 1, 6, 3]
def baseStart_1108202 : Nat := 118140960795 + 1108202 * 2 ^ 59
def prefixEnd_1108202 : Nat := 4983230072969 + 3 ^ 40 * 1108202 * 2
def baseEnd_1108202 : Nat := 252906794788434839234879

theorem tailTrace_1108202 : CollatzResearch.WordTrace tailWord_1108202 prefixEnd_1108202 252906794788434839234879 := by
  unfold tailWord_1108202
  simp only [CollatzResearch.WordTrace]
  refine ⟨10104861882795223669621715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26946298354120596452324573 10104861882795223669621715)
  ·
    refine ⟨15157292824192835504432573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10104861882795223669621715 15157292824192835504432573)
    ·
      refine ⟨5683984809072313314162215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15157292824192835504432573 5683984809072313314162215)
      ·
        refine ⟨8525977213608469971243323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5683984809072313314162215 8525977213608469971243323)
        ·
          refine ⟨12788965820412704956864985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8525977213608469971243323 12788965820412704956864985)
          ·
            refine ⟨9591724365309528717648739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12788965820412704956864985 9591724365309528717648739)
            ·
              refine ⟨14387586547964293076473109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9591724365309528717648739 14387586547964293076473109)
              ·
                refine ⟨674418119435826237959677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 14387586547964293076473109 674418119435826237959677)
                ·
                  refine ⟨252906794788434839234879, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 674418119435826237959677 252906794788434839234879)
                  ·
                    rfl

theorem cell21_1108202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 1, 6, 3].length) (baseStart_1108202 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1108202 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1108202 prefixEnd_1108202 := by exact prefixLift 1108202
  have htrace : WordTrace (prefixWord ++ tailWord_1108202) baseStart_1108202 baseEnd_1108202 := by
    simpa [prefixWord, tailWord_1108202, baseEnd_1108202] using wordTrace_append hprefix tailTrace_1108202
  have hstable : (prefixWord ++ tailWord_1108202).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1108202).length < 2 ^ (prefixWord ++ tailWord_1108202).sum := by decide
  have hdescent : baseEnd_1108202 < baseStart_1108202 := by decide
  rcases family_descends (prefixWord ++ tailWord_1108202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1108309 : List Nat := [1, 3, 2, 2, 4, 1, 2, 2, 4]
def baseStart_1108309 : Nat := 118140960795 + 1108309 * 2 ^ 59
def prefixEnd_1108309 : Nat := 4983230072969 + 3 ^ 40 * 1108309 * 2
def baseEnd_1108309 : Nat := 252931213646226430951327

theorem tailTrace_1108309 : CollatzResearch.WordTrace tailWord_1108309 prefixEnd_1108309 252931213646226430951327 := by
  unfold tailWord_1108309
  simp only [CollatzResearch.WordTrace]
  refine ⟨40423350141793251952631981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26948900094528834635087987 40423350141793251952631981)
  ·
    refine ⟨15158756303172469482236993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40423350141793251952631981 15158756303172469482236993)
    ·
      refine ⟨11369067227379352111677745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15158756303172469482236993 11369067227379352111677745)
      ·
        refine ⟨8526800420534514083758309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11369067227379352111677745 8526800420534514083758309)
        ·
          refine ⟨1598775078850221390704683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8526800420534514083758309 1598775078850221390704683)
          ·
            refine ⟨2398162618275332086057025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1598775078850221390704683 2398162618275332086057025)
            ·
              refine ⟨1798621963706499064542769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2398162618275332086057025 1798621963706499064542769)
              ·
                refine ⟨1348966472779874298407077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1798621963706499064542769 1348966472779874298407077)
                ·
                  refine ⟨252931213646226430951327, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1348966472779874298407077 252931213646226430951327)
                  ·
                    rfl

theorem cell21_1108309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 1, 2, 2, 4].length) (baseStart_1108309 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1108309 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1108309 prefixEnd_1108309 := by exact prefixLift 1108309
  have htrace : WordTrace (prefixWord ++ tailWord_1108309) baseStart_1108309 baseEnd_1108309 := by
    simpa [prefixWord, tailWord_1108309, baseEnd_1108309] using wordTrace_append hprefix tailTrace_1108309
  have hstable : (prefixWord ++ tailWord_1108309).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1108309).length < 2 ^ (prefixWord ++ tailWord_1108309).sum := by decide
  have hdescent : baseEnd_1108309 < baseStart_1108309 := by decide
  rcases family_descends (prefixWord ++ tailWord_1108309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1108427 : List Nat := [1, 1, 1, 1, 3, 3, 1, 6, 4]
def baseStart_1108427 : Nat := 118140960795 + 1108427 * 2 ^ 59
def prefixEnd_1108427 : Nat := 4983230072969 + 3 ^ 40 * 1108427 * 2
def baseEnd_1108427 : Nat := 252958142853884447984419

theorem tailTrace_1108427 : CollatzResearch.WordTrace tailWord_1108427 prefixEnd_1108427 252958142853884447984419 := by
  unfold tailWord_1108427
  simp only [CollatzResearch.WordTrace]
  refine ⟨40427653955365758105427535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26951769303577172070285023 40427653955365758105427535)
  ·
    refine ⟨60641480933048637158141303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40427653955365758105427535 60641480933048637158141303)
    ·
      refine ⟨90962221399572955737211955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60641480933048637158141303 90962221399572955737211955)
      ·
        refine ⟨136443332099359433605817933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90962221399572955737211955 136443332099359433605817933)
        ·
          refine ⟨51166249537259787602181725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 136443332099359433605817933 51166249537259787602181725)
          ·
            refine ⟨19187343576472420350818147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 51166249537259787602181725 19187343576472420350818147)
            ·
              refine ⟨28781015364708630526227221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19187343576472420350818147 28781015364708630526227221)
              ·
                refine ⟨1349110095220717055916901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 28781015364708630526227221 1349110095220717055916901)
                ·
                  refine ⟨252958142853884447984419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1349110095220717055916901 252958142853884447984419)
                  ·
                    rfl

theorem cell21_1108427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 6, 4].length) (baseStart_1108427 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1108427 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1108427 prefixEnd_1108427 := by exact prefixLift 1108427
  have htrace : WordTrace (prefixWord ++ tailWord_1108427) baseStart_1108427 baseEnd_1108427 := by
    simpa [prefixWord, tailWord_1108427, baseEnd_1108427] using wordTrace_append hprefix tailTrace_1108427
  have hstable : (prefixWord ++ tailWord_1108427).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1108427).length < 2 ^ (prefixWord ++ tailWord_1108427).sum := by decide
  have hdescent : baseEnd_1108427 < baseStart_1108427 := by decide
  rcases family_descends (prefixWord ++ tailWord_1108427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1108458 : List Nat := [3, 1, 3, 1, 3, 1, 2, 7]
def baseStart_1108458 : Nat := 118140960795 + 1108458 * 2 ^ 59
def prefixEnd_1108458 : Nat := 4983230072969 + 3 ^ 40 * 1108458 * 2
def baseEnd_1108458 : Nat := 84321739158745094322563

theorem tailTrace_1108458 : CollatzResearch.WordTrace tailWord_1108458 prefixEnd_1108458 84321739158745094322563 := by
  unfold tailWord_1108458
  simp only [CollatzResearch.WordTrace]
  refine ⟨10107196154563362599951507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26952523078835633599870685 10107196154563362599951507)
  ·
    refine ⟨15160794231845043899927261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10107196154563362599951507 15160794231845043899927261)
    ·
      refine ⟨5685297836941891462472723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15160794231845043899927261 5685297836941891462472723)
      ·
        refine ⟨8527946755412837193709085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5685297836941891462472723 8527946755412837193709085)
        ·
          refine ⟨3197980033279813947640907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8527946755412837193709085 3197980033279813947640907)
          ·
            refine ⟨4796970049919720921461361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3197980033279813947640907 4796970049919720921461361)
            ·
              refine ⟨3597727537439790691096021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4796970049919720921461361 3597727537439790691096021)
              ·
                refine ⟨84321739158745094322563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3597727537439790691096021 84321739158745094322563)
                ·
                  rfl

theorem cell21_1108458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 2, 7].length) (baseStart_1108458 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1108458 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1108458 prefixEnd_1108458 := by exact prefixLift 1108458
  have htrace : WordTrace (prefixWord ++ tailWord_1108458) baseStart_1108458 baseEnd_1108458 := by
    simpa [prefixWord, tailWord_1108458, baseEnd_1108458] using wordTrace_append hprefix tailTrace_1108458
  have hstable : (prefixWord ++ tailWord_1108458).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1108458).length < 2 ^ (prefixWord ++ tailWord_1108458).sum := by decide
  have hdescent : baseEnd_1108458 < baseStart_1108458 := by decide
  rcases family_descends (prefixWord ++ tailWord_1108458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1108517 : List Nat := [1, 3, 1, 2, 2, 1, 2, 9]
def baseStart_1108517 : Nat := 118140960795 + 1108517 * 2 ^ 59
def prefixEnd_1108517 : Nat := 4983230072969 + 3 ^ 40 * 1108517 * 2
def baseEnd_1108517 : Nat := 84326227360021430494745

theorem tailTrace_1108517 : CollatzResearch.WordTrace tailWord_1108517 prefixEnd_1108517 84326227360021430494745 := by
  unfold tailWord_1108517
  simp only [CollatzResearch.WordTrace]
  refine ⟨40430936525039703476203805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26953957683359802317469203 40430936525039703476203805)
  ·
    refine ⟨15161601196889888803576427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40430936525039703476203805 15161601196889888803576427)
    ·
      refine ⟨22742401795334833205364641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15161601196889888803576427 22742401795334833205364641)
      ·
        refine ⟨17056801346501124904023481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22742401795334833205364641 17056801346501124904023481)
        ·
          refine ⟨12792601009875843678017611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17056801346501124904023481 12792601009875843678017611)
          ·
            refine ⟨19188901514813765517026417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12792601009875843678017611 19188901514813765517026417)
            ·
              refine ⟨14391676136110324137769813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19188901514813765517026417 14391676136110324137769813)
              ·
                refine ⟨84326227360021430494745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 14391676136110324137769813 84326227360021430494745)
                ·
                  rfl

theorem cell21_1108517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 2, 9].length) (baseStart_1108517 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1108517 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1108517 prefixEnd_1108517 := by exact prefixLift 1108517
  have htrace : WordTrace (prefixWord ++ tailWord_1108517) baseStart_1108517 baseEnd_1108517 := by
    simpa [prefixWord, tailWord_1108517, baseEnd_1108517] using wordTrace_append hprefix tailTrace_1108517
  have hstable : (prefixWord ++ tailWord_1108517).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1108517).length < 2 ^ (prefixWord ++ tailWord_1108517).sum := by decide
  have hdescent : baseEnd_1108517 < baseStart_1108517 := by decide
  rcases family_descends (prefixWord ++ tailWord_1108517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1108574 : List Nat := [4, 4, 1, 2, 1, 2, 1, 3, 3]
def baseStart_1108574 : Nat := 118140960795 + 1108574 * 2 ^ 59
def prefixEnd_1108574 : Nat := 4983230072969 + 3 ^ 40 * 1108574 * 2
def baseEnd_1108574 : Nat := 252991690256644859034119

theorem tailTrace_1108574 : CollatzResearch.WordTrace tailWord_1108574 prefixEnd_1108574 252991690256644859034119 := by
  unfold tailWord_1108574
  simp only [CollatzResearch.WordTrace]
  refine ⟨5054126935729150276378597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 26955343657222134807352517 5054126935729150276378597)
  ·
    refine ⟨947648800449215676820987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5054126935729150276378597 947648800449215676820987)
    ·
      refine ⟨1421473200673823515231481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 947648800449215676820987 1421473200673823515231481)
      ·
        refine ⟨1066104900505367636423611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1421473200673823515231481 1066104900505367636423611)
        ·
          refine ⟨1599157350758051454635417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1066104900505367636423611 1599157350758051454635417)
          ·
            refine ⟨1199368013068538590976563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1599157350758051454635417 1199368013068538590976563)
            ·
              refine ⟨1799052019602807886464845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1199368013068538590976563 1799052019602807886464845)
              ·
                refine ⟨674644507351052957424317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1799052019602807886464845 674644507351052957424317)
                ·
                  refine ⟨252991690256644859034119, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 674644507351052957424317 252991690256644859034119)
                  ·
                    rfl

theorem cell21_1108574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 2, 1, 3, 3].length) (baseStart_1108574 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1108574 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1108574 prefixEnd_1108574 := by exact prefixLift 1108574
  have htrace : WordTrace (prefixWord ++ tailWord_1108574) baseStart_1108574 baseEnd_1108574 := by
    simpa [prefixWord, tailWord_1108574, baseEnd_1108574] using wordTrace_append hprefix tailTrace_1108574
  have hstable : (prefixWord ++ tailWord_1108574).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1108574).length < 2 ^ (prefixWord ++ tailWord_1108574).sum := by decide
  have hdescent : baseEnd_1108574 < baseStart_1108574 := by decide
  rcases family_descends (prefixWord ++ tailWord_1108574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1108613 : List Nat := [1, 3, 1, 1, 4, 4, 2, 1, 4]
def baseStart_1108613 : Nat := 118140960795 + 1108613 * 2 ^ 59
def prefixEnd_1108613 : Nat := 4983230072969 + 3 ^ 40 * 1108613 * 2
def baseEnd_1108613 : Nat := 253000590587989457884039

theorem tailTrace_1108613 : CollatzResearch.WordTrace tailWord_1108613 prefixEnd_1108613 253000590587989457884039 := by
  unfold tailWord_1108613
  simp only [CollatzResearch.WordTrace]
  refine ⟨40434437932691911871698493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26956291955127941247798995 40434437932691911871698493)
  ·
    refine ⟨15162914224759466951886935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40434437932691911871698493 15162914224759466951886935)
    ·
      refine ⟨22744371337139200427830403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15162914224759466951886935 22744371337139200427830403)
      ·
        refine ⟨34116557005708800641745605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22744371337139200427830403 34116557005708800641745605)
        ·
          refine ⟨6396854438570400120327301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 34116557005708800641745605 6396854438570400120327301)
          ·
            refine ⟨1199410207231950022561369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6396854438570400120327301 1199410207231950022561369)
            ·
              refine ⟨899557655423962516921027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1199410207231950022561369 899557655423962516921027)
              ·
                refine ⟨1349336483135943775381541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 899557655423962516921027 1349336483135943775381541)
                ·
                  refine ⟨253000590587989457884039, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1349336483135943775381541 253000590587989457884039)
                  ·
                    rfl

theorem cell21_1108613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 4, 2, 1, 4].length) (baseStart_1108613 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1108613 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1108613 prefixEnd_1108613 := by exact prefixLift 1108613
  have htrace : WordTrace (prefixWord ++ tailWord_1108613) baseStart_1108613 baseEnd_1108613 := by
    simpa [prefixWord, tailWord_1108613, baseEnd_1108613] using wordTrace_append hprefix tailTrace_1108613
  have hstable : (prefixWord ++ tailWord_1108613).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1108613).length < 2 ^ (prefixWord ++ tailWord_1108613).sum := by decide
  have hdescent : baseEnd_1108613 < baseStart_1108613 := by decide
  rcases family_descends (prefixWord ++ tailWord_1108613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1108650 : List Nat := [3, 1, 5, 2, 2, 1, 2, 2, 3]
def baseStart_1108650 : Nat := 118140960795 + 1108650 * 2 ^ 59
def prefixEnd_1108650 : Nat := 4983230072969 + 3 ^ 40 * 1108650 * 2
def baseEnd_1108650 : Nat := 253009034492085615767297

theorem tailTrace_1108650 : CollatzResearch.WordTrace tailWord_1108650 prefixEnd_1108650 253009034492085615767297 := by
  unfold tailWord_1108650
  simp only [CollatzResearch.WordTrace]
  refine ⟨10108946858389466797698851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26957191622371911460530269 10108946858389466797698851)
  ·
    refine ⟨15163420287584200196548277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10108946858389466797698851 15163420287584200196548277)
    ·
      refine ⟨1421570651961018768426401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 15163420287584200196548277 1421570651961018768426401)
      ·
        refine ⟨1066177988970764076319801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1421570651961018768426401 1066177988970764076319801)
        ·
          refine ⟨799633491728073057239851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1066177988970764076319801 799633491728073057239851)
          ·
            refine ⟨1199450237592109585859777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 799633491728073057239851 1199450237592109585859777)
            ·
              refine ⟨899587678194082189394833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1199450237592109585859777 899587678194082189394833)
              ·
                refine ⟨674690758645561642046125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 899587678194082189394833 674690758645561642046125)
                ·
                  refine ⟨253009034492085615767297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 674690758645561642046125 253009034492085615767297)
                  ·
                    rfl

theorem cell21_1108650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 2, 1, 2, 2, 3].length) (baseStart_1108650 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1108650 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1108650 prefixEnd_1108650 := by exact prefixLift 1108650
  have htrace : WordTrace (prefixWord ++ tailWord_1108650) baseStart_1108650 baseEnd_1108650 := by
    simpa [prefixWord, tailWord_1108650, baseEnd_1108650] using wordTrace_append hprefix tailTrace_1108650
  have hstable : (prefixWord ++ tailWord_1108650).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1108650).length < 2 ^ (prefixWord ++ tailWord_1108650).sum := by decide
  have hdescent : baseEnd_1108650 < baseStart_1108650 := by decide
  rcases family_descends (prefixWord ++ tailWord_1108650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1108655 : List Nat := [1, 1, 2, 1, 2, 5, 1, 4, 4]
def baseStart_1108655 : Nat := 118140960795 + 1108655 * 2 ^ 59
def prefixEnd_1108655 : Nat := 4983230072969 + 3 ^ 40 * 1108655 * 2
def baseEnd_1108655 : Nat := 253010175560206718183953

theorem tailTrace_1108655 : CollatzResearch.WordTrace tailWord_1108655 prefixEnd_1108655 253010175560206718183953 := by
  unfold tailWord_1108655
  simp only [CollatzResearch.WordTrace]
  refine ⟨40435969798539753044727419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26957313199026502029818279 40435969798539753044727419)
  ·
    refine ⟨60653954697809629567091129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40435969798539753044727419 60653954697809629567091129)
    ·
      refine ⟨45490466023357222175318347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60653954697809629567091129 45490466023357222175318347)
      ·
        refine ⟨68235699035035833262977521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45490466023357222175318347 68235699035035833262977521)
        ·
          refine ⟨51176774276276874947233141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 68235699035035833262977521 51176774276276874947233141)
          ·
            refine ⟨4797822588400957026303107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 51176774276276874947233141 4797822588400957026303107)
            ·
              refine ⟨7196733882601435539454661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4797822588400957026303107 7196733882601435539454661)
              ·
                refine ⟨1349387602987769163647749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7196733882601435539454661 1349387602987769163647749)
                ·
                  refine ⟨253010175560206718183953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1349387602987769163647749 253010175560206718183953)
                  ·
                    rfl

theorem cell21_1108655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 1, 4, 4].length) (baseStart_1108655 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1108655 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1108655 prefixEnd_1108655 := by exact prefixLift 1108655
  have htrace : WordTrace (prefixWord ++ tailWord_1108655) baseStart_1108655 baseEnd_1108655 := by
    simpa [prefixWord, tailWord_1108655, baseEnd_1108655] using wordTrace_append hprefix tailTrace_1108655
  have hstable : (prefixWord ++ tailWord_1108655).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1108655).length < 2 ^ (prefixWord ++ tailWord_1108655).sum := by decide
  have hdescent : baseEnd_1108655 < baseStart_1108655 := by decide
  rcases family_descends (prefixWord ++ tailWord_1108655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1108717 : List Nat := [1, 5, 1, 2, 1, 1, 4, 1, 5]
def baseStart_1108717 : Nat := 118140960795 + 1108717 * 2 ^ 59
def prefixEnd_1108717 : Nat := 4983230072969 + 3 ^ 40 * 1108717 * 2
def baseEnd_1108717 : Nat := 253024324804908388150493

theorem tailTrace_1108717 : CollatzResearch.WordTrace tailWord_1108717 prefixEnd_1108717 253024324804908388150493 := by
  unfold tailWord_1108717
  simp only [CollatzResearch.WordTrace]
  refine ⟨40438231124315137633484405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26958820749543425088989603 40438231124315137633484405)
  ·
    refine ⟨3791084167904544153139163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 40438231124315137633484405 3791084167904544153139163)
    ·
      refine ⟨5686626251856816229708745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3791084167904544153139163 5686626251856816229708745)
      ·
        refine ⟨4264969688892612172281559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5686626251856816229708745 4264969688892612172281559)
        ·
          refine ⟨6397454533338918258422339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4264969688892612172281559 6397454533338918258422339)
          ·
            refine ⟨9596181800008377387633509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6397454533338918258422339 9596181800008377387633509)
            ·
              refine ⟨1799284087501570760181283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9596181800008377387633509 1799284087501570760181283)
              ·
                refine ⟨2698926131252356140271925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1799284087501570760181283 2698926131252356140271925)
                ·
                  refine ⟨253024324804908388150493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2698926131252356140271925 253024324804908388150493)
                  ·
                    rfl

theorem cell21_1108717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 4, 1, 5].length) (baseStart_1108717 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1108717 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1108717 prefixEnd_1108717 := by exact prefixLift 1108717
  have htrace : WordTrace (prefixWord ++ tailWord_1108717) baseStart_1108717 baseEnd_1108717 := by
    simpa [prefixWord, tailWord_1108717, baseEnd_1108717] using wordTrace_append hprefix tailTrace_1108717
  have hstable : (prefixWord ++ tailWord_1108717).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1108717).length < 2 ^ (prefixWord ++ tailWord_1108717).sum := by decide
  have hdescent : baseEnd_1108717 < baseStart_1108717 := by decide
  rcases family_descends (prefixWord ++ tailWord_1108717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1108782 : List Nat := [4, 1, 3, 2, 1, 3, 2, 1, 4]
def baseStart_1108782 : Nat := 118140960795 + 1108782 * 2 ^ 59
def prefixEnd_1108782 : Nat := 4983230072969 + 3 ^ 40 * 1108782 * 2
def baseEnd_1108782 : Nat := 253039158690482719567027

theorem tailTrace_1108782 : CollatzResearch.WordTrace tailWord_1108782 prefixEnd_1108782 253039158690482719567027 := by
  unfold tailWord_1108782
  simp only [CollatzResearch.WordTrace]
  refine ⟨5055075233634956716825075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 26960401246053102489733733 5055075233634956716825075)
  ·
    refine ⟨7582612850452435075237613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5055075233634956716825075 7582612850452435075237613)
    ·
      refine ⟨2843479818919663153214105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7582612850452435075237613 2843479818919663153214105)
      ·
        refine ⟨2132609864189747364910579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2843479818919663153214105 2132609864189747364910579)
        ·
          refine ⟨3198914796284621047365869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2132609864189747364910579 3198914796284621047365869)
          ·
            refine ⟨1199593048606732892762201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3198914796284621047365869 1199593048606732892762201)
            ·
              refine ⟨899694786455049669571651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1199593048606732892762201 899694786455049669571651)
              ·
                refine ⟨1349542179682574504357477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 899694786455049669571651 1349542179682574504357477)
                ·
                  refine ⟨253039158690482719567027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1349542179682574504357477 253039158690482719567027)
                  ·
                    rfl

theorem cell21_1108782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 3, 2, 1, 4].length) (baseStart_1108782 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1108782 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1108782 prefixEnd_1108782 := by exact prefixLift 1108782
  have htrace : WordTrace (prefixWord ++ tailWord_1108782) baseStart_1108782 baseEnd_1108782 := by
    simpa [prefixWord, tailWord_1108782, baseEnd_1108782] using wordTrace_append hprefix tailTrace_1108782
  have hstable : (prefixWord ++ tailWord_1108782).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1108782).length < 2 ^ (prefixWord ++ tailWord_1108782).sum := by decide
  have hdescent : baseEnd_1108782 < baseStart_1108782 := by decide
  rcases family_descends (prefixWord ++ tailWord_1108782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1108869 : List Nat := [1, 3, 1, 1, 3, 3, 1, 5, 3]
def baseStart_1108869 : Nat := 118140960795 + 1108869 * 2 ^ 59
def prefixEnd_1108869 : Nat := 4983230072969 + 3 ^ 40 * 1108869 * 2
def baseEnd_1108869 : Nat := 253059013275789901616849

theorem tailTrace_1108869 : CollatzResearch.WordTrace tailWord_1108869 prefixEnd_1108869 253059013275789901616849 := by
  unfold tailWord_1108869
  simp only [CollatzResearch.WordTrace]
  refine ⟨40443775019764467593017661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26962516679842978395345107 40443775019764467593017661)
  ·
    refine ⟨15166415632411675347381623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40443775019764467593017661 15166415632411675347381623)
    ·
      refine ⟨22749623448617513021072435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15166415632411675347381623 22749623448617513021072435)
      ·
        refine ⟨34124435172926269531608653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22749623448617513021072435 34124435172926269531608653)
        ·
          refine ⟨12796663189847351074353245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34124435172926269531608653 12796663189847351074353245)
          ·
            refine ⟨4798748696192756652882467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12796663189847351074353245 4798748696192756652882467)
            ·
              refine ⟨7198123044289134979323701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4798748696192756652882467 7198123044289134979323701)
              ·
                refine ⟨674824035402106404311597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7198123044289134979323701 674824035402106404311597)
                ·
                  refine ⟨253059013275789901616849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 674824035402106404311597 253059013275789901616849)
                  ·
                    rfl

theorem cell21_1108869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 1, 5, 3].length) (baseStart_1108869 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1108869 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1108869 prefixEnd_1108869 := by exact prefixLift 1108869
  have htrace : WordTrace (prefixWord ++ tailWord_1108869) baseStart_1108869 baseEnd_1108869 := by
    simpa [prefixWord, tailWord_1108869, baseEnd_1108869] using wordTrace_append hprefix tailTrace_1108869
  have hstable : (prefixWord ++ tailWord_1108869).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1108869).length < 2 ^ (prefixWord ++ tailWord_1108869).sum := by decide
  have hdescent : baseEnd_1108869 < baseStart_1108869 := by decide
  rcases family_descends (prefixWord ++ tailWord_1108869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1108900 : List Nat := [2, 3, 1, 2, 1, 2, 5, 1, 4]
def baseStart_1108900 : Nat := 118140960795 + 1108900 * 2 ^ 59
def prefixEnd_1108900 : Nat := 4983230072969 + 3 ^ 40 * 1108900 * 2
def baseEnd_1108900 : Nat := 253066087898140736600119

theorem tailTrace_1108900 : CollatzResearch.WordTrace tailWord_1108900 prefixEnd_1108900 253066087898140736600119 := by
  unfold tailWord_1108900
  simp only [CollatzResearch.WordTrace]
  refine ⟨20222452841326079943698077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26963270455101439924930769 20222452841326079943698077)
  ·
    refine ⟨7583419815497279978886779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20222452841326079943698077 7583419815497279978886779)
    ·
      refine ⟨11375129723245919968330169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7583419815497279978886779 11375129723245919968330169)
      ·
        refine ⟨8531347292434439976247627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11375129723245919968330169 8531347292434439976247627)
        ·
          refine ⟨12797020938651659964371441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8531347292434439976247627 12797020938651659964371441)
          ·
            refine ⟨9597765703988744973278581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12797020938651659964371441 9597765703988744973278581)
            ·
              refine ⟨899790534748944841244867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 9597765703988744973278581 899790534748944841244867)
              ·
                refine ⟨1349685802123417261867301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 899790534748944841244867 1349685802123417261867301)
                ·
                  refine ⟨253066087898140736600119, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1349685802123417261867301 253066087898140736600119)
                  ·
                    rfl

theorem cell21_1108900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 5, 1, 4].length) (baseStart_1108900 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1108900 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1108900 prefixEnd_1108900 := by exact prefixLift 1108900
  have htrace : WordTrace (prefixWord ++ tailWord_1108900) baseStart_1108900 baseEnd_1108900 := by
    simpa [prefixWord, tailWord_1108900, baseEnd_1108900] using wordTrace_append hprefix tailTrace_1108900
  have hstable : (prefixWord ++ tailWord_1108900).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1108900).length < 2 ^ (prefixWord ++ tailWord_1108900).sum := by decide
  have hdescent : baseEnd_1108900 < baseStart_1108900 := by decide
  rcases family_descends (prefixWord ++ tailWord_1108900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1108911 : List Nat := [1, 1, 2, 1, 2, 2, 2, 3, 7]
def baseStart_1108911 : Nat := 118140960795 + 1108911 * 2 ^ 59
def prefixEnd_1108911 : Nat := 4983230072969 + 3 ^ 40 * 1108911 * 2
def baseEnd_1108911 : Nat := 253068598248007161916763

theorem tailTrace_1108911 : CollatzResearch.WordTrace tailWord_1108911 prefixEnd_1108911 253068598248007161916763 := by
  unfold tailWord_1108911
  simp only [CollatzResearch.WordTrace]
  refine ⟨40445306885612308766046587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26963537923741539177364391 40445306885612308766046587)
  ·
    refine ⟨60667960328418463149069881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40445306885612308766046587 60667960328418463149069881)
    ·
      refine ⟨45500970246313847361802411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60667960328418463149069881 45500970246313847361802411)
      ·
        refine ⟨68251455369470771042703617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45500970246313847361802411 68251455369470771042703617)
        ·
          refine ⟨51188591527103078282027713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 68251455369470771042703617 51188591527103078282027713)
          ·
            refine ⟨38391443645327308711520785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51188591527103078282027713 38391443645327308711520785)
            ·
              refine ⟨28793582733995481533640589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38391443645327308711520785 28793582733995481533640589)
              ·
                refine ⟨10797593525248305575115221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28793582733995481533640589 10797593525248305575115221)
                ·
                  refine ⟨253068598248007161916763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10797593525248305575115221 253068598248007161916763)
                  ·
                    rfl

theorem cell21_1108911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 3, 7].length) (baseStart_1108911 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1108911 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1108911 prefixEnd_1108911 := by exact prefixLift 1108911
  have htrace : WordTrace (prefixWord ++ tailWord_1108911) baseStart_1108911 baseEnd_1108911 := by
    simpa [prefixWord, tailWord_1108911, baseEnd_1108911] using wordTrace_append hprefix tailTrace_1108911
  have hstable : (prefixWord ++ tailWord_1108911).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1108911).length < 2 ^ (prefixWord ++ tailWord_1108911).sum := by decide
  have hdescent : baseEnd_1108911 < baseStart_1108911 := by decide
  rcases family_descends (prefixWord ++ tailWord_1108911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1108990 : List Nat := [4, 2, 2, 2, 2, 9]
def baseStart_1108990 : Nat := 118140960795 + 1108990 * 2 ^ 59
def prefixEnd_1108990 : Nat := 4983230072969 + 3 ^ 40 * 1108990 * 2
def baseEnd_1108990 : Nat := 9373578782382243707405

theorem tailTrace_1108990 : CollatzResearch.WordTrace tailWord_1108990 prefixEnd_1108990 9373578782382243707405 := by
  unfold tailWord_1108990
  simp only [CollatzResearch.WordTrace]
  refine ⟨5056023531540763157271553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 26965458834884070172114949 5056023531540763157271553)
  ·
    refine ⟨3792017648655572367953665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5056023531540763157271553 3792017648655572367953665)
    ·
      refine ⟨2844013236491679275965249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3792017648655572367953665 2844013236491679275965249)
      ·
        refine ⟨2133009927368759456973937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2844013236491679275965249 2133009927368759456973937)
        ·
          refine ⟨1599757445526569592730453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2133009927368759456973937 1599757445526569592730453)
          ·
            refine ⟨9373578782382243707405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1599757445526569592730453 9373578782382243707405)
            ·
              rfl

theorem cell21_1108990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 9].length) (baseStart_1108990 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1108990 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1108990 prefixEnd_1108990 := by exact prefixLift 1108990
  have htrace : WordTrace (prefixWord ++ tailWord_1108990) baseStart_1108990 baseEnd_1108990 := by
    simpa [prefixWord, tailWord_1108990, baseEnd_1108990] using wordTrace_append hprefix tailTrace_1108990
  have hstable : (prefixWord ++ tailWord_1108990).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1108990).length < 2 ^ (prefixWord ++ tailWord_1108990).sum := by decide
  have hdescent : baseEnd_1108990 < baseStart_1108990 := by decide
  rcases family_descends (prefixWord ++ tailWord_1108990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1109021 : List Nat := [1, 4, 2, 2, 3, 1, 1, 2, 5]
def baseStart_1109021 : Nat := 118140960795 + 1109021 * 2 ^ 59
def prefixEnd_1109021 : Nat := 4983230072969 + 3 ^ 40 * 1109021 * 2
def baseEnd_1109021 : Nat := 253093701746671415083205

theorem tailTrace_1109021 : CollatzResearch.WordTrace tailWord_1109021 prefixEnd_1109021 253093701746671415083205 := by
  unfold tailWord_1109021
  simp only [CollatzResearch.WordTrace]
  refine ⟨40449318915213797552550917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26966212610142531701700611 40449318915213797552550917)
  ·
    refine ⟨7584247296602587041103297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 40449318915213797552550917 7584247296602587041103297)
    ·
      refine ⟨5688185472451940280827473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7584247296602587041103297 5688185472451940280827473)
      ·
        refine ⟨4266139104338955210620605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5688185472451940280827473 4266139104338955210620605)
        ·
          refine ⟨1599802164127108203982727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4266139104338955210620605 1599802164127108203982727)
          ·
            refine ⟨2399703246190662305974091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1599802164127108203982727 2399703246190662305974091)
            ·
              refine ⟨3599554869285993458961137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2399703246190662305974091 3599554869285993458961137)
              ·
                refine ⟨2699666151964495094220853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3599554869285993458961137 2699666151964495094220853)
                ·
                  refine ⟨253093701746671415083205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2699666151964495094220853 253093701746671415083205)
                  ·
                    rfl

theorem cell21_1109021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 1, 1, 2, 5].length) (baseStart_1109021 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1109021 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1109021 prefixEnd_1109021 := by exact prefixLift 1109021
  have htrace : WordTrace (prefixWord ++ tailWord_1109021) baseStart_1109021 baseEnd_1109021 := by
    simpa [prefixWord, tailWord_1109021, baseEnd_1109021] using wordTrace_append hprefix tailTrace_1109021
  have hstable : (prefixWord ++ tailWord_1109021).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1109021).length < 2 ^ (prefixWord ++ tailWord_1109021).sum := by decide
  have hdescent : baseEnd_1109021 < baseStart_1109021 := by decide
  rcases family_descends (prefixWord ++ tailWord_1109021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1109038 : List Nat := [4, 1, 3, 1, 1, 1, 4, 3, 3]
def baseStart_1109038 : Nat := 118140960795 + 1109038 * 2 ^ 59
def prefixEnd_1109038 : Nat := 4983230072969 + 3 ^ 40 * 1109038 * 2
def baseEnd_1109038 : Nat := 253097581378283163299837

theorem tailTrace_1109038 : CollatzResearch.WordTrace tailWord_1109038 prefixEnd_1109038 253097581378283163299837 := by
  unfold tailWord_1109038
  simp only [CollatzResearch.WordTrace]
  refine ⟨5056242369519026181989971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 26966625970768139637279845 5056242369519026181989971)
  ·
    refine ⟨7584363554278539272984957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5056242369519026181989971 7584363554278539272984957)
    ·
      refine ⟨2844136332854452227369359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7584363554278539272984957 2844136332854452227369359)
      ·
        refine ⟨4266204499281678341054039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2844136332854452227369359 4266204499281678341054039)
        ·
          refine ⟨6399306748922517511581059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4266204499281678341054039 6399306748922517511581059)
          ·
            refine ⟨9598960123383776267371589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6399306748922517511581059 9598960123383776267371589)
            ·
              refine ⟨1799805023134458050132173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9598960123383776267371589 1799805023134458050132173)
              ·
                refine ⟨674926883675421768799565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1799805023134458050132173 674926883675421768799565)
                ·
                  refine ⟨253097581378283163299837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 674926883675421768799565 253097581378283163299837)
                  ·
                    rfl

theorem cell21_1109038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 4, 3, 3].length) (baseStart_1109038 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1109038 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1109038 prefixEnd_1109038 := by exact prefixLift 1109038
  have htrace : WordTrace (prefixWord ++ tailWord_1109038) baseStart_1109038 baseEnd_1109038 := by
    simpa [prefixWord, tailWord_1109038, baseEnd_1109038] using wordTrace_append hprefix tailTrace_1109038
  have hstable : (prefixWord ++ tailWord_1109038).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1109038).length < 2 ^ (prefixWord ++ tailWord_1109038).sum := by decide
  have hdescent : baseEnd_1109038 < baseStart_1109038 := by decide
  rcases family_descends (prefixWord ++ tailWord_1109038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1109049 : List Nat := [1, 2, 1, 5, 2, 2, 8]
def baseStart_1109049 : Nat := 118140960795 + 1109049 * 2 ^ 59
def prefixEnd_1109049 : Nat := 4983230072969 + 3 ^ 40 * 1109049 * 2
def baseEnd_1109049 : Nat := 28122232414238843179609

theorem tailTrace_1109049 : CollatzResearch.WordTrace tailWord_1109049 prefixEnd_1109049 28122232414238843179609 := by
  unfold tailWord_1109049
  simp only [CollatzResearch.WordTrace]
  refine ⟨40450340159112358334570201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26966893439408238889713467 40450340159112358334570201)
  ·
    refine ⟨30337755119334268750927651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40450340159112358334570201 30337755119334268750927651)
    ·
      refine ⟨45506632679001403126391477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30337755119334268750927651 45506632679001403126391477)
      ·
        refine ⟨4266246813656381543099201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 45506632679001403126391477 4266246813656381543099201)
        ·
          refine ⟨3199685110242286157324401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4266246813656381543099201 3199685110242286157324401)
          ·
            refine ⟨2399763832681714617993301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3199685110242286157324401 2399763832681714617993301)
            ·
              refine ⟨28122232414238843179609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2399763832681714617993301 28122232414238843179609)
              ·
                rfl

theorem cell21_1109049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 2, 8].length) (baseStart_1109049 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1109049 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1109049 prefixEnd_1109049 := by exact prefixLift 1109049
  have htrace : WordTrace (prefixWord ++ tailWord_1109049) baseStart_1109049 baseEnd_1109049 := by
    simpa [prefixWord, tailWord_1109049, baseEnd_1109049] using wordTrace_append hprefix tailTrace_1109049
  have hstable : (prefixWord ++ tailWord_1109049).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1109049).length < 2 ^ (prefixWord ++ tailWord_1109049).sum := by decide
  have hdescent : baseEnd_1109049 < baseStart_1109049 := by decide
  rcases family_descends (prefixWord ++ tailWord_1109049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1109052 : List Nat := [2, 2, 2, 2, 2, 4, 1, 2, 4]
def baseStart_1109052 : Nat := 118140960795 + 1109052 * 2 ^ 59
def prefixEnd_1109052 : Nat := 4983230072969 + 3 ^ 40 * 1109052 * 2
def baseEnd_1109052 : Nat := 253100776369022250066475

theorem tailTrace_1109052 : CollatzResearch.WordTrace tailWord_1109052 prefixEnd_1109052 253100776369022250066475 := by
  unfold tailWord_1109052
  simp only [CollatzResearch.WordTrace]
  refine ⟨20225224789050744923464705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26966966385400993231286273 20225224789050744923464705)
  ·
    refine ⟨15168918591788058692598529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20225224789050744923464705 15168918591788058692598529)
    ·
      refine ⟨11376688943841044019448897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15168918591788058692598529 11376688943841044019448897)
      ·
        refine ⟨8532516707880783014586673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11376688943841044019448897 8532516707880783014586673)
        ·
          refine ⟨6399387530910587260940005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8532516707880783014586673 6399387530910587260940005)
          ·
            refine ⟨1199885162045735111426251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6399387530910587260940005 1199885162045735111426251)
            ·
              refine ⟨1799827743068602667139377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1199885162045735111426251 1799827743068602667139377)
              ·
                refine ⟨1349870807301452000354533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1799827743068602667139377 1349870807301452000354533)
                ·
                  refine ⟨253100776369022250066475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1349870807301452000354533 253100776369022250066475)
                  ·
                    rfl

theorem cell21_1109052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 4, 1, 2, 4].length) (baseStart_1109052 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1109052 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1109052 prefixEnd_1109052 := by exact prefixLift 1109052
  have htrace : WordTrace (prefixWord ++ tailWord_1109052) baseStart_1109052 baseEnd_1109052 := by
    simpa [prefixWord, tailWord_1109052, baseEnd_1109052] using wordTrace_append hprefix tailTrace_1109052
  have hstable : (prefixWord ++ tailWord_1109052).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1109052).length < 2 ^ (prefixWord ++ tailWord_1109052).sum := by decide
  have hdescent : baseEnd_1109052 < baseStart_1109052 := by decide
  rcases family_descends (prefixWord ++ tailWord_1109052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1109069 : List Nat := [1, 6, 1, 1, 1, 3, 3, 1, 4]
def baseStart_1109069 : Nat := 118140960795 + 1109069 * 2 ^ 59
def prefixEnd_1109069 : Nat := 4983230072969 + 3 ^ 40 * 1109069 * 2
def baseEnd_1109069 : Nat := 253104656000633998283107

theorem tailTrace_1109069 : CollatzResearch.WordTrace tailWord_1109069 prefixEnd_1109069 253104656000633998283107 := by
  unfold tailWord_1109069
  simp only [CollatzResearch.WordTrace]
  refine ⟨40451069619039901750298261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26967379746026601166865507 40451069619039901750298261)
  ·
    refine ⟨1896143888392495394545231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 40451069619039901750298261 1896143888392495394545231)
    ·
      refine ⟨2844215832588743091817847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1896143888392495394545231 2844215832588743091817847)
      ·
        refine ⟨4266323748883114637726771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2844215832588743091817847 4266323748883114637726771)
        ·
          refine ⟨6399485623324671956590157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4266323748883114637726771 6399485623324671956590157)
          ·
            refine ⟨2399807108746751983721309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6399485623324671956590157 2399807108746751983721309)
            ·
              refine ⟨899927665780031993895491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2399807108746751983721309 899927665780031993895491)
              ·
                refine ⟨1349891498670047990843237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 899927665780031993895491 1349891498670047990843237)
                ·
                  refine ⟨253104656000633998283107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1349891498670047990843237 253104656000633998283107)
                  ·
                    rfl

theorem cell21_1109069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 3, 3, 1, 4].length) (baseStart_1109069 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1109069 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1109069 prefixEnd_1109069 := by exact prefixLift 1109069
  have htrace : WordTrace (prefixWord ++ tailWord_1109069) baseStart_1109069 baseEnd_1109069 := by
    simpa [prefixWord, tailWord_1109069, baseEnd_1109069] using wordTrace_append hprefix tailTrace_1109069
  have hstable : (prefixWord ++ tailWord_1109069).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1109069).length < 2 ^ (prefixWord ++ tailWord_1109069).sum := by decide
  have hdescent : baseEnd_1109069 < baseStart_1109069 := by decide
  rcases family_descends (prefixWord ++ tailWord_1109069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1109097 : List Nat := [1, 2, 1, 1, 1, 6, 3, 3, 3]
def baseStart_1109097 : Nat := 118140960795 + 1109097 * 2 ^ 59
def prefixEnd_1109097 : Nat := 4983230072969 + 3 ^ 40 * 1109097 * 2
def baseEnd_1109097 : Nat := 253111045982112171816383

theorem tailTrace_1109097 : CollatzResearch.WordTrace tailWord_1109097 prefixEnd_1109097 253111045982112171816383 := by
  unfold tailWord_1109097
  simp only [CollatzResearch.WordTrace]
  refine ⟨40452090862938462532317545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26968060575292308354878363 40452090862938462532317545)
  ·
    refine ⟨30339068147203846899238159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40452090862938462532317545 30339068147203846899238159)
    ·
      refine ⟨45508602220805770348857239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30339068147203846899238159 45508602220805770348857239)
      ·
        refine ⟨68262903331208655523285859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45508602220805770348857239 68262903331208655523285859)
        ·
          refine ⟨102394354996812983284928789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68262903331208655523285859 102394354996812983284928789)
          ·
            refine ⟨4799735390475608591481037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 102394354996812983284928789 4799735390475608591481037)
            ·
              refine ⟨1799900771428353221805389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4799735390475608591481037 1799900771428353221805389)
              ·
                refine ⟨674962789285632458177021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1799900771428353221805389 674962789285632458177021)
                ·
                  refine ⟨253111045982112171816383, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 674962789285632458177021 253111045982112171816383)
                  ·
                    rfl

theorem cell21_1109097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 3, 3, 3].length) (baseStart_1109097 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1109097 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1109097 prefixEnd_1109097 := by exact prefixLift 1109097
  have htrace : WordTrace (prefixWord ++ tailWord_1109097) baseStart_1109097 baseEnd_1109097 := by
    simpa [prefixWord, tailWord_1109097, baseEnd_1109097] using wordTrace_append hprefix tailTrace_1109097
  have hstable : (prefixWord ++ tailWord_1109097).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1109097).length < 2 ^ (prefixWord ++ tailWord_1109097).sum := by decide
  have hdescent : baseEnd_1109097 < baseStart_1109097 := by decide
  rcases family_descends (prefixWord ++ tailWord_1109097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1109128 : List Nat := [2, 1, 3, 4, 2, 1, 1, 3, 4]
def baseStart_1109128 : Nat := 118140960795 + 1109128 * 2 ^ 59
def prefixEnd_1109128 : Nat := 4983230072969 + 3 ^ 40 * 1109128 * 2
def baseEnd_1109128 : Nat := 253118120604463006799653

theorem tailTrace_1109128 : CollatzResearch.WordTrace tailWord_1109128 prefixEnd_1109128 253118120604463006799653 := by
  unfold tailWord_1109128
  simp only [CollatzResearch.WordTrace]
  refine ⟨20226610762913077413348019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26968814350550769884464025 20226610762913077413348019)
  ·
    refine ⟨30339916144369616120022029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20226610762913077413348019 30339916144369616120022029)
    ·
      refine ⟨11377468554138606045008261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30339916144369616120022029 11377468554138606045008261)
      ·
        refine ⟨2133275353900988633439049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11377468554138606045008261 2133275353900988633439049)
        ·
          refine ⟨1599956515425741475079287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2133275353900988633439049 1599956515425741475079287)
          ·
            refine ⟨2399934773138612212618931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1599956515425741475079287 2399934773138612212618931)
            ·
              refine ⟨3599902159707918318928397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2399934773138612212618931 3599902159707918318928397)
              ·
                refine ⟨1349963309890469369598149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3599902159707918318928397 1349963309890469369598149)
                ·
                  refine ⟨253118120604463006799653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1349963309890469369598149 253118120604463006799653)
                  ·
                    rfl

theorem cell21_1109128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 1, 1, 3, 4].length) (baseStart_1109128 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1109128 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1109128 prefixEnd_1109128 := by exact prefixLift 1109128
  have htrace : WordTrace (prefixWord ++ tailWord_1109128) baseStart_1109128 baseEnd_1109128 := by
    simpa [prefixWord, tailWord_1109128, baseEnd_1109128] using wordTrace_append hprefix tailTrace_1109128
  have hstable : (prefixWord ++ tailWord_1109128).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1109128).length < 2 ^ (prefixWord ++ tailWord_1109128).sum := by decide
  have hdescent : baseEnd_1109128 < baseStart_1109128 := by decide
  rcases family_descends (prefixWord ++ tailWord_1109128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1109139 : List Nat := [1, 1, 1, 2, 1, 2, 4, 4, 5]
def baseStart_1109139 : Nat := 118140960795 + 1109139 * 2 ^ 59
def prefixEnd_1109139 : Nat := 4983230072969 + 3 ^ 40 * 1109139 * 2
def baseEnd_1109139 : Nat := 253120630954329432116297

theorem tailTrace_1109139 : CollatzResearch.WordTrace tailWord_1109139 prefixEnd_1109139 253120630954329432116297 := by
  unfold tailWord_1109139
  simp only [CollatzResearch.WordTrace]
  refine ⟨40453622728786303705346471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26969081819190869136897647 40453622728786303705346471)
  ·
    refine ⟨60680434093179455558019707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40453622728786303705346471 60680434093179455558019707)
    ·
      refine ⟨91020651139769183337029561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60680434093179455558019707 91020651139769183337029561)
      ·
        refine ⟨68265488354826887502772171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 91020651139769183337029561 68265488354826887502772171)
        ·
          refine ⟨102398232532240331254158257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68265488354826887502772171 102398232532240331254158257)
          ·
            refine ⟨76798674399180248440618693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 102398232532240331254158257 76798674399180248440618693)
            ·
              refine ⟨14399751449846296582616005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 76798674399180248440618693 14399751449846296582616005)
              ·
                refine ⟨2699953396846180609240501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14399751449846296582616005 2699953396846180609240501)
                ·
                  refine ⟨253120630954329432116297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2699953396846180609240501 253120630954329432116297)
                  ·
                    rfl

theorem cell21_1109139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 4, 4, 5].length) (baseStart_1109139 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1109139 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1109139 prefixEnd_1109139 := by exact prefixLift 1109139
  have htrace : WordTrace (prefixWord ++ tailWord_1109139) baseStart_1109139 baseEnd_1109139 := by
    simpa [prefixWord, tailWord_1109139, baseEnd_1109139] using wordTrace_append hprefix tailTrace_1109139
  have hstable : (prefixWord ++ tailWord_1109139).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1109139).length < 2 ^ (prefixWord ++ tailWord_1109139).sum := by decide
  have hdescent : baseEnd_1109139 < baseStart_1109139 := by decide
  rcases family_descends (prefixWord ++ tailWord_1109139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1109221 : List Nat := [1, 3, 1, 4, 4, 1, 1, 2, 4]
def baseStart_1109221 : Nat := 118140960795 + 1109221 * 2 ^ 59
def prefixEnd_1109221 : Nat := 4983230072969 + 3 ^ 40 * 1109221 * 2
def baseEnd_1109221 : Nat := 253139344471515511749463

theorem tailTrace_1109221 : CollatzResearch.WordTrace tailWord_1109221 prefixEnd_1109221 253139344471515511749463 := by
  unfold tailWord_1109221
  simp only [CollatzResearch.WordTrace]
  refine ⟨40456613514489231709831517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26971075676326154473221011 40456613514489231709831517)
  ·
    refine ⟨15171230067933461891186819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40456613514489231709831517 15171230067933461891186819)
    ·
      refine ⟨22756845101900192836780229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15171230067933461891186819 22756845101900192836780229)
      ·
        refine ⟨4266908456606286156896293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 22756845101900192836780229 4266908456606286156896293)
        ·
          refine ⟨800045335613678654418055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4266908456606286156896293 800045335613678654418055)
          ·
            refine ⟨1200068003420517981627083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 800045335613678654418055 1200068003420517981627083)
            ·
              refine ⟨1800102005130776972440625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1200068003420517981627083 1800102005130776972440625)
              ·
                refine ⟨1350076503848082729330469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1800102005130776972440625 1350076503848082729330469)
                ·
                  refine ⟨253139344471515511749463, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1350076503848082729330469 253139344471515511749463)
                  ·
                    rfl

theorem cell21_1109221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 4, 1, 1, 2, 4].length) (baseStart_1109221 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1109221 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1109221 prefixEnd_1109221 := by exact prefixLift 1109221
  have htrace : WordTrace (prefixWord ++ tailWord_1109221) baseStart_1109221 baseEnd_1109221 := by
    simpa [prefixWord, tailWord_1109221, baseEnd_1109221] using wordTrace_append hprefix tailTrace_1109221
  have hstable : (prefixWord ++ tailWord_1109221).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1109221).length < 2 ^ (prefixWord ++ tailWord_1109221).sum := by decide
  have hdescent : baseEnd_1109221 < baseStart_1109221 := by decide
  rcases family_descends (prefixWord ++ tailWord_1109221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1109277 : List Nat := [1, 4, 2, 3, 1, 1, 9]
def baseStart_1109277 : Nat := 118140960795 + 1109277 * 2 ^ 59
def prefixEnd_1109277 : Nat := 4983230072969 + 3 ^ 40 * 1109277 * 2
def baseEnd_1109277 : Nat := 28128013826052428757335

theorem tailTrace_1109277 : CollatzResearch.WordTrace tailWord_1109277 prefixEnd_1109277 28128013826052428757335 := by
  unfold tailWord_1109277
  simp only [CollatzResearch.WordTrace]
  refine ⟨40458656002286353273870085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26972437334857568849246723 40458656002286353273870085)
  ·
    refine ⟨7585998000428691238850641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 40458656002286353273870085 7585998000428691238850641)
    ·
      refine ⟨5689498500321518429137981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7585998000428691238850641 5689498500321518429137981)
      ·
        refine ⟨2133561937620569410926743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5689498500321518429137981 2133561937620569410926743)
        ·
          refine ⟨3200342906430854116390115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2133561937620569410926743 3200342906430854116390115)
          ·
            refine ⟨4800514359646281174585173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3200342906430854116390115 4800514359646281174585173)
            ·
              refine ⟨28128013826052428757335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 4800514359646281174585173 28128013826052428757335)
              ·
                rfl

theorem cell21_1109277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 9].length) (baseStart_1109277 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1109277 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1109277 prefixEnd_1109277 := by exact prefixLift 1109277
  have htrace : WordTrace (prefixWord ++ tailWord_1109277) baseStart_1109277 baseEnd_1109277 := by
    simpa [prefixWord, tailWord_1109277, baseEnd_1109277] using wordTrace_append hprefix tailTrace_1109277
  have hstable : (prefixWord ++ tailWord_1109277).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1109277).length < 2 ^ (prefixWord ++ tailWord_1109277).sum := by decide
  have hdescent : baseEnd_1109277 < baseStart_1109277 := by decide
  rcases family_descends (prefixWord ++ tailWord_1109277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1109334 : List Nat := [5, 2, 3, 1, 1, 2, 2, 2, 3]
def baseStart_1109334 : Nat := 118140960795 + 1109334 * 2 ^ 59
def prefixEnd_1109334 : Nat := 4983230072969 + 3 ^ 40 * 1109334 * 2
def baseEnd_1109334 : Nat := 253165132611052426365899

theorem tailTrace_1109334 : CollatzResearch.WordTrace tailWord_1109334 prefixEnd_1109334 253165132611052426365899 := by
  unfold tailWord_1109334
  simp only [CollatzResearch.WordTrace]
  refine ⟨2528795935192490750543441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 26973823308719901339130037 2528795935192490750543441)
  ·
    refine ⟨1896596951394368062907581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2528795935192490750543441 1896596951394368062907581)
    ·
      refine ⟨711223856772888023590343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1896596951394368062907581 711223856772888023590343)
      ·
        refine ⟨1066835785159332035385515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 711223856772888023590343 1066835785159332035385515)
        ·
          refine ⟨1600253677738998053078273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1066835785159332035385515 1600253677738998053078273)
          ·
            refine ⟨1200190258304248539808705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1600253677738998053078273 1200190258304248539808705)
            ·
              refine ⟨900142693728186404856529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1200190258304248539808705 900142693728186404856529)
              ·
                refine ⟨675107020296139803642397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 900142693728186404856529 675107020296139803642397)
                ·
                  refine ⟨253165132611052426365899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 675107020296139803642397 253165132611052426365899)
                  ·
                    rfl

theorem cell21_1109334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 2, 2, 2, 3].length) (baseStart_1109334 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1109334 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1109334 prefixEnd_1109334 := by exact prefixLift 1109334
  have htrace : WordTrace (prefixWord ++ tailWord_1109334) baseStart_1109334 baseEnd_1109334 := by
    simpa [prefixWord, tailWord_1109334, baseEnd_1109334] using wordTrace_append hprefix tailTrace_1109334
  have hstable : (prefixWord ++ tailWord_1109334).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1109334).length < 2 ^ (prefixWord ++ tailWord_1109334).sum := by decide
  have hdescent : baseEnd_1109334 < baseStart_1109334 := by decide
  rcases family_descends (prefixWord ++ tailWord_1109334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1109367 : List Nat := [1, 1, 3, 1, 1, 2, 5, 2, 5]
def baseStart_1109367 : Nat := 118140960795 + 1109367 * 2 ^ 59
def prefixEnd_1109367 : Nat := 4983230072969 + 3 ^ 40 * 1109367 * 2
def baseEnd_1109367 : Nat := 253172663660651702315831

theorem tailTrace_1109367 : CollatzResearch.WordTrace tailWord_1109367 prefixEnd_1109367 253172663660651702315831 := by
  unfold tailWord_1109367
  simp only [CollatzResearch.WordTrace]
  refine ⟨40461938571960298644646355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26974625714640199096430903 40461938571960298644646355)
  ·
    refine ⟨60692907857940447966969533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40461938571960298644646355 60692907857940447966969533)
    ·
      refine ⟨22759840446727667987613575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 60692907857940447966969533 22759840446727667987613575)
      ·
        refine ⟨34139760670091501981420363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22759840446727667987613575 34139760670091501981420363)
        ·
          refine ⟨51209641005137252972130545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34139760670091501981420363 51209641005137252972130545)
          ·
            refine ⟨38407230753852939729097909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51209641005137252972130545 38407230753852939729097909)
            ·
              refine ⟨3600677883173713099602929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 38407230753852939729097909 3600677883173713099602929)
              ·
                refine ⟨2700508412380284824702197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3600677883173713099602929 2700508412380284824702197)
                ·
                  refine ⟨253172663660651702315831, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2700508412380284824702197 253172663660651702315831)
                  ·
                    rfl

theorem cell21_1109367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 5, 2, 5].length) (baseStart_1109367 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1109367 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1109367 prefixEnd_1109367 := by exact prefixLift 1109367
  have htrace : WordTrace (prefixWord ++ tailWord_1109367) baseStart_1109367 baseEnd_1109367 := by
    simpa [prefixWord, tailWord_1109367, baseEnd_1109367] using wordTrace_append hprefix tailTrace_1109367
  have hstable : (prefixWord ++ tailWord_1109367).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1109367).length < 2 ^ (prefixWord ++ tailWord_1109367).sum := by decide
  have hdescent : baseEnd_1109367 < baseStart_1109367 := by decide
  rcases family_descends (prefixWord ++ tailWord_1109367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1109412 : List Nat := [2, 3, 1, 2, 1, 1, 1, 10]
def baseStart_1109412 : Nat := 118140960795 + 1109412 * 2 ^ 59
def prefixEnd_1109412 : Nat := 4983230072969 + 3 ^ 40 * 1109412 * 2
def baseEnd_1109412 : Nat := 84394311091247208021913

theorem tailTrace_1109412 : CollatzResearch.WordTrace tailWord_1109412 prefixEnd_1109412 84394311091247208021913 := by
  unfold tailWord_1109412
  simp only [CollatzResearch.WordTrace]
  refine ⟨20231789928398635665017245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26975719904531514220022993 20231789928398635665017245)
  ·
    refine ⟨7586921223149488374381467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20231789928398635665017245 7586921223149488374381467)
    ·
      refine ⟨11380381834724232561572201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7586921223149488374381467 11380381834724232561572201)
      ·
        refine ⟨8535286376043174421179151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11380381834724232561572201 8535286376043174421179151)
        ·
          refine ⟨12802929564064761631768727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8535286376043174421179151 12802929564064761631768727)
          ·
            refine ⟨19204394346097142447653091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12802929564064761631768727 19204394346097142447653091)
            ·
              refine ⟨28806591519145713671479637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19204394346097142447653091 28806591519145713671479637)
              ·
                refine ⟨84394311091247208021913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 28806591519145713671479637 84394311091247208021913)
                ·
                  rfl

theorem cell21_1109412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 10].length) (baseStart_1109412 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1109412 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1109412 prefixEnd_1109412 := by exact prefixLift 1109412
  have htrace : WordTrace (prefixWord ++ tailWord_1109412) baseStart_1109412 baseEnd_1109412 := by
    simpa [prefixWord, tailWord_1109412, baseEnd_1109412] using wordTrace_append hprefix tailTrace_1109412
  have hstable : (prefixWord ++ tailWord_1109412).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1109412).length < 2 ^ (prefixWord ++ tailWord_1109412).sum := by decide
  have hdescent : baseEnd_1109412 < baseStart_1109412 := by decide
  rcases family_descends (prefixWord ++ tailWord_1109412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1109429 : List Nat := [1, 3, 3, 2, 2, 2, 1, 7]
def baseStart_1109429 : Nat := 118140960795 + 1109429 * 2 ^ 59
def prefixEnd_1109429 : Nat := 4983230072969 + 3 ^ 40 * 1109429 * 2
def baseEnd_1109429 : Nat := 84395604301784457427457

theorem tailTrace_1109429 : CollatzResearch.WordTrace tailWord_1109429 prefixEnd_1109429 84395604301784457427457 := by
  unfold tailWord_1109429
  simp only [CollatzResearch.WordTrace]
  refine ⟨40464199897735683233403341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26976133265157122155602227 40464199897735683233403341)
  ·
    refine ⟨15174074961650881212526253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40464199897735683233403341 15174074961650881212526253)
    ·
      refine ⟨5690278110619080454697345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15174074961650881212526253 5690278110619080454697345)
      ·
        refine ⟨4267708582964310341023009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5690278110619080454697345 4267708582964310341023009)
        ·
          refine ⟨3200781437223232755767257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4267708582964310341023009 3200781437223232755767257)
          ·
            refine ⟨2400586077917424566825443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3200781437223232755767257 2400586077917424566825443)
            ·
              refine ⟨3600879116876136850238165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2400586077917424566825443 3600879116876136850238165)
              ·
                refine ⟨84395604301784457427457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3600879116876136850238165 84395604301784457427457)
                ·
                  rfl

theorem cell21_1109429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 2, 1, 7].length) (baseStart_1109429 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1109429 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1109429 prefixEnd_1109429 := by exact prefixLift 1109429
  have htrace : WordTrace (prefixWord ++ tailWord_1109429) baseStart_1109429 baseEnd_1109429 := by
    simpa [prefixWord, tailWord_1109429, baseEnd_1109429] using wordTrace_append hprefix tailTrace_1109429
  have hstable : (prefixWord ++ tailWord_1109429).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1109429).length < 2 ^ (prefixWord ++ tailWord_1109429).sum := by decide
  have hdescent : baseEnd_1109429 < baseStart_1109429 := by decide
  rcases family_descends (prefixWord ++ tailWord_1109429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1109488 : List Nat := [2, 1, 1, 1, 3, 4, 2, 7]
def baseStart_1109488 : Nat := 118140960795 + 1109488 * 2 ^ 59
def prefixEnd_1109488 : Nat := 4983230072969 + 3 ^ 40 * 1109488 * 2
def baseEnd_1109488 : Nat := 84400092503060793599639

theorem tailTrace_1109488 : CollatzResearch.WordTrace tailWord_1109488 prefixEnd_1109488 84400092503060793599639 := by
  unfold tailWord_1109488
  simp only [CollatzResearch.WordTrace]
  refine ⟨20233175902260968154900559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26977567869681290873200745 20233175902260968154900559)
  ·
    refine ⟨30349763853391452232350839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20233175902260968154900559 30349763853391452232350839)
    ·
      refine ⟨45524645780087178348526259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30349763853391452232350839 45524645780087178348526259)
      ·
        refine ⟨68286968670130767522789389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45524645780087178348526259 68286968670130767522789389)
        ·
          refine ⟨25607613251299037821046021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 68286968670130767522789389 25607613251299037821046021)
          ·
            refine ⟨4801427484618569591446129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 25607613251299037821046021 4801427484618569591446129)
            ·
              refine ⟨3601070613463927193584597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4801427484618569591446129 3601070613463927193584597)
              ·
                refine ⟨84400092503060793599639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3601070613463927193584597 84400092503060793599639)
                ·
                  rfl

theorem cell21_1109488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 2, 7].length) (baseStart_1109488 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1109488 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1109488 prefixEnd_1109488 := by exact prefixLift 1109488
  have htrace : WordTrace (prefixWord ++ tailWord_1109488) baseStart_1109488 baseEnd_1109488 := by
    simpa [prefixWord, tailWord_1109488, baseEnd_1109488] using wordTrace_append hprefix tailTrace_1109488
  have hstable : (prefixWord ++ tailWord_1109488).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1109488).length < 2 ^ (prefixWord ++ tailWord_1109488).sum := by decide
  have hdescent : baseEnd_1109488 < baseStart_1109488 := by decide
  rcases family_descends (prefixWord ++ tailWord_1109488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1109505 : List Nat := [1, 2, 4, 1, 5, 8]
def baseStart_1109505 : Nat := 118140960795 + 1109505 * 2 ^ 59
def prefixEnd_1109505 : Nat := 4983230072969 + 3 ^ 40 * 1109505 * 2
def baseEnd_1109505 : Nat := 9377931745955338111687

theorem tailTrace_1109505 : CollatzResearch.WordTrace tailWord_1109505 prefixEnd_1109505 9377931745955338111687 := by
  unfold tailWord_1109505
  simp only [CollatzResearch.WordTrace]
  refine ⟨40466971845460348213169969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26977981230306898808779979 40466971845460348213169969)
  ·
    refine ⟨30350228884095261159877477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40466971845460348213169969 30350228884095261159877477)
    ·
      refine ⟨5690667915767861467477027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 30350228884095261159877477 5690667915767861467477027)
      ·
        refine ⟨8536001873651792201215541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5690667915767861467477027 8536001873651792201215541)
        ·
          refine ⟨800250175654855518863957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 8536001873651792201215541 800250175654855518863957)
          ·
            refine ⟨9377931745955338111687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 800250175654855518863957 9377931745955338111687)
            ·
              rfl

theorem cell21_1109505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 5, 8].length) (baseStart_1109505 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1109505 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1109505 prefixEnd_1109505 := by exact prefixLift 1109505
  have htrace : WordTrace (prefixWord ++ tailWord_1109505) baseStart_1109505 baseEnd_1109505 := by
    simpa [prefixWord, tailWord_1109505, baseEnd_1109505] using wordTrace_append hprefix tailTrace_1109505
  have hstable : (prefixWord ++ tailWord_1109505).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1109505).length < 2 ^ (prefixWord ++ tailWord_1109505).sum := by decide
  have hdescent : baseEnd_1109505 < baseStart_1109505 := by decide
  rcases family_descends (prefixWord ++ tailWord_1109505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1109508 : List Nat := [2, 3, 2, 3, 2, 1, 2, 2, 4]
def baseStart_1109508 : Nat := 118140960795 + 1109508 * 2 ^ 59
def prefixEnd_1109508 : Nat := 4983230072969 + 3 ^ 40 * 1109508 * 2
def baseEnd_1109508 : Nat := 253204841781666790465543

theorem tailTrace_1109508 : CollatzResearch.WordTrace tailWord_1109508 prefixEnd_1109508 253204841781666790465543 := by
  unfold tailWord_1109508
  simp only [CollatzResearch.WordTrace]
  refine ⟨20233540632224739862764589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26978054176299653150352785 20233540632224739862764589)
  ·
    refine ⟨7587577737084277448536721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20233540632224739862764589 7587577737084277448536721)
    ·
      refine ⟨5690683302813208086402541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7587577737084277448536721 5690683302813208086402541)
      ·
        refine ⟨2134006238554953032400953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5690683302813208086402541 2134006238554953032400953)
        ·
          refine ⟨1600504678916214774300715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2134006238554953032400953 1600504678916214774300715)
          ·
            refine ⟨2400757018374322161451073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1600504678916214774300715 2400757018374322161451073)
            ·
              refine ⟨1800567763780741621088305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2400757018374322161451073 1800567763780741621088305)
              ·
                refine ⟨1350425822835556215816229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1800567763780741621088305 1350425822835556215816229)
                ·
                  refine ⟨253204841781666790465543, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1350425822835556215816229 253204841781666790465543)
                  ·
                    rfl

theorem cell21_1109508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 1, 2, 2, 4].length) (baseStart_1109508 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1109508 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1109508 prefixEnd_1109508 := by exact prefixLift 1109508
  have htrace : WordTrace (prefixWord ++ tailWord_1109508) baseStart_1109508 baseEnd_1109508 := by
    simpa [prefixWord, tailWord_1109508, baseEnd_1109508] using wordTrace_append hprefix tailTrace_1109508
  have hstable : (prefixWord ++ tailWord_1109508).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1109508).length < 2 ^ (prefixWord ++ tailWord_1109508).sum := by decide
  have hdescent : baseEnd_1109508 < baseStart_1109508 := by decide
  rcases family_descends (prefixWord ++ tailWord_1109508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1109536 : List Nat := [2, 1, 1, 6, 1, 2, 1, 2, 5]
def baseStart_1109536 : Nat := 118140960795 + 1109536 * 2 ^ 59
def prefixEnd_1109536 : Nat := 4983230072969 + 3 ^ 40 * 1109536 * 2
def baseEnd_1109536 : Nat := 253211231763144963998819

theorem tailTrace_1109536 : CollatzResearch.WordTrace tailWord_1109536 prefixEnd_1109536 253211231763144963998819 := by
  unfold tailWord_1109536
  simp only [CollatzResearch.WordTrace]
  refine ⟨20234051254174020253774231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26978735005565360338365641 20234051254174020253774231)
  ·
    refine ⟨30351076881261030380661347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20234051254174020253774231 30351076881261030380661347)
    ·
      refine ⟨45526615321891545570992021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30351076881261030380661347 45526615321891545570992021)
      ·
        refine ⟨2134060093213666198640251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 45526615321891545570992021 2134060093213666198640251)
        ·
          refine ⟨3201090139820499297960377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2134060093213666198640251 3201090139820499297960377)
          ·
            refine ⟨2400817604865374473470283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3201090139820499297960377 2400817604865374473470283)
            ·
              refine ⟨3601226407298061710205425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2400817604865374473470283 3601226407298061710205425)
              ·
                refine ⟨2700919805473546282654069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3601226407298061710205425 2700919805473546282654069)
                ·
                  refine ⟨253211231763144963998819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2700919805473546282654069 253211231763144963998819)
                  ·
                    rfl

theorem cell21_1109536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 2, 1, 2, 5].length) (baseStart_1109536 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1109536 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1109536 prefixEnd_1109536 := by exact prefixLift 1109536
  have htrace : WordTrace (prefixWord ++ tailWord_1109536) baseStart_1109536 baseEnd_1109536 := by
    simpa [prefixWord, tailWord_1109536, baseEnd_1109536] using wordTrace_append hprefix tailTrace_1109536
  have hstable : (prefixWord ++ tailWord_1109536).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1109536).length < 2 ^ (prefixWord ++ tailWord_1109536).sum := by decide
  have hdescent : baseEnd_1109536 < baseStart_1109536 := by decide
  rcases family_descends (prefixWord ++ tailWord_1109536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1109567 : List Nat := [1, 1, 2, 2, 3, 5, 1, 2, 4]
def baseStart_1109567 : Nat := 118140960795 + 1109567 * 2 ^ 59
def prefixEnd_1109567 : Nat := 4983230072969 + 3 ^ 40 * 1109567 * 2
def baseEnd_1109567 : Nat := 253218306385495798982089

theorem tailTrace_1109567 : CollatzResearch.WordTrace tailWord_1109567 prefixEnd_1109567 253218306385495798982089 := by
  unfold tailWord_1109567
  simp only [CollatzResearch.WordTrace]
  refine ⟨40469233171235732801926955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26979488780823821867951303 40469233171235732801926955)
  ·
    refine ⟨60703849756853599202890433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40469233171235732801926955 60703849756853599202890433)
    ·
      refine ⟨45527887317640199402167825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60703849756853599202890433 45527887317640199402167825)
      ·
        refine ⟨34145915488230149551625869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45527887317640199402167825 34145915488230149551625869)
        ·
          refine ⟨12804718308086306081859701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34145915488230149551625869 12804718308086306081859701)
          ·
            refine ⟨1200442341383091195174347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 12804718308086306081859701 1200442341383091195174347)
            ·
              refine ⟨1800663512074636792761521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1200442341383091195174347 1800663512074636792761521)
              ·
                refine ⟨1350497634055977594571141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1800663512074636792761521 1350497634055977594571141)
                ·
                  refine ⟨253218306385495798982089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1350497634055977594571141 253218306385495798982089)
                  ·
                    rfl

theorem cell21_1109567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 5, 1, 2, 4].length) (baseStart_1109567 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1109567 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1109567 prefixEnd_1109567 := by exact prefixLift 1109567
  have htrace : WordTrace (prefixWord ++ tailWord_1109567) baseStart_1109567 baseEnd_1109567 := by
    simpa [prefixWord, tailWord_1109567, baseEnd_1109567] using wordTrace_append hprefix tailTrace_1109567
  have hstable : (prefixWord ++ tailWord_1109567).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1109567).length < 2 ^ (prefixWord ++ tailWord_1109567).sum := by decide
  have hdescent : baseEnd_1109567 < baseStart_1109567 := by decide
  rcases family_descends (prefixWord ++ tailWord_1109567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1109609 : List Nat := [1, 2, 1, 1, 1, 4, 3, 2, 6]
def baseStart_1109609 : Nat := 118140960795 + 1109609 * 2 ^ 59
def prefixEnd_1109609 : Nat := 4983230072969 + 3 ^ 40 * 1109609 * 2
def baseEnd_1109609 : Nat := 253227891357713059282003

theorem tailTrace_1109609 : CollatzResearch.WordTrace tailWord_1109609 prefixEnd_1109609 253227891357713059282003 := by
  unfold tailWord_1109609
  simp only [CollatzResearch.WordTrace]
  refine ⟨40470765037083573974955881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26980510024722382649970587 40470765037083573974955881)
  ·
    refine ⟨30353073777812680481216911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40470765037083573974955881 30353073777812680481216911)
    ·
      refine ⟨45529610666719020721825367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30353073777812680481216911 45529610666719020721825367)
      ·
        refine ⟨68294416000078531082738051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45529610666719020721825367 68294416000078531082738051)
        ·
          refine ⟨102441624000117796624107077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68294416000078531082738051 102441624000117796624107077)
          ·
            refine ⟨19207804500022086867020077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 102441624000117796624107077 19207804500022086867020077)
            ·
              refine ⟨7202926687508282575132529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19207804500022086867020077 7202926687508282575132529)
              ·
                refine ⟨5402195015631211931349397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7202926687508282575132529 5402195015631211931349397)
                ·
                  refine ⟨253227891357713059282003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5402195015631211931349397 253227891357713059282003)
                  ·
                    rfl

theorem cell21_1109609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 3, 2, 6].length) (baseStart_1109609 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1109609 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1109609 prefixEnd_1109609 := by exact prefixLift 1109609
  have htrace : WordTrace (prefixWord ++ tailWord_1109609) baseStart_1109609 baseEnd_1109609 := by
    simpa [prefixWord, tailWord_1109609, baseEnd_1109609] using wordTrace_append hprefix tailTrace_1109609
  have hstable : (prefixWord ++ tailWord_1109609).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1109609).length < 2 ^ (prefixWord ++ tailWord_1109609).sum := by decide
  have hdescent : baseEnd_1109609 < baseStart_1109609 := by decide
  rcases family_descends (prefixWord ++ tailWord_1109609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1109767 : List Nat := [1, 1, 4, 4, 3, 1, 2, 5]
def baseStart_1109767 : Nat := 118140960795 + 1109767 * 2 ^ 59
def prefixEnd_1109767 : Nat := 4983230072969 + 3 ^ 40 * 1109767 * 2
def baseEnd_1109767 : Nat := 84421316370113298549449

theorem tailTrace_1109767 : CollatzResearch.WordTrace tailWord_1109767 prefixEnd_1109767 84421316370113298549449 := by
  unfold tailWord_1109767
  simp only [CollatzResearch.WordTrace]
  refine ⟨40476527770511166959207555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26984351847007444639471703 40476527770511166959207555)
  ·
    refine ⟨60714791655766750438811333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40476527770511166959207555 60714791655766750438811333)
    ·
      refine ⟨11384023435456265707277125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 60714791655766750438811333 11384023435456265707277125)
      ·
        refine ⟨2134504394148049820114461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11384023435456265707277125 2134504394148049820114461)
        ·
          refine ⟨800439147805518682542923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2134504394148049820114461 800439147805518682542923)
          ·
            refine ⟨1200658721708278023814385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 800439147805518682542923 1200658721708278023814385)
            ·
              refine ⟨900494041281208517860789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1200658721708278023814385 900494041281208517860789)
              ·
                refine ⟨84421316370113298549449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 900494041281208517860789 84421316370113298549449)
                ·
                  rfl

theorem cell21_1109767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 3, 1, 2, 5].length) (baseStart_1109767 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1109767 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1109767 prefixEnd_1109767 := by exact prefixLift 1109767
  have htrace : WordTrace (prefixWord ++ tailWord_1109767) baseStart_1109767 baseEnd_1109767 := by
    simpa [prefixWord, tailWord_1109767, baseEnd_1109767] using wordTrace_append hprefix tailTrace_1109767
  have hstable : (prefixWord ++ tailWord_1109767).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1109767).length < 2 ^ (prefixWord ++ tailWord_1109767).sum := by decide
  have hdescent : baseEnd_1109767 < baseStart_1109767 := by decide
  rcases family_descends (prefixWord ++ tailWord_1109767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1109773 : List Nat := [1, 7, 2, 1, 1, 2, 1, 3, 3]
def baseStart_1109773 : Nat := 118140960795 + 1109773 * 2 ^ 59
def prefixEnd_1109773 : Nat := 4983230072969 + 3 ^ 40 * 1109773 * 2
def baseEnd_1109773 : Nat := 253265318392085218548335

theorem tailTrace_1109773 : CollatzResearch.WordTrace tailWord_1109773 prefixEnd_1109773 253265318392085218548335 := by
  unfold tailWord_1109773
  simp only [CollatzResearch.WordTrace]
  refine ⟨40476746608489429983925973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26984497738992953322617315 40476746608489429983925973)
  ·
    refine ⟨948673748636471015248265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 40476746608489429983925973 948673748636471015248265)
    ·
      refine ⟨711505311477353261436199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 948673748636471015248265 711505311477353261436199)
      ·
        refine ⟨1067257967216029892154299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 711505311477353261436199 1067257967216029892154299)
        ·
          refine ⟨1600886950824044838231449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1067257967216029892154299 1600886950824044838231449)
          ·
            refine ⟨1200665213118033628673587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1600886950824044838231449 1200665213118033628673587)
            ·
              refine ⟨1800997819677050443010381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1200665213118033628673587 1800997819677050443010381)
              ·
                refine ⟨675374182378893916128893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1800997819677050443010381 675374182378893916128893)
                ·
                  refine ⟨253265318392085218548335, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 675374182378893916128893 253265318392085218548335)
                  ·
                    rfl

theorem cell21_1109773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 2, 1, 3, 3].length) (baseStart_1109773 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1109773 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1109773 prefixEnd_1109773 := by exact prefixLift 1109773
  have htrace : WordTrace (prefixWord ++ tailWord_1109773) baseStart_1109773 baseEnd_1109773 := by
    simpa [prefixWord, tailWord_1109773, baseEnd_1109773] using wordTrace_append hprefix tailTrace_1109773
  have hstable : (prefixWord ++ tailWord_1109773).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1109773).length < 2 ^ (prefixWord ++ tailWord_1109773).sum := by decide
  have hdescent : baseEnd_1109773 < baseStart_1109773 := by decide
  rcases family_descends (prefixWord ++ tailWord_1109773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1109781 : List Nat := [1, 3, 2, 1, 2, 5, 1, 3, 3]
def baseStart_1109781 : Nat := 118140960795 + 1109781 * 2 ^ 59
def prefixEnd_1109781 : Nat := 4983230072969 + 3 ^ 40 * 1109781 * 2
def baseEnd_1109781 : Nat := 253267144101078982414985

theorem tailTrace_1109781 : CollatzResearch.WordTrace tailWord_1109781 prefixEnd_1109781 253267144101078982414985 := by
  unfold tailWord_1109781
  simp only [CollatzResearch.WordTrace]
  refine ⟨40477038392460447350217197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26984692261640298233478131 40477038392460447350217197)
  ·
    refine ⟨15178889397172667756331449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40477038392460447350217197 15178889397172667756331449)
    ·
      refine ⟨11384167047879500817248587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15178889397172667756331449 11384167047879500817248587)
      ·
        refine ⟨17076250571819251225872881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11384167047879500817248587 17076250571819251225872881)
        ·
          refine ⟨12807187928864438419404661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17076250571819251225872881 12807187928864438419404661)
          ·
            refine ⟨1200673868331041101819187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 12807187928864438419404661 1200673868331041101819187)
            ·
              refine ⟨1801010802496561652728781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1200673868331041101819187 1801010802496561652728781)
              ·
                refine ⟨675379050936210619773293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1801010802496561652728781 675379050936210619773293)
                ·
                  refine ⟨253267144101078982414985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 675379050936210619773293 253267144101078982414985)
                  ·
                    rfl

theorem cell21_1109781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 5, 1, 3, 3].length) (baseStart_1109781 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1109781 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1109781 prefixEnd_1109781 := by exact prefixLift 1109781
  have htrace : WordTrace (prefixWord ++ tailWord_1109781) baseStart_1109781 baseEnd_1109781 := by
    simpa [prefixWord, tailWord_1109781, baseEnd_1109781] using wordTrace_append hprefix tailTrace_1109781
  have hstable : (prefixWord ++ tailWord_1109781).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1109781).length < 2 ^ (prefixWord ++ tailWord_1109781).sum := by decide
  have hdescent : baseEnd_1109781 < baseStart_1109781 := by decide
  rcases family_descends (prefixWord ++ tailWord_1109781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1109812 : List Nat := [2, 5, 1, 1, 2, 1, 4, 1, 4]
def baseStart_1109812 : Nat := 118140960795 + 1109812 * 2 ^ 59
def prefixEnd_1109812 : Nat := 4983230072969 + 3 ^ 40 * 1109812 * 2
def baseEnd_1109812 : Nat := 253274218723429817398255

theorem tailTrace_1109812 : CollatzResearch.WordTrace tailWord_1109812 prefixEnd_1109812 253274218723429817398255 := by
  unfold tailWord_1109812
  simp only [CollatzResearch.WordTrace]
  refine ⟨20239084527674069822297845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26985446036898759763063793 20239084527674069822297845)
  ·
    refine ⟨1897414174469444045840423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 20239084527674069822297845 1897414174469444045840423)
    ·
      refine ⟨2846121261704166068760635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1897414174469444045840423 2846121261704166068760635)
      ·
        refine ⟨4269181892556249103140953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2846121261704166068760635 4269181892556249103140953)
        ·
          refine ⟨3201886419417186827355715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4269181892556249103140953 3201886419417186827355715)
          ·
            refine ⟨4802829629125780241033573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3201886419417186827355715 4802829629125780241033573)
            ·
              refine ⟨900530555461083795193795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4802829629125780241033573 900530555461083795193795)
              ·
                refine ⟨1350795833191625692790693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 900530555461083795193795 1350795833191625692790693)
                ·
                  refine ⟨253274218723429817398255, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1350795833191625692790693 253274218723429817398255)
                  ·
                    rfl

theorem cell21_1109812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 4, 1, 4].length) (baseStart_1109812 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1109812 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1109812 prefixEnd_1109812 := by exact prefixLift 1109812
  have htrace : WordTrace (prefixWord ++ tailWord_1109812) baseStart_1109812 baseEnd_1109812 := by
    simpa [prefixWord, tailWord_1109812, baseEnd_1109812] using wordTrace_append hprefix tailTrace_1109812
  have hstable : (prefixWord ++ tailWord_1109812).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1109812).length < 2 ^ (prefixWord ++ tailWord_1109812).sum := by decide
  have hdescent : baseEnd_1109812 < baseStart_1109812 := by decide
  rcases family_descends (prefixWord ++ tailWord_1109812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1109868 : List Nat := [2, 2, 1, 1, 4, 2, 3, 6]
def baseStart_1109868 : Nat := 118140960795 + 1109868 * 2 ^ 59
def prefixEnd_1109868 : Nat := 4983230072969 + 3 ^ 40 * 1109868 * 2
def baseEnd_1109868 : Nat := 84428999562128721488269

theorem tailTrace_1109868 : CollatzResearch.WordTrace tailWord_1109868 prefixEnd_1109868 84428999562128721488269 := by
  unfold tailWord_1109868
  simp only [CollatzResearch.WordTrace]
  refine ⟨20240105771572630604317129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26986807695430174139089505 20240105771572630604317129)
  ·
    refine ⟨15180079328679472953237847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20240105771572630604317129 15180079328679472953237847)
    ·
      refine ⟨22770118993019209429856771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15180079328679472953237847 22770118993019209429856771)
      ·
        refine ⟨34155178489528814144785157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22770118993019209429856771 34155178489528814144785157)
        ·
          refine ⟨6404095966786652652147217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 34155178489528814144785157 6404095966786652652147217)
          ·
            refine ⟨4803071975089989489110413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6404095966786652652147217 4803071975089989489110413)
            ·
              refine ⟨1801151990658746058416405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4803071975089989489110413 1801151990658746058416405)
              ·
                refine ⟨84428999562128721488269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1801151990658746058416405 84428999562128721488269)
                ·
                  rfl

theorem cell21_1109868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 3, 6].length) (baseStart_1109868 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1109868 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1109868 prefixEnd_1109868 := by exact prefixLift 1109868
  have htrace : WordTrace (prefixWord ++ tailWord_1109868) baseStart_1109868 baseEnd_1109868 := by
    simpa [prefixWord, tailWord_1109868, baseEnd_1109868] using wordTrace_append hprefix tailTrace_1109868
  have hstable : (prefixWord ++ tailWord_1109868).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1109868).length < 2 ^ (prefixWord ++ tailWord_1109868).sum := by decide
  have hdescent : baseEnd_1109868 < baseStart_1109868 := by decide
  rcases family_descends (prefixWord ++ tailWord_1109868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1109882 : List Nat := [3, 1, 1, 1, 1, 1, 5, 1, 7]
def baseStart_1109882 : Nat := 118140960795 + 1109882 * 2 ^ 59
def prefixEnd_1109882 : Nat := 4983230072969 + 3 ^ 40 * 1109882 * 2
def baseEnd_1109882 : Nat := 253290193677125251231445

theorem tailTrace_1109882 : CollatzResearch.WordTrace tailWord_1109882 prefixEnd_1109882 253290193677125251231445 := by
  unfold tailWord_1109882
  simp only [CollatzResearch.WordTrace]
  refine ⟨10120180541273635399910975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26987148110063027733095933 10120180541273635399910975)
  ·
    refine ⟨15180270811910453099866463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10120180541273635399910975 15180270811910453099866463)
    ·
      refine ⟨22770406217865679649799695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15180270811910453099866463 22770406217865679649799695)
      ·
        refine ⟨34155609326798519474699543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22770406217865679649799695 34155609326798519474699543)
        ·
          refine ⟨51233413990197779212049315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34155609326798519474699543 51233413990197779212049315)
          ·
            refine ⟨76850120985296668818073973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51233413990197779212049315 76850120985296668818073973)
            ·
              refine ⟨7204698842371562701694435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 76850120985296668818073973 7204698842371562701694435)
              ·
                refine ⟨10807048263557344052541653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7204698842371562701694435 10807048263557344052541653)
                ·
                  refine ⟨253290193677125251231445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10807048263557344052541653 253290193677125251231445)
                  ·
                    rfl

theorem cell21_1109882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 5, 1, 7].length) (baseStart_1109882 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1109882 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1109882 prefixEnd_1109882 := by exact prefixLift 1109882
  have htrace : WordTrace (prefixWord ++ tailWord_1109882) baseStart_1109882 baseEnd_1109882 := by
    simpa [prefixWord, tailWord_1109882, baseEnd_1109882] using wordTrace_append hprefix tailTrace_1109882
  have hstable : (prefixWord ++ tailWord_1109882).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1109882).length < 2 ^ (prefixWord ++ tailWord_1109882).sum := by decide
  have hdescent : baseEnd_1109882 < baseStart_1109882 := by decide
  rcases family_descends (prefixWord ++ tailWord_1109882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1109916 : List Nat := [2, 2, 3, 3, 1, 2, 2, 1, 5]
def baseStart_1109916 : Nat := 118140960795 + 1109916 * 2 ^ 59
def prefixEnd_1109916 : Nat := 4983230072969 + 3 ^ 40 * 1109916 * 2
def baseEnd_1109916 : Nat := 253297952940348747664709

theorem tailTrace_1109916 : CollatzResearch.WordTrace tailWord_1109916 prefixEnd_1109916 253297952940348747664709 := by
  unfold tailWord_1109916
  simp only [CollatzResearch.WordTrace]
  refine ⟨20240981123485682703190801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26987974831314243604254401 20240981123485682703190801)
  ·
    refine ⟨15180735842614262027393101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20240981123485682703190801 15180735842614262027393101)
    ·
      refine ⟨5692775940980348260272413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15180735842614262027393101 5692775940980348260272413)
      ·
        refine ⟨2134790977867630597602155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5692775940980348260272413 2134790977867630597602155)
        ·
          refine ⟨3202186466801445896403233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2134790977867630597602155 3202186466801445896403233)
          ·
            refine ⟨2401639850101084422302425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3202186466801445896403233 2401639850101084422302425)
            ·
              refine ⟨1801229887575813316726819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2401639850101084422302425 1801229887575813316726819)
              ·
                refine ⟨2701844831363719975090229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1801229887575813316726819 2701844831363719975090229)
                ·
                  refine ⟨253297952940348747664709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2701844831363719975090229 253297952940348747664709)
                  ·
                    rfl

theorem cell21_1109916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 2, 2, 1, 5].length) (baseStart_1109916 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1109916 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1109916 prefixEnd_1109916 := by exact prefixLift 1109916
  have htrace : WordTrace (prefixWord ++ tailWord_1109916) baseStart_1109916 baseEnd_1109916 := by
    simpa [prefixWord, tailWord_1109916, baseEnd_1109916] using wordTrace_append hprefix tailTrace_1109916
  have hstable : (prefixWord ++ tailWord_1109916).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1109916).length < 2 ^ (prefixWord ++ tailWord_1109916).sum := by decide
  have hdescent : baseEnd_1109916 < baseStart_1109916 := by decide
  rcases family_descends (prefixWord ++ tailWord_1109916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1109981 : List Nat := [1, 4, 3, 1, 4, 1, 2, 1, 4]
def baseStart_1109981 : Nat := 118140960795 + 1109981 * 2 ^ 59
def prefixEnd_1109981 : Nat := 4983230072969 + 3 ^ 40 * 1109981 * 2
def baseEnd_1109981 : Nat := 253312786825923079081243

theorem tailTrace_1109981 : CollatzResearch.WordTrace tailWord_1109981 prefixEnd_1109981 253312786825923079081243 := by
  unfold tailWord_1109981
  simp only [CollatzResearch.WordTrace]
  refine ⟨40484332991735881507497797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26989555327823921004998531 40484332991735881507497797)
  ·
    refine ⟨7590812435950477782655837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 40484332991735881507497797 7590812435950477782655837)
    ·
      refine ⟨2846554663481429168495939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7590812435950477782655837 2846554663481429168495939)
      ·
        refine ⟨4269831995222143752743909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2846554663481429168495939 4269831995222143752743909)
        ·
          refine ⟨800593499104151953639483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4269831995222143752743909 800593499104151953639483)
          ·
            refine ⟨1200890248656227930459225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 800593499104151953639483 1200890248656227930459225)
            ·
              refine ⟨900667686492170947844419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1200890248656227930459225 900667686492170947844419)
              ·
                refine ⟨1351001529738256421766629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 900667686492170947844419 1351001529738256421766629)
                ·
                  refine ⟨253312786825923079081243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1351001529738256421766629 253312786825923079081243)
                  ·
                    rfl

theorem cell21_1109981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 4, 1, 2, 1, 4].length) (baseStart_1109981 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1109981 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1109981 prefixEnd_1109981 := by exact prefixLift 1109981
  have htrace : WordTrace (prefixWord ++ tailWord_1109981) baseStart_1109981 baseEnd_1109981 := by
    simpa [prefixWord, tailWord_1109981, baseEnd_1109981] using wordTrace_append hprefix tailTrace_1109981
  have hstable : (prefixWord ++ tailWord_1109981).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1109981).length < 2 ^ (prefixWord ++ tailWord_1109981).sum := by decide
  have hdescent : baseEnd_1109981 < baseStart_1109981 := by decide
  rcases family_descends (prefixWord ++ tailWord_1109981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1110020 : List Nat := [2, 3, 2, 4, 10]
def baseStart_1110020 : Nat := 118140960795 + 1110020 * 2 ^ 59
def prefixEnd_1110020 : Nat := 4983230072969 + 3 ^ 40 * 1110020 * 2
def baseEnd_1110020 : Nat := 3127428236509477505323

theorem tailTrace_1110020 : CollatzResearch.WordTrace tailWord_1110020 prefixEnd_1110020 3127428236509477505323 := by
  unfold tailWord_1110020
  simp only [CollatzResearch.WordTrace]
  refine ⟨20242877719297295584083757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26990503625729727445445009 20242877719297295584083757)
  ·
    refine ⟨7591079144736485844031409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20242877719297295584083757 7591079144736485844031409)
    ·
      refine ⟨5693309358552364383023557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7591079144736485844031409 5693309358552364383023557)
      ·
        refine ⟨1067495504728568321816917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5693309358552364383023557 1067495504728568321816917)
        ·
          refine ⟨3127428236509477505323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 10 1067495504728568321816917 3127428236509477505323)
          ·
            rfl

theorem cell21_1110020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 10].length) (baseStart_1110020 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1110020 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1110020 prefixEnd_1110020 := by exact prefixLift 1110020
  have htrace : WordTrace (prefixWord ++ tailWord_1110020) baseStart_1110020 baseEnd_1110020 := by
    simpa [prefixWord, tailWord_1110020, baseEnd_1110020] using wordTrace_append hprefix tailTrace_1110020
  have hstable : (prefixWord ++ tailWord_1110020).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1110020).length < 2 ^ (prefixWord ++ tailWord_1110020).sum := by decide
  have hdescent : baseEnd_1110020 < baseStart_1110020 := by decide
  rcases family_descends (prefixWord ++ tailWord_1110020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1110026 : List Nat := [3, 1, 2, 2, 4, 2, 2, 2, 3]
def baseStart_1110026 : Nat := 118140960795 + 1110026 * 2 ^ 59
def prefixEnd_1110026 : Nat := 4983230072969 + 3 ^ 40 * 1110026 * 2
def baseEnd_1110026 : Nat := 253323056439013000831151

theorem tailTrace_1110026 : CollatzResearch.WordTrace tailWord_1110026 prefixEnd_1110026 253323056439013000831151 := by
  unfold tailWord_1110026
  simp only [CollatzResearch.WordTrace]
  refine ⟨10121493569143213548221483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26990649517715236128590621 10121493569143213548221483)
  ·
    refine ⟨15182240353714820322332225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10121493569143213548221483 15182240353714820322332225)
    ·
      refine ⟨11386680265286115241749169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15182240353714820322332225 11386680265286115241749169)
      ·
        refine ⟨8540010198964586431311877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11386680265286115241749169 8540010198964586431311877)
        ·
          refine ⟨1601251912305859955870977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8540010198964586431311877 1601251912305859955870977)
          ·
            refine ⟨1200938934229394966903233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1601251912305859955870977 1200938934229394966903233)
            ·
              refine ⟨900704200672046225177425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1200938934229394966903233 900704200672046225177425)
              ·
                refine ⟨675528150504034668883069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 900704200672046225177425 675528150504034668883069)
                ·
                  refine ⟨253323056439013000831151, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 675528150504034668883069 253323056439013000831151)
                  ·
                    rfl

theorem cell21_1110026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 2, 2, 2, 3].length) (baseStart_1110026 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1110026 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1110026 prefixEnd_1110026 := by exact prefixLift 1110026
  have htrace : WordTrace (prefixWord ++ tailWord_1110026) baseStart_1110026 baseEnd_1110026 := by
    simpa [prefixWord, tailWord_1110026, baseEnd_1110026] using wordTrace_append hprefix tailTrace_1110026
  have hstable : (prefixWord ++ tailWord_1110026).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1110026).length < 2 ^ (prefixWord ++ tailWord_1110026).sum := by decide
  have hdescent : baseEnd_1110026 < baseStart_1110026 := by decide
  rcases family_descends (prefixWord ++ tailWord_1110026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1110037 : List Nat := [1, 3, 2, 1, 5, 2, 1, 6]
def baseStart_1110037 : Nat := 118140960795 + 1110037 * 2 ^ 59
def prefixEnd_1110037 : Nat := 4983230072969 + 3 ^ 40 * 1110037 * 2
def baseEnd_1110037 : Nat := 84441855596293142049265

theorem tailTrace_1110037 : CollatzResearch.WordTrace tailWord_1110037 prefixEnd_1110037 84441855596293142049265 := by
  unfold tailWord_1110037
  simp only [CollatzResearch.WordTrace]
  refine ⟨40486375479533003071536365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26990916986355335381024243 40486375479533003071536365)
  ·
    refine ⟨15182390804824876151826137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40486375479533003071536365 15182390804824876151826137)
    ·
      refine ⟨11386793103618657113869603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15182390804824876151826137 11386793103618657113869603)
      ·
        refine ⟨17080189655427985670804405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11386793103618657113869603 17080189655427985670804405)
        ·
          refine ⟨1601267780196373656637913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 17080189655427985670804405 1601267780196373656637913)
          ·
            refine ⟨1200950835147280242478435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1601267780196373656637913 1200950835147280242478435)
            ·
              refine ⟨1801426252720920363717653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1200950835147280242478435 1801426252720920363717653)
              ·
                refine ⟨84441855596293142049265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1801426252720920363717653 84441855596293142049265)
                ·
                  rfl

theorem cell21_1110037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 2, 1, 6].length) (baseStart_1110037 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1110037 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1110037 prefixEnd_1110037 := by exact prefixLift 1110037
  have htrace : WordTrace (prefixWord ++ tailWord_1110037) baseStart_1110037 baseEnd_1110037 := by
    simpa [prefixWord, tailWord_1110037, baseEnd_1110037] using wordTrace_append hprefix tailTrace_1110037
  have hstable : (prefixWord ++ tailWord_1110037).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1110037).length < 2 ^ (prefixWord ++ tailWord_1110037).sum := by decide
  have hdescent : baseEnd_1110037 < baseStart_1110037 := by decide
  rcases family_descends (prefixWord ++ tailWord_1110037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1110141 : List Nat := [1, 4, 1, 1, 3, 2, 2, 1, 6]
def baseStart_1110141 : Nat := 118140960795 + 1110141 * 2 ^ 59
def prefixEnd_1110141 : Nat := 4983230072969 + 3 ^ 40 * 1110141 * 2
def baseEnd_1110141 : Nat := 253349301005798356414249

theorem tailTrace_1110141 : CollatzResearch.WordTrace tailWord_1110141 prefixEnd_1110141 253349301005798356414249 := by
  unfold tailWord_1110141
  simp only [CollatzResearch.WordTrace]
  refine ⟨40490168671156228833322277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26993445780770819222214851 40490168671156228833322277)
  ·
    refine ⟨7591906625841792906247927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 40490168671156228833322277 7591906625841792906247927)
    ·
      refine ⟨11387859938762689359371891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7591906625841792906247927 11387859938762689359371891)
      ·
        refine ⟨17081789908144034039057837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11387859938762689359371891 17081789908144034039057837)
        ·
          refine ⟨6405671215554012764646689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17081789908144034039057837 6405671215554012764646689)
          ·
            refine ⟨4804253411665509573485017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6405671215554012764646689 4804253411665509573485017)
            ·
              refine ⟨3603190058749132180113763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4804253411665509573485017 3603190058749132180113763)
              ·
                refine ⟨5404785088123698270170645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3603190058749132180113763 5404785088123698270170645)
                ·
                  refine ⟨253349301005798356414249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5404785088123698270170645 253349301005798356414249)
                  ·
                    rfl

theorem cell21_1110141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 2, 1, 6].length) (baseStart_1110141 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1110141 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1110141 prefixEnd_1110141 := by exact prefixLift 1110141
  have htrace : WordTrace (prefixWord ++ tailWord_1110141) baseStart_1110141 baseEnd_1110141 := by
    simpa [prefixWord, tailWord_1110141, baseEnd_1110141] using wordTrace_append hprefix tailTrace_1110141
  have hstable : (prefixWord ++ tailWord_1110141).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1110141).length < 2 ^ (prefixWord ++ tailWord_1110141).sum := by decide
  have hdescent : baseEnd_1110141 < baseStart_1110141 := by decide
  rcases family_descends (prefixWord ++ tailWord_1110141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1110203 : List Nat := [1, 1, 1, 1, 1, 2, 7, 4, 3]
def baseStart_1110203 : Nat := 118140960795 + 1110203 * 2 ^ 59
def prefixEnd_1110203 : Nat := 4983230072969 + 3 ^ 40 * 1110203 * 2
def baseEnd_1110203 : Nat := 253363450250500026380789

theorem tailTrace_1110203 : CollatzResearch.WordTrace tailWord_1110203 prefixEnd_1110203 253363450250500026380789 := by
  unfold tailWord_1110203
  simp only [CollatzResearch.WordTrace]
  refine ⟨40492429996931613422079263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26994953331287742281386175 40492429996931613422079263)
  ·
    refine ⟨60738644995397420133118895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40492429996931613422079263 60738644995397420133118895)
    ·
      refine ⟨91107967493096130199678343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60738644995397420133118895 91107967493096130199678343)
      ·
        refine ⟨136661951239644195299517515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91107967493096130199678343 136661951239644195299517515)
        ·
          refine ⟨204992926859466292949276273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 136661951239644195299517515 204992926859466292949276273)
          ·
            refine ⟨153744695144599719711957205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 204992926859466292949276273 153744695144599719711957205)
            ·
              refine ⟨3603391292451555930748997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 153744695144599719711957205 3603391292451555930748997)
              ·
                refine ⟨675635867334666737015437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3603391292451555930748997 675635867334666737015437)
                ·
                  refine ⟨253363450250500026380789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 675635867334666737015437 253363450250500026380789)
                  ·
                    rfl

theorem cell21_1110203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 7, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 7, 4, 3].length) (baseStart_1110203 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1110203 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1110203 prefixEnd_1110203 := by exact prefixLift 1110203
  have htrace : WordTrace (prefixWord ++ tailWord_1110203) baseStart_1110203 baseEnd_1110203 := by
    simpa [prefixWord, tailWord_1110203, baseEnd_1110203] using wordTrace_append hprefix tailTrace_1110203
  have hstable : (prefixWord ++ tailWord_1110203).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1110203).length < 2 ^ (prefixWord ++ tailWord_1110203).sum := by decide
  have hdescent : baseEnd_1110203 < baseStart_1110203 := by decide
  rcases family_descends (prefixWord ++ tailWord_1110203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1110206 : List Nat := [4, 2, 1, 1, 5, 1, 1, 6]
def baseStart_1110206 : Nat := 118140960795 + 1110206 * 2 ^ 59
def prefixEnd_1110206 : Nat := 4983230072969 + 3 ^ 40 * 1110206 * 2
def baseEnd_1110206 : Nat := 84454711630457562610261

theorem tailTrace_1110206 : CollatzResearch.WordTrace tailWord_1110206 prefixEnd_1110206 84454711630457562610261 := by
  unfold tailWord_1110206
  simp only [CollatzResearch.WordTrace]
  refine ⟨5061567426990093116804809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 26995026277280496622958981 5061567426990093116804809)
  ·
    refine ⟨3796175570242569837603607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5061567426990093116804809 3796175570242569837603607)
    ·
      refine ⟨5694263355363854756405411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3796175570242569837603607 5694263355363854756405411)
      ·
        refine ⟨8541395033045782134608117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5694263355363854756405411 8541395033045782134608117)
        ·
          refine ⟨800755784348042075119511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 8541395033045782134608117 800755784348042075119511)
          ·
            refine ⟨1201133676522063112679267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 800755784348042075119511 1201133676522063112679267)
            ·
              refine ⟨1801700514783094669018901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1201133676522063112679267 1801700514783094669018901)
              ·
                refine ⟨84454711630457562610261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1801700514783094669018901 84454711630457562610261)
                ·
                  rfl

theorem cell21_1110206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 5, 1, 1, 6].length) (baseStart_1110206 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1110206 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1110206 prefixEnd_1110206 := by exact prefixLift 1110206
  have htrace : WordTrace (prefixWord ++ tailWord_1110206) baseStart_1110206 baseEnd_1110206 := by
    simpa [prefixWord, tailWord_1110206, baseEnd_1110206] using wordTrace_append hprefix tailTrace_1110206
  have hstable : (prefixWord ++ tailWord_1110206).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1110206).length < 2 ^ (prefixWord ++ tailWord_1110206).sum := by decide
  have hdescent : baseEnd_1110206 < baseStart_1110206 := by decide
  rcases family_descends (prefixWord ++ tailWord_1110206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1110220 : List Nat := [2, 2, 1, 6, 1, 1, 1, 2, 5]
def baseStart_1110220 : Nat := 118140960795 + 1110220 * 2 ^ 59
def prefixEnd_1110220 : Nat := 4983230072969 + 3 ^ 40 * 1110220 * 2
def baseEnd_1110220 : Nat := 253367329882111774597421

theorem tailTrace_1110220 : CollatzResearch.WordTrace tailWord_1110220 prefixEnd_1110220 253367329882111774597421 := by
  unfold tailWord_1110220
  simp only [CollatzResearch.WordTrace]
  refine ⟨20246525018935012662724057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26995366691913350216965409 20246525018935012662724057)
  ·
    refine ⟨15184893764201259497043043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20246525018935012662724057 15184893764201259497043043)
    ·
      refine ⟨22777340646301889245564565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15184893764201259497043043 22777340646301889245564565)
      ·
        refine ⟨1067687842795401058385839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 22777340646301889245564565 1067687842795401058385839)
        ·
          refine ⟨1601531764193101587578759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1067687842795401058385839 1601531764193101587578759)
          ·
            refine ⟨2402297646289652381368139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1601531764193101587578759 2402297646289652381368139)
            ·
              refine ⟨3603446469434478572052209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2402297646289652381368139 3603446469434478572052209)
              ·
                refine ⟨2702584852075858929039157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3603446469434478572052209 2702584852075858929039157)
                ·
                  refine ⟨253367329882111774597421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2702584852075858929039157 253367329882111774597421)
                  ·
                    rfl

theorem cell21_1110220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 1, 1, 2, 5].length) (baseStart_1110220 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1110220 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1110220 prefixEnd_1110220 := by exact prefixLift 1110220
  have htrace : WordTrace (prefixWord ++ tailWord_1110220) baseStart_1110220 baseEnd_1110220 := by
    simpa [prefixWord, tailWord_1110220, baseEnd_1110220] using wordTrace_append hprefix tailTrace_1110220
  have hstable : (prefixWord ++ tailWord_1110220).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1110220).length < 2 ^ (prefixWord ++ tailWord_1110220).sum := by decide
  have hdescent : baseEnd_1110220 < baseStart_1110220 := by decide
  rcases family_descends (prefixWord ++ tailWord_1110220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1110237 : List Nat := [1, 4, 3, 2, 1, 2, 2, 3, 3]
def baseStart_1110237 : Nat := 118140960795 + 1110237 * 2 ^ 59
def prefixEnd_1110237 : Nat := 4983230072969 + 3 ^ 40 * 1110237 * 2
def baseEnd_1110237 : Nat := 253371209513723522814053

theorem tailTrace_1110237 : CollatzResearch.WordTrace tailWord_1110237 prefixEnd_1110237 253371209513723522814053 := by
  unfold tailWord_1110237
  simp only [CollatzResearch.WordTrace]
  refine ⟨40493670078808437228816965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26995780052538958152544643 40493670078808437228816965)
  ·
    refine ⟨7592563139776581980403181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 40493670078808437228816965 7592563139776581980403181)
    ·
      refine ⟨2847211177416218242651193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7592563139776581980403181 2847211177416218242651193)
      ·
        refine ⟨2135408383062163681988395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2847211177416218242651193 2135408383062163681988395)
        ·
          refine ⟨3203112574593245522982593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2135408383062163681988395 3203112574593245522982593)
          ·
            refine ⟨2402334430944934142236945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3203112574593245522982593 2402334430944934142236945)
            ·
              refine ⟨1801750823208700606677709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2402334430944934142236945 1801750823208700606677709)
              ·
                refine ⟨675656558703262727504141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1801750823208700606677709 675656558703262727504141)
                ·
                  refine ⟨253371209513723522814053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 675656558703262727504141 253371209513723522814053)
                  ·
                    rfl

theorem cell21_1110237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 2, 2, 3, 3].length) (baseStart_1110237 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1110237 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1110237 prefixEnd_1110237 := by exact prefixLift 1110237
  have htrace : WordTrace (prefixWord ++ tailWord_1110237) baseStart_1110237 baseEnd_1110237 := by
    simpa [prefixWord, tailWord_1110237, baseEnd_1110237] using wordTrace_append hprefix tailTrace_1110237
  have hstable : (prefixWord ++ tailWord_1110237).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1110237).length < 2 ^ (prefixWord ++ tailWord_1110237).sum := by decide
  have hdescent : baseEnd_1110237 < baseStart_1110237 := by decide
  rcases family_descends (prefixWord ++ tailWord_1110237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1110324 : List Nat := [2, 5, 1, 1, 1, 2, 1, 8]
def baseStart_1110324 : Nat := 118140960795 + 1110324 * 2 ^ 59
def prefixEnd_1110324 : Nat := 4983230072969 + 3 ^ 40 * 1110324 * 2
def baseEnd_1110324 : Nat := 84463688033010234954625

theorem tailTrace_1110324 : CollatzResearch.WordTrace tailWord_1110324 prefixEnd_1110324 84463688033010234954625 := by
  unfold tailWord_1110324
  simp only [CollatzResearch.WordTrace]
  refine ⟨20248421614746625543617013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26997895486328834058156017 20248421614746625543617013)
  ·
    refine ⟨1898289526382496144714095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 20248421614746625543617013 1898289526382496144714095)
    ·
      refine ⟨2847434289573744217071143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1898289526382496144714095 2847434289573744217071143)
      ·
        refine ⟨4271151434360616325606715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2847434289573744217071143 4271151434360616325606715)
        ·
          refine ⟨6406727151540924488410073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4271151434360616325606715 6406727151540924488410073)
          ·
            refine ⟨4805045363655693366307555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6406727151540924488410073 4805045363655693366307555)
            ·
              refine ⟨7207568045483540049461333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4805045363655693366307555 7207568045483540049461333)
              ·
                refine ⟨84463688033010234954625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7207568045483540049461333 84463688033010234954625)
                ·
                  rfl

theorem cell21_1110324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 1, 8].length) (baseStart_1110324 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1110324 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1110324 prefixEnd_1110324 := by exact prefixLift 1110324
  have htrace : WordTrace (prefixWord ++ tailWord_1110324) baseStart_1110324 baseEnd_1110324 := by
    simpa [prefixWord, tailWord_1110324, baseEnd_1110324] using wordTrace_append hprefix tailTrace_1110324
  have hstable : (prefixWord ++ tailWord_1110324).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1110324).length < 2 ^ (prefixWord ++ tailWord_1110324).sum := by decide
  have hdescent : baseEnd_1110324 < baseStart_1110324 := by decide
  rcases family_descends (prefixWord ++ tailWord_1110324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1110420 : List Nat := [2, 4, 2, 1, 4, 1, 1, 2, 4]
def baseStart_1110420 : Nat := 118140960795 + 1110420 * 2 ^ 59
def prefixEnd_1110420 : Nat := 4983230072969 + 3 ^ 40 * 1110420 * 2
def baseEnd_1110420 : Nat := 253412972606955871263679

theorem tailTrace_1110420 : CollatzResearch.WordTrace tailWord_1110420 prefixEnd_1110420 253412972606955871263679 := by
  unfold tailWord_1110420
  simp only [CollatzResearch.WordTrace]
  refine ⟨20250172318572729741364357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27000229758096972988485809 20250172318572729741364357)
  ·
    refine ⟨3796907309732386826505817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 20250172318572729741364357 3796907309732386826505817)
    ·
      refine ⟨2847680482299290119879363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3796907309732386826505817 2847680482299290119879363)
      ·
        refine ⟨4271520723448935179819045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2847680482299290119879363 4271520723448935179819045)
        ·
          refine ⟨800910135646675346216071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4271520723448935179819045 800910135646675346216071)
          ·
            refine ⟨1201365203470013019324107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 800910135646675346216071 1201365203470013019324107)
            ·
              refine ⟨1802047805205019528986161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1201365203470013019324107 1802047805205019528986161)
              ·
                refine ⟨1351535853903764646739621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1802047805205019528986161 1351535853903764646739621)
                ·
                  refine ⟨253412972606955871263679, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1351535853903764646739621 253412972606955871263679)
                  ·
                    rfl

theorem cell21_1110420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 4, 1, 1, 2, 4].length) (baseStart_1110420 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1110420 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1110420 prefixEnd_1110420 := by exact prefixLift 1110420
  have htrace : WordTrace (prefixWord ++ tailWord_1110420) baseStart_1110420 baseEnd_1110420 := by
    simpa [prefixWord, tailWord_1110420, baseEnd_1110420] using wordTrace_append hprefix tailTrace_1110420
  have hstable : (prefixWord ++ tailWord_1110420).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1110420).length < 2 ^ (prefixWord ++ tailWord_1110420).sum := by decide
  have hdescent : baseEnd_1110420 < baseStart_1110420 := by decide
  rcases family_descends (prefixWord ++ tailWord_1110420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1110431 : List Nat := [1, 1, 2, 5, 1, 1, 1, 6, 3]
def baseStart_1110431 : Nat := 118140960795 + 1110431 * 2 ^ 59
def prefixEnd_1110431 : Nat := 4983230072969 + 3 ^ 40 * 1110431 * 2
def baseEnd_1110431 : Nat := 253415482956822296580323

theorem tailTrace_1110431 : CollatzResearch.WordTrace tailWord_1110431 prefixEnd_1110431 253415482956822296580323 := by
  unfold tailWord_1110431
  simp only [CollatzResearch.WordTrace]
  refine ⟨40500745840105608361379147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27000497226737072240919431 40500745840105608361379147)
  ·
    refine ⟨60751118760158412542068721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40500745840105608361379147 60751118760158412542068721)
    ·
      refine ⟨45563339070118809406551541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60751118760158412542068721 45563339070118809406551541)
      ·
        refine ⟨4271563037823638381864207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 45563339070118809406551541 4271563037823638381864207)
        ·
          refine ⟨6407344556735457572796311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4271563037823638381864207 6407344556735457572796311)
          ·
            refine ⟨9611016835103186359194467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6407344556735457572796311 9611016835103186359194467)
            ·
              refine ⟨14416525252654779538791701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9611016835103186359194467 14416525252654779538791701)
              ·
                refine ⟨675774621218192790880861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 14416525252654779538791701 675774621218192790880861)
                ·
                  refine ⟨253415482956822296580323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 675774621218192790880861 253415482956822296580323)
                  ·
                    rfl

theorem cell21_1110431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 1, 6, 3].length) (baseStart_1110431 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1110431 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1110431 prefixEnd_1110431 := by exact prefixLift 1110431
  have htrace : WordTrace (prefixWord ++ tailWord_1110431) baseStart_1110431 baseEnd_1110431 := by
    simpa [prefixWord, tailWord_1110431, baseEnd_1110431] using wordTrace_append hprefix tailTrace_1110431
  have hstable : (prefixWord ++ tailWord_1110431).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1110431).length < 2 ^ (prefixWord ++ tailWord_1110431).sum := by decide
  have hdescent : baseEnd_1110431 < baseStart_1110431 := by decide
  rcases family_descends (prefixWord ++ tailWord_1110431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1110473 : List Nat := [1, 2, 1, 1, 2, 1, 4, 2, 7]
def baseStart_1110473 : Nat := 118140960795 + 1110473 * 2 ^ 59
def prefixEnd_1110473 : Nat := 4983230072969 + 3 ^ 40 * 1110473 * 2
def baseEnd_1110473 : Nat := 253425067929039556880237

theorem tailTrace_1110473 : CollatzResearch.WordTrace tailWord_1110473 prefixEnd_1110473 253425067929039556880237 := by
  unfold tailWord_1110473
  simp only [CollatzResearch.WordTrace]
  refine ⟨40502277705953449534408073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27001518470635633022938715 40502277705953449534408073)
  ·
    refine ⟨30376708279465087150806055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40502277705953449534408073 30376708279465087150806055)
    ·
      refine ⟨45565062419197630726209083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30376708279465087150806055 45565062419197630726209083)
      ·
        refine ⟨68347593628796446089313625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45565062419197630726209083 68347593628796446089313625)
        ·
          refine ⟨51260695221597334566985219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 68347593628796446089313625 51260695221597334566985219)
          ·
            refine ⟨76891042832396001850477829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51260695221597334566985219 76891042832396001850477829)
            ·
              refine ⟨14417070531074250346964593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 76891042832396001850477829 14417070531074250346964593)
              ·
                refine ⟨10812802898305687760223445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14417070531074250346964593 10812802898305687760223445)
                ·
                  refine ⟨253425067929039556880237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10812802898305687760223445 253425067929039556880237)
                  ·
                    rfl

theorem cell21_1110473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 4, 2, 7].length) (baseStart_1110473 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1110473 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1110473 prefixEnd_1110473 := by exact prefixLift 1110473
  have htrace : WordTrace (prefixWord ++ tailWord_1110473) baseStart_1110473 baseEnd_1110473 := by
    simpa [prefixWord, tailWord_1110473, baseEnd_1110473] using wordTrace_append hprefix tailTrace_1110473
  have hstable : (prefixWord ++ tailWord_1110473).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1110473).length < 2 ^ (prefixWord ++ tailWord_1110473).sum := by decide
  have hdescent : baseEnd_1110473 < baseStart_1110473 := by decide
  rcases family_descends (prefixWord ++ tailWord_1110473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1110476 : List Nat := [2, 2, 1, 4, 3, 2, 7]
def baseStart_1110476 : Nat := 118140960795 + 1110476 * 2 ^ 59
def prefixEnd_1110476 : Nat := 4983230072969 + 3 ^ 40 * 1110476 * 2
def baseEnd_1110476 : Nat := 28158416952212468703359

theorem tailTrace_1110476 : CollatzResearch.WordTrace tailWord_1110476 prefixEnd_1110476 28158416952212468703359 := by
  unfold tailWord_1110476
  simp only [CollatzResearch.WordTrace]
  refine ⟨20251193562471290523383641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27001591416628387364511521 20251193562471290523383641)
  ·
    refine ⟨15188395171853467892537731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20251193562471290523383641 15188395171853467892537731)
    ·
      refine ⟨22782592757780201838806597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15188395171853467892537731 22782592757780201838806597)
      ·
        refine ⟨4271736142083787844776237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 22782592757780201838806597 4271736142083787844776237)
        ·
          refine ⟨1601901053281420441791089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4271736142083787844776237 1601901053281420441791089)
          ·
            refine ⟨1201425789961065331343317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1601901053281420441791089 1201425789961065331343317)
            ·
              refine ⟨28158416952212468703359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1201425789961065331343317 28158416952212468703359)
              ·
                rfl

theorem cell21_1110476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 2, 7].length) (baseStart_1110476 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1110476 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1110476 prefixEnd_1110476 := by exact prefixLift 1110476
  have htrace : WordTrace (prefixWord ++ tailWord_1110476) baseStart_1110476 baseEnd_1110476 := by
    simpa [prefixWord, tailWord_1110476, baseEnd_1110476] using wordTrace_append hprefix tailTrace_1110476
  have hstable : (prefixWord ++ tailWord_1110476).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1110476).length < 2 ^ (prefixWord ++ tailWord_1110476).sum := by decide
  have hdescent : baseEnd_1110476 < baseStart_1110476 := by decide
  rcases family_descends (prefixWord ++ tailWord_1110476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1110482 : List Nat := [3, 2, 2, 4, 1, 1, 3, 2, 3]
def baseStart_1110482 : Nat := 118140960795 + 1110482 * 2 ^ 59
def prefixEnd_1110482 : Nat := 4983230072969 + 3 ^ 40 * 1110482 * 2
def baseEnd_1110482 : Nat := 253427121851657541230219

theorem tailTrace_1110482 : CollatzResearch.WordTrace tailWord_1110482 prefixEnd_1110482 253427121851657541230219 := by
  unfold tailWord_1110482
  simp only [CollatzResearch.WordTrace]
  refine ⟨10125651490730211017871425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27001737308613896047657133 10125651490730211017871425)
  ·
    refine ⟨7594238618047658263403569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10125651490730211017871425 7594238618047658263403569)
    ·
      refine ⟨5695678963535743697552677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7594238618047658263403569 5695678963535743697552677)
      ·
        refine ⟨1067939805662951943291127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5695678963535743697552677 1067939805662951943291127)
        ·
          refine ⟨1601909708494427914936691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1067939805662951943291127 1601909708494427914936691)
          ·
            refine ⟨2402864562741641872405037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1601909708494427914936691 2402864562741641872405037)
            ·
              refine ⟨901074211028115702151889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2402864562741641872405037 901074211028115702151889)
              ·
                refine ⟨675805658271086776613917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 901074211028115702151889 675805658271086776613917)
                ·
                  refine ⟨253427121851657541230219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 675805658271086776613917 253427121851657541230219)
                  ·
                    rfl

theorem cell21_1110482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 1, 3, 2, 3].length) (baseStart_1110482 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1110482 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1110482 prefixEnd_1110482 := by exact prefixLift 1110482
  have htrace : WordTrace (prefixWord ++ tailWord_1110482) baseStart_1110482 baseEnd_1110482 := by
    simpa [prefixWord, tailWord_1110482, baseEnd_1110482] using wordTrace_append hprefix tailTrace_1110482
  have hstable : (prefixWord ++ tailWord_1110482).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1110482).length < 2 ^ (prefixWord ++ tailWord_1110482).sum := by decide
  have hdescent : baseEnd_1110482 < baseStart_1110482 := by decide
  rcases family_descends (prefixWord ++ tailWord_1110482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1110535 : List Nat := [1, 1, 4, 3, 3, 9]
def baseStart_1110535 : Nat := 118140960795 + 1110535 * 2 ^ 59
def prefixEnd_1110535 : Nat := 4983230072969 + 3 ^ 40 * 1110535 * 2
def baseEnd_1110535 : Nat := 9386637673101526920251

theorem tailTrace_1110535 : CollatzResearch.WordTrace tailWord_1110535 prefixEnd_1110535 9386637673101526920251 := by
  unfold tailWord_1110535
  simp only [CollatzResearch.WordTrace]
  refine ⟨40504539031728834123165059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27003026021152556082110039 40504539031728834123165059)
  ·
    refine ⟨60756808547593251184747589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40504539031728834123165059 60756808547593251184747589)
    ·
      refine ⟨11391901602673734597140173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 60756808547593251184747589 11391901602673734597140173)
      ·
        refine ⟨4271963101002650473927565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11391901602673734597140173 4271963101002650473927565)
        ·
          refine ⟨1601986162875993927722837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4271963101002650473927565 1601986162875993927722837)
          ·
            refine ⟨9386637673101526920251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1601986162875993927722837 9386637673101526920251)
            ·
              rfl

theorem cell21_1110535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 9].length) (baseStart_1110535 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1110535 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1110535 prefixEnd_1110535 := by exact prefixLift 1110535
  have htrace : WordTrace (prefixWord ++ tailWord_1110535) baseStart_1110535 baseEnd_1110535 := by
    simpa [prefixWord, tailWord_1110535, baseEnd_1110535] using wordTrace_append hprefix tailTrace_1110535
  have hstable : (prefixWord ++ tailWord_1110535).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1110535).length < 2 ^ (prefixWord ++ tailWord_1110535).sum := by decide
  have hdescent : baseEnd_1110535 < baseStart_1110535 := by decide
  rcases family_descends (prefixWord ++ tailWord_1110535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1110552 : List Nat := [2, 1, 2, 3, 3, 3, 1, 6]
def baseStart_1110552 : Nat := 118140960795 + 1110552 * 2 ^ 59
def prefixEnd_1110552 : Nat := 4983230072969 + 3 ^ 40 * 1110552 * 2
def baseEnd_1110552 : Nat := 84481032268450991687803

theorem tailTrace_1110552 : CollatzResearch.WordTrace tailWord_1110552 prefixEnd_1110552 84481032268450991687803 := by
  unfold tailWord_1110552
  simp only [CollatzResearch.WordTrace]
  refine ⟨20252579536333623013266955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27003439381778164017689273 20252579536333623013266955)
  ·
    refine ⟨30378869304500434519900433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20252579536333623013266955 30378869304500434519900433)
    ·
      refine ⟨22784151978375325889925325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30378869304500434519900433 22784151978375325889925325)
      ·
        refine ⟨8544056991890747208721997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22784151978375325889925325 8544056991890747208721997)
        ·
          refine ⟨3204021371959030203270749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8544056991890747208721997 3204021371959030203270749)
          ·
            refine ⟨1201508014484636326226531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3204021371959030203270749 1201508014484636326226531)
            ·
              refine ⟨1802262021726954489339797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1201508014484636326226531 1802262021726954489339797)
              ·
                refine ⟨84481032268450991687803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1802262021726954489339797 84481032268450991687803)
                ·
                  rfl

theorem cell21_1110552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 3, 1, 6].length) (baseStart_1110552 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1110552 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1110552 prefixEnd_1110552 := by exact prefixLift 1110552
  have htrace : WordTrace (prefixWord ++ tailWord_1110552) baseStart_1110552 baseEnd_1110552 := by
    simpa [prefixWord, tailWord_1110552, baseEnd_1110552] using wordTrace_append hprefix tailTrace_1110552
  have hstable : (prefixWord ++ tailWord_1110552).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1110552).length < 2 ^ (prefixWord ++ tailWord_1110552).sum := by decide
  have hdescent : baseEnd_1110552 < baseStart_1110552 := by decide
  rcases family_descends (prefixWord ++ tailWord_1110552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1110583 : List Nat := [1, 1, 3, 1, 2, 3, 4, 3, 3]
def baseStart_1110583 : Nat := 118140960795 + 1110583 * 2 ^ 59
def prefixEnd_1110583 : Nat := 4983230072969 + 3 ^ 40 * 1110583 * 2
def baseEnd_1110583 : Nat := 253450171427703810046679

theorem tailTrace_1110583 : CollatzResearch.WordTrace tailWord_1110583 prefixEnd_1110583 253450171427703810046679 := by
  unfold tailWord_1110583
  simp only [CollatzResearch.WordTrace]
  refine ⟨40506289735554938320912403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27004193157036625547274935 40506289735554938320912403)
  ·
    refine ⟨60759434603332407481368605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40506289735554938320912403 60759434603332407481368605)
    ·
      refine ⟨22784787976249652805513227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 60759434603332407481368605 22784787976249652805513227)
      ·
        refine ⟨34177181964374479208269841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22784787976249652805513227 34177181964374479208269841)
        ·
          refine ⟨25632886473280859406202381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34177181964374479208269841 25632886473280859406202381)
          ·
            refine ⟨9612332427480322277325893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25632886473280859406202381 9612332427480322277325893)
            ·
              refine ⟨1802312330152560426998605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9612332427480322277325893 1802312330152560426998605)
              ·
                refine ⟨675867123807210160124477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1802312330152560426998605 675867123807210160124477)
                ·
                  refine ⟨253450171427703810046679, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 675867123807210160124477 253450171427703810046679)
                  ·
                    rfl

theorem cell21_1110583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 4, 3, 3].length) (baseStart_1110583 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1110583 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1110583 prefixEnd_1110583 := by exact prefixLift 1110583
  have htrace : WordTrace (prefixWord ++ tailWord_1110583) baseStart_1110583 baseEnd_1110583 := by
    simpa [prefixWord, tailWord_1110583, baseEnd_1110583] using wordTrace_append hprefix tailTrace_1110583
  have hstable : (prefixWord ++ tailWord_1110583).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1110583).length < 2 ^ (prefixWord ++ tailWord_1110583).sum := by decide
  have hdescent : baseEnd_1110583 < baseStart_1110583 := by decide
  rcases family_descends (prefixWord ++ tailWord_1110583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1110597 : List Nat := [1, 3, 1, 1, 1, 5, 3, 2, 4]
def baseStart_1110597 : Nat := 118140960795 + 1110597 * 2 ^ 59
def prefixEnd_1110597 : Nat := 4983230072969 + 3 ^ 40 * 1110597 * 2
def baseEnd_1110597 : Nat := 253453366418442896813317

theorem tailTrace_1110597 : CollatzResearch.WordTrace tailWord_1110597 prefixEnd_1110597 253453366418442896813317 := by
  unfold tailWord_1110597
  simp only [CollatzResearch.WordTrace]
  refine ⟨40506800357504218711922045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27004533571669479141281363 40506800357504218711922045)
  ·
    refine ⟨15190050134064082016970767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40506800357504218711922045 15190050134064082016970767)
    ·
      refine ⟨22785075201096123025456151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15190050134064082016970767 22785075201096123025456151)
      ·
        refine ⟨34177612801644184538184227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22785075201096123025456151 34177612801644184538184227)
        ·
          refine ⟨51266419202466276807276341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34177612801644184538184227 51266419202466276807276341)
          ·
            refine ⟨4806226800231213450682157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 51266419202466276807276341 4806226800231213450682157)
            ·
              refine ⟨1802335050086705044005809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4806226800231213450682157 1802335050086705044005809)
              ·
                refine ⟨1351751287565028783004357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1802335050086705044005809 1351751287565028783004357)
                ·
                  refine ⟨253453366418442896813317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1351751287565028783004357 253453366418442896813317)
                  ·
                    rfl

theorem cell21_1110597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 3, 2, 4].length) (baseStart_1110597 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1110597 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1110597 prefixEnd_1110597 := by exact prefixLift 1110597
  have htrace : WordTrace (prefixWord ++ tailWord_1110597) baseStart_1110597 baseEnd_1110597 := by
    simpa [prefixWord, tailWord_1110597, baseEnd_1110597] using wordTrace_append hprefix tailTrace_1110597
  have hstable : (prefixWord ++ tailWord_1110597).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1110597).length < 2 ^ (prefixWord ++ tailWord_1110597).sum := by decide
  have hdescent : baseEnd_1110597 < baseStart_1110597 := by decide
  rcases family_descends (prefixWord ++ tailWord_1110597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1110645 : List Nat := [1, 3, 4, 2, 3, 1, 7]
def baseStart_1110645 : Nat := 118140960795 + 1110645 * 2 ^ 59
def prefixEnd_1110645 : Nat := 4983230072969 + 3 ^ 40 * 1110645 * 2
def baseEnd_1110645 : Nat := 28162702296933942223691

theorem tailTrace_1110645 : CollatzResearch.WordTrace tailWord_1110645 prefixEnd_1110645 28162702296933942223691 := by
  unfold tailWord_1110645
  simp only [CollatzResearch.WordTrace]
  refine ⟨40508551061330322909669389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27005700707553548606446259 40508551061330322909669389)
  ·
    refine ⟨15190706647998871091126021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40508551061330322909669389 15190706647998871091126021)
    ·
      refine ⟨2848257496499788329586129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15190706647998871091126021 2848257496499788329586129)
      ·
        refine ⟨2136193122374841247189597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2848257496499788329586129 2136193122374841247189597)
        ·
          refine ⟨801072420890565467696099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2136193122374841247189597 801072420890565467696099)
          ·
            refine ⟨1201608631335848201544149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 801072420890565467696099 1201608631335848201544149)
            ·
              refine ⟨28162702296933942223691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1201608631335848201544149 28162702296933942223691)
              ·
                rfl

theorem cell21_1110645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 3, 1, 7].length) (baseStart_1110645 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1110645 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1110645 prefixEnd_1110645 := by exact prefixLift 1110645
  have htrace : WordTrace (prefixWord ++ tailWord_1110645) baseStart_1110645 baseEnd_1110645 := by
    simpa [prefixWord, tailWord_1110645, baseEnd_1110645] using wordTrace_append hprefix tailTrace_1110645
  have hstable : (prefixWord ++ tailWord_1110645).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1110645).length < 2 ^ (prefixWord ++ tailWord_1110645).sum := by decide
  have hdescent : baseEnd_1110645 < baseStart_1110645 := by decide
  rcases family_descends (prefixWord ++ tailWord_1110645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1110656 : List Nat := [2, 1, 1, 2, 1, 5, 2, 1, 6]
def baseStart_1110656 : Nat := 118140960795 + 1110656 * 2 ^ 59
def prefixEnd_1110656 : Nat := 4983230072969 + 3 ^ 40 * 1110656 * 2
def baseEnd_1110656 : Nat := 253466831022271905329863

theorem tailTrace_1110656 : CollatzResearch.WordTrace tailWord_1110656 prefixEnd_1110656 253466831022271905329863 := by
  unfold tailWord_1110656
  simp only [CollatzResearch.WordTrace]
  refine ⟨20254476132145235894159911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27005968176193647858879881 20254476132145235894159911)
  ·
    refine ⟨30381714198217853841239867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20254476132145235894159911 30381714198217853841239867)
    ·
      refine ⟨45572571297326780761859801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30381714198217853841239867 45572571297326780761859801)
      ·
        refine ⟨34179428472995085571394851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45572571297326780761859801 34179428472995085571394851)
        ·
          refine ⟨51269142709492628357092277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34179428472995085571394851 51269142709492628357092277)
          ·
            refine ⟨4806482129014933908477401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 51269142709492628357092277 4806482129014933908477401)
            ·
              refine ⟨3604861596761200431358051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4806482129014933908477401 3604861596761200431358051)
              ·
                refine ⟨5407292395141800647037077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3604861596761200431358051 5407292395141800647037077)
                ·
                  refine ⟨253466831022271905329863, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5407292395141800647037077 253466831022271905329863)
                  ·
                    rfl

theorem cell21_1110656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 2, 1, 6].length) (baseStart_1110656 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1110656 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1110656 prefixEnd_1110656 := by exact prefixLift 1110656
  have htrace : WordTrace (prefixWord ++ tailWord_1110656) baseStart_1110656 baseEnd_1110656 := by
    simpa [prefixWord, tailWord_1110656, baseEnd_1110656] using wordTrace_append hprefix tailTrace_1110656
  have hstable : (prefixWord ++ tailWord_1110656).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1110656).length < 2 ^ (prefixWord ++ tailWord_1110656).sum := by decide
  have hdescent : baseEnd_1110656 < baseStart_1110656 := by decide
  rcases family_descends (prefixWord ++ tailWord_1110656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1110718 : List Nat := [4, 2, 1, 1, 2, 1, 2, 3, 5]
def baseStart_1110718 : Nat := 118140960795 + 1110718 * 2 ^ 59
def prefixEnd_1110718 : Nat := 4983230072969 + 3 ^ 40 * 1110718 * 2
def baseEnd_1110718 : Nat := 253480980266973575296403

theorem tailTrace_1110718 : CollatzResearch.WordTrace tailWord_1110718 prefixEnd_1110718 253480980266973575296403 := by
  unfold tailWord_1110718
  simp only [CollatzResearch.WordTrace]
  refine ⟨5063901698758232047134601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 27007475726710570918051205 5063901698758232047134601)
  ·
    refine ⟨3797926274068674035350951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5063901698758232047134601 3797926274068674035350951)
    ·
      refine ⟨5696889411103011053026427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3797926274068674035350951 5696889411103011053026427)
      ·
        refine ⟨8545334116654516579539641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5696889411103011053026427 8545334116654516579539641)
        ·
          refine ⟨6409000587490887434654731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8545334116654516579539641 6409000587490887434654731)
          ·
            refine ⟨9613500881236331151982097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6409000587490887434654731 9613500881236331151982097)
            ·
              refine ⟨7210125660927248363986573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9613500881236331151982097 7210125660927248363986573)
              ·
                refine ⟨2703797122847718136494965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7210125660927248363986573 2703797122847718136494965)
                ·
                  refine ⟨253480980266973575296403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2703797122847718136494965 253480980266973575296403)
                  ·
                    rfl

theorem cell21_1110718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 2, 3, 5].length) (baseStart_1110718 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1110718 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1110718 prefixEnd_1110718 := by exact prefixLift 1110718
  have htrace : WordTrace (prefixWord ++ tailWord_1110718) baseStart_1110718 baseEnd_1110718 := by
    simpa [prefixWord, tailWord_1110718, baseEnd_1110718] using wordTrace_append hprefix tailTrace_1110718
  have hstable : (prefixWord ++ tailWord_1110718).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1110718).length < 2 ^ (prefixWord ++ tailWord_1110718).sum := by decide
  have hdescent : baseEnd_1110718 < baseStart_1110718 := by decide
  rcases family_descends (prefixWord ++ tailWord_1110718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1110766 : List Nat := [4, 1, 2, 1, 1, 5, 1, 2, 4]
def baseStart_1110766 : Nat := 118140960795 + 1110766 * 2 ^ 59
def prefixEnd_1110766 : Nat := 4983230072969 + 3 ^ 40 * 1110766 * 2
def baseEnd_1110766 : Nat := 253491934520936158496305

theorem tailTrace_1110766 : CollatzResearch.WordTrace tailWord_1110766 prefixEnd_1110766 253491934520936158496305 := by
  unfold tailWord_1110766
  simp only [CollatzResearch.WordTrace]
  refine ⟨5064120536736495071853019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 27008642862594640383216101 5064120536736495071853019)
  ·
    refine ⟨7596180805104742607779529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5064120536736495071853019 7596180805104742607779529)
    ·
      refine ⟨5697135603828556955834647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7596180805104742607779529 5697135603828556955834647)
      ·
        refine ⟨8545703405742835433751971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5697135603828556955834647 8545703405742835433751971)
        ·
          refine ⟨12818555108614253150627957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8545703405742835433751971 12818555108614253150627957)
          ·
            refine ⟨1201739541432586232871371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 12818555108614253150627957 1201739541432586232871371)
            ·
              refine ⟨1802609312148879349307057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1201739541432586232871371 1802609312148879349307057)
              ·
                refine ⟨1351956984111659511980293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1802609312148879349307057 1351956984111659511980293)
                ·
                  refine ⟨253491934520936158496305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1351956984111659511980293 253491934520936158496305)
                  ·
                    rfl

theorem cell21_1110766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 5, 1, 2, 4].length) (baseStart_1110766 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1110766 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1110766 prefixEnd_1110766 := by exact prefixLift 1110766
  have htrace : WordTrace (prefixWord ++ tailWord_1110766) baseStart_1110766 baseEnd_1110766 := by
    simpa [prefixWord, tailWord_1110766, baseEnd_1110766] using wordTrace_append hprefix tailTrace_1110766
  have hstable : (prefixWord ++ tailWord_1110766).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1110766).length < 2 ^ (prefixWord ++ tailWord_1110766).sum := by decide
  have hdescent : baseEnd_1110766 < baseStart_1110766 := by decide
  rcases family_descends (prefixWord ++ tailWord_1110766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1110867 : List Nat := [1, 1, 1, 2, 1, 1, 3, 3, 8]
def baseStart_1110867 : Nat := 118140960795 + 1110867 * 2 ^ 59
def prefixEnd_1110867 : Nat := 4983230072969 + 3 ^ 40 * 1110867 * 2
def baseEnd_1110867 : Nat := 253514984096982427312765

theorem tailTrace_1110867 : CollatzResearch.WordTrace tailWord_1110867 prefixEnd_1110867 253514984096982427312765 := by
  unfold tailWord_1110867
  simp only [CollatzResearch.WordTrace]
  refine ⟨40516648066526054824250855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27011098711017369882833903 40516648066526054824250855)
  ·
    refine ⟨60774972099789082236376283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40516648066526054824250855 60774972099789082236376283)
    ·
      refine ⟨91162458149683623354564425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60774972099789082236376283 91162458149683623354564425)
      ·
        refine ⟨68371843612262717515923319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 91162458149683623354564425 68371843612262717515923319)
        ·
          refine ⟨102557765418394076273884979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68371843612262717515923319 102557765418394076273884979)
          ·
            refine ⟨153836648127591114410827469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 102557765418394076273884979 153836648127591114410827469)
            ·
              refine ⟨57688743047846667904060301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 153836648127591114410827469 57688743047846667904060301)
              ·
                refine ⟨21633278642942500464022613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 57688743047846667904060301 21633278642942500464022613)
                ·
                  refine ⟨253514984096982427312765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 21633278642942500464022613 253514984096982427312765)
                  ·
                    rfl

theorem cell21_1110867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 3, 8].length) (baseStart_1110867 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1110867 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1110867 prefixEnd_1110867 := by exact prefixLift 1110867
  have htrace : WordTrace (prefixWord ++ tailWord_1110867) baseStart_1110867 baseEnd_1110867 := by
    simpa [prefixWord, tailWord_1110867, baseEnd_1110867] using wordTrace_append hprefix tailTrace_1110867
  have hstable : (prefixWord ++ tailWord_1110867).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1110867).length < 2 ^ (prefixWord ++ tailWord_1110867).sum := by decide
  have hdescent : baseEnd_1110867 < baseStart_1110867 := by decide
  rcases family_descends (prefixWord ++ tailWord_1110867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1110887 : List Nat := [1, 1, 5, 1, 2, 3, 1, 4, 3]
def baseStart_1110887 : Nat := 118140960795 + 1110887 * 2 ^ 59
def prefixEnd_1110887 : Nat := 4983230072969 + 3 ^ 40 * 1110887 * 2
def baseEnd_1110887 : Nat := 253519548369466836979391

theorem tailTrace_1110887 : CollatzResearch.WordTrace tailWord_1110887 prefixEnd_1110887 253519548369466836979391 := by
  unfold tailWord_1110887
  simp only [CollatzResearch.WordTrace]
  refine ⟨40517377526453598239978915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27011585017635732159985943 40517377526453598239978915)
  ·
    refine ⟨60776066289680397359968373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40517377526453598239978915 60776066289680397359968373)
    ·
      refine ⟨5697756214657537252497035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 60776066289680397359968373 5697756214657537252497035)
      ·
        refine ⟨8546634321986305878745553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5697756214657537252497035 8546634321986305878745553)
        ·
          refine ⟨6409975741489729409059165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8546634321986305878745553 6409975741489729409059165)
          ·
            refine ⟨2403740903058648528397187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6409975741489729409059165 2403740903058648528397187)
            ·
              refine ⟨3605611354587972792595781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2403740903058648528397187 3605611354587972792595781)
              ·
                refine ⟨676052128985244898611709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3605611354587972792595781 676052128985244898611709)
                ·
                  refine ⟨253519548369466836979391, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 676052128985244898611709 253519548369466836979391)
                  ·
                    rfl

theorem cell21_1110887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 3, 1, 4, 3].length) (baseStart_1110887 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1110887 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1110887 prefixEnd_1110887 := by exact prefixLift 1110887
  have htrace : WordTrace (prefixWord ++ tailWord_1110887) baseStart_1110887 baseEnd_1110887 := by
    simpa [prefixWord, tailWord_1110887, baseEnd_1110887] using wordTrace_append hprefix tailTrace_1110887
  have hstable : (prefixWord ++ tailWord_1110887).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1110887).length < 2 ^ (prefixWord ++ tailWord_1110887).sum := by decide
  have hdescent : baseEnd_1110887 < baseStart_1110887 := by decide
  rcases family_descends (prefixWord ++ tailWord_1110887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1110901 : List Nat := [1, 3, 4, 1, 1, 2, 2, 3, 4]
def baseStart_1110901 : Nat := 118140960795 + 1110901 * 2 ^ 59
def prefixEnd_1110901 : Nat := 4983230072969 + 3 ^ 40 * 1110901 * 2
def baseEnd_1110901 : Nat := 253522743360205923746029

theorem tailTrace_1110901 : CollatzResearch.WordTrace tailWord_1110901 prefixEnd_1110901 253522743360205923746029 := by
  unfold tailWord_1110901
  simp only [CollatzResearch.WordTrace]
  refine ⟨40517888148402878630988557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27011925432268585753992371 40517888148402878630988557)
  ·
    refine ⟨15194208055651079486620709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40517888148402878630988557 15194208055651079486620709)
    ·
      refine ⟨2848914010434577403741383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15194208055651079486620709 2848914010434577403741383)
      ·
        refine ⟨4273371015651866105612075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2848914010434577403741383 4273371015651866105612075)
        ·
          refine ⟨6410056523477799158418113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4273371015651866105612075 6410056523477799158418113)
          ·
            refine ⟨4807542392608349368813585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6410056523477799158418113 4807542392608349368813585)
            ·
              refine ⟨3605656794456262026610189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4807542392608349368813585 3605656794456262026610189)
              ·
                refine ⟨1352121297921098259978821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3605656794456262026610189 1352121297921098259978821)
                ·
                  refine ⟨253522743360205923746029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1352121297921098259978821 253522743360205923746029)
                  ·
                    rfl

theorem cell21_1110901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 2, 3, 4].length) (baseStart_1110901 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1110901 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1110901 prefixEnd_1110901 := by exact prefixLift 1110901
  have htrace : WordTrace (prefixWord ++ tailWord_1110901) baseStart_1110901 baseEnd_1110901 := by
    simpa [prefixWord, tailWord_1110901, baseEnd_1110901] using wordTrace_append hprefix tailTrace_1110901
  have hstable : (prefixWord ++ tailWord_1110901).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1110901).length < 2 ^ (prefixWord ++ tailWord_1110901).sum := by decide
  have hdescent : baseEnd_1110901 < baseStart_1110901 := by decide
  rcases family_descends (prefixWord ++ tailWord_1110901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1110915 : List Nat := [1, 1, 1, 3, 4, 1, 5, 5]
def baseStart_1110915 : Nat := 118140960795 + 1110915 * 2 ^ 59
def prefixEnd_1110915 : Nat := 4983230072969 + 3 ^ 40 * 1110915 * 2
def baseEnd_1110915 : Nat := 84508646116981670170889

theorem tailTrace_1110915 : CollatzResearch.WordTrace tailWord_1110915 prefixEnd_1110915 84508646116981670170889 := by
  unfold tailWord_1110915
  simp only [CollatzResearch.WordTrace]
  refine ⟨40518398770352159021998199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27012265846901439347998799 40518398770352159021998199)
  ·
    refine ⟨60777598155528238532997299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40518398770352159021998199 60777598155528238532997299)
    ·
      refine ⟨91166397233292357799495949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60777598155528238532997299 91166397233292357799495949)
      ·
        refine ⟨34187398962484634174810981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 91166397233292357799495949 34187398962484634174810981)
        ·
          refine ⟨6410137305465868907777059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 34187398962484634174810981 6410137305465868907777059)
          ·
            refine ⟨9615205958198803361665589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6410137305465868907777059 9615205958198803361665589)
            ·
              refine ⟨901425558581137815156149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 9615205958198803361665589 901425558581137815156149)
              ·
                refine ⟨84508646116981670170889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 901425558581137815156149 84508646116981670170889)
                ·
                  rfl

theorem cell21_1110915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 5, 5].length) (baseStart_1110915 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1110915 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1110915 prefixEnd_1110915 := by exact prefixLift 1110915
  have htrace : WordTrace (prefixWord ++ tailWord_1110915) baseStart_1110915 baseEnd_1110915 := by
    simpa [prefixWord, tailWord_1110915, baseEnd_1110915] using wordTrace_append hprefix tailTrace_1110915
  have hstable : (prefixWord ++ tailWord_1110915).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1110915).length < 2 ^ (prefixWord ++ tailWord_1110915).sum := by decide
  have hdescent : baseEnd_1110915 < baseStart_1110915 := by decide
  rcases family_descends (prefixWord ++ tailWord_1110915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1110946 : List Nat := [3, 3, 1, 2, 2, 1, 1, 3, 5]
def baseStart_1110946 : Nat := 118140960795 + 1110946 * 2 ^ 59
def prefixEnd_1110946 : Nat := 4983230072969 + 3 ^ 40 * 1110946 * 2
def baseEnd_1110946 : Nat := 253533012973295845495937

theorem tailTrace_1110946 : CollatzResearch.WordTrace tailWord_1110946 prefixEnd_1110946 253533012973295845495937 := by
  unfold tailWord_1110946
  simp only [CollatzResearch.WordTrace]
  refine ⟨10129882358309962829094173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27013019622159900877584461 10129882358309962829094173)
  ·
    refine ⟨3798705884366236060910315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10129882358309962829094173 3798705884366236060910315)
    ·
      refine ⟨5698058826549354091365473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3798705884366236060910315 5698058826549354091365473)
      ·
        refine ⟨4273544119912015568524105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5698058826549354091365473 4273544119912015568524105)
        ·
          refine ⟨3205158089934011676393079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4273544119912015568524105 3205158089934011676393079)
          ·
            refine ⟨4807737134901017514589619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3205158089934011676393079 4807737134901017514589619)
            ·
              refine ⟨7211605702351526271884429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4807737134901017514589619 7211605702351526271884429)
              ·
                refine ⟨2704352138381822351956661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7211605702351526271884429 2704352138381822351956661)
                ·
                  refine ⟨253533012973295845495937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2704352138381822351956661 253533012973295845495937)
                  ·
                    rfl

theorem cell21_1110946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 1, 3, 5].length) (baseStart_1110946 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1110946 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1110946 prefixEnd_1110946 := by exact prefixLift 1110946
  have htrace : WordTrace (prefixWord ++ tailWord_1110946) baseStart_1110946 baseEnd_1110946 := by
    simpa [prefixWord, tailWord_1110946, baseEnd_1110946] using wordTrace_append hprefix tailTrace_1110946
  have hstable : (prefixWord ++ tailWord_1110946).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1110946).length < 2 ^ (prefixWord ++ tailWord_1110946).sum := by decide
  have hdescent : baseEnd_1110946 < baseStart_1110946 := by decide
  rcases family_descends (prefixWord ++ tailWord_1110946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1110966 : List Nat := [5, 1, 4, 1, 1, 1, 1, 7]
def baseStart_1110966 : Nat := 118140960795 + 1110966 * 2 ^ 59
def prefixEnd_1110966 : Nat := 4983230072969 + 3 ^ 40 * 1110966 * 2
def baseEnd_1110966 : Nat := 84512525748593418387521

theorem tailTrace_1110966 : CollatzResearch.WordTrace tailWord_1110966 prefixEnd_1110966 84512525748593418387521 := by
  unfold tailWord_1110966
  simp only [CollatzResearch.WordTrace]
  refine ⟨2532516180822962170756547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 27013505928778263154736501 2532516180822962170756547)
  ·
    refine ⟨3798774271234443256134821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2532516180822962170756547 3798774271234443256134821)
    ·
      refine ⟨712270175856458110525279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3798774271234443256134821 712270175856458110525279)
      ·
        refine ⟨1068405263784687165787919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 712270175856458110525279 1068405263784687165787919)
        ·
          refine ⟨1602607895677030748681879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1068405263784687165787919 1602607895677030748681879)
          ·
            refine ⟨2403911843515546123022819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1602607895677030748681879 2403911843515546123022819)
            ·
              refine ⟨3605867765273319184534229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2403911843515546123022819 3605867765273319184534229)
              ·
                refine ⟨84512525748593418387521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3605867765273319184534229 84512525748593418387521)
                ·
                  rfl

theorem cell21_1110966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 1, 1, 7].length) (baseStart_1110966 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1110966 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1110966 prefixEnd_1110966 := by exact prefixLift 1110966
  have htrace : WordTrace (prefixWord ++ tailWord_1110966) baseStart_1110966 baseEnd_1110966 := by
    simpa [prefixWord, tailWord_1110966, baseEnd_1110966] using wordTrace_append hprefix tailTrace_1110966
  have hstable : (prefixWord ++ tailWord_1110966).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1110966).length < 2 ^ (prefixWord ++ tailWord_1110966).sum := by decide
  have hdescent : baseEnd_1110966 < baseStart_1110966 := by decide
  rcases family_descends (prefixWord ++ tailWord_1110966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1111050 : List Nat := [3, 1, 2, 2, 3, 10]
def baseStart_1111050 : Nat := 118140960795 + 1111050 * 2 ^ 59
def prefixEnd_1111050 : Nat := 4983230072969 + 3 ^ 40 * 1111050 * 2
def baseEnd_1111050 : Nat := 9390990636674621324533

theorem tailTrace_1111050 : CollatzResearch.WordTrace tailWord_1111050 prefixEnd_1111050 9390990636674621324533 := by
  unfold tailWord_1111050
  simp only [CollatzResearch.WordTrace]
  refine ⟨10130830656215769269540651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27015548416575384718775069 10130830656215769269540651)
  ·
    refine ⟨15196245984323653904310977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10130830656215769269540651 15196245984323653904310977)
    ·
      refine ⟨11397184488242740428233233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15196245984323653904310977 11397184488242740428233233)
      ·
        refine ⟨8547888366182055321174925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11397184488242740428233233 8547888366182055321174925)
        ·
          refine ⟨3205458137318270745440597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8547888366182055321174925 3205458137318270745440597)
          ·
            refine ⟨9390990636674621324533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 3205458137318270745440597 9390990636674621324533)
            ·
              rfl

theorem cell21_1111050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 10].length) (baseStart_1111050 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1111050 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1111050 prefixEnd_1111050 := by exact prefixLift 1111050
  have htrace : WordTrace (prefixWord ++ tailWord_1111050) baseStart_1111050 baseEnd_1111050 := by
    simpa [prefixWord, tailWord_1111050, baseEnd_1111050] using wordTrace_append hprefix tailTrace_1111050
  have hstable : (prefixWord ++ tailWord_1111050).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1111050).length < 2 ^ (prefixWord ++ tailWord_1111050).sum := by decide
  have hdescent : baseEnd_1111050 < baseStart_1111050 := by decide
  rcases family_descends (prefixWord ++ tailWord_1111050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1111095 : List Nat := [1, 1, 3, 1, 2, 2, 1, 4, 6]
def baseStart_1111095 : Nat := 118140960795 + 1111095 * 2 ^ 59
def prefixEnd_1111095 : Nat := 4983230072969 + 3 ^ 40 * 1111095 * 2
def baseEnd_1111095 : Nat := 253567016803304697512299

theorem tailTrace_1111095 : CollatzResearch.WordTrace tailWord_1111095 prefixEnd_1111095 253567016803304697512299 := by
  unfold tailWord_1111095
  simp only [CollatzResearch.WordTrace]
  refine ⟨40524963909700049763550739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27016642606466699842367159 40524963909700049763550739)
  ·
    refine ⟨60787445864550074645326109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40524963909700049763550739 60787445864550074645326109)
    ·
      refine ⟨22795292199206277991997291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 60787445864550074645326109 22795292199206277991997291)
      ·
        refine ⟨34192938298809416987995937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22795292199206277991997291 34192938298809416987995937)
        ·
          refine ⟨25644703724107062740996953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34192938298809416987995937 25644703724107062740996953)
          ·
            refine ⟨19233527793080297055747715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25644703724107062740996953 19233527793080297055747715)
            ·
              refine ⟨28850291689620445583621573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19233527793080297055747715 28850291689620445583621573)
              ·
                refine ⟨5409429691803833546929045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 28850291689620445583621573 5409429691803833546929045)
                ·
                  refine ⟨253567016803304697512299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5409429691803833546929045 253567016803304697512299)
                  ·
                    rfl

theorem cell21_1111095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 4, 6].length) (baseStart_1111095 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1111095 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1111095 prefixEnd_1111095 := by exact prefixLift 1111095
  have htrace : WordTrace (prefixWord ++ tailWord_1111095) baseStart_1111095 baseEnd_1111095 := by
    simpa [prefixWord, tailWord_1111095, baseEnd_1111095] using wordTrace_append hprefix tailTrace_1111095
  have hstable : (prefixWord ++ tailWord_1111095).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1111095).length < 2 ^ (prefixWord ++ tailWord_1111095).sum := by decide
  have hdescent : baseEnd_1111095 < baseStart_1111095 := by decide
  rcases family_descends (prefixWord ++ tailWord_1111095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1111098 : List Nat := [3, 1, 1, 1, 3, 1, 3, 5, 3]
def baseStart_1111098 : Nat := 118140960795 + 1111098 * 2 ^ 59
def prefixEnd_1111098 : Nat := 4983230072969 + 3 ^ 40 * 1111098 * 2
def baseEnd_1111098 : Nat := 253567701444177358962293

theorem tailTrace_1111098 : CollatzResearch.WordTrace tailWord_1111098 prefixEnd_1111098 253567701444177358962293 := by
  unfold tailWord_1111098
  simp only [CollatzResearch.WordTrace]
  refine ⟨10131268332172295318977487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27016715552459454183939965 10131268332172295318977487)
  ·
    refine ⟨15196902498258442978466231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10131268332172295318977487 15196902498258442978466231)
    ·
      refine ⟨22795353747387664467699347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15196902498258442978466231 22795353747387664467699347)
      ·
        refine ⟨34193030621081496701549021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22795353747387664467699347 34193030621081496701549021)
        ·
          refine ⟨12822386482905561263080883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34193030621081496701549021 12822386482905561263080883)
          ·
            refine ⟨19233579724358341894621325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12822386482905561263080883 19233579724358341894621325)
            ·
              refine ⟨7212592396634378210482997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19233579724358341894621325 7212592396634378210482997)
              ·
                refine ⟨676180537184472957232781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7212592396634378210482997 676180537184472957232781)
                ·
                  refine ⟨253567701444177358962293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 676180537184472957232781 253567701444177358962293)
                  ·
                    rfl

theorem cell21_1111098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 3, 5, 3].length) (baseStart_1111098 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1111098 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1111098 prefixEnd_1111098 := by exact prefixLift 1111098
  have htrace : WordTrace (prefixWord ++ tailWord_1111098) baseStart_1111098 baseEnd_1111098 := by
    simpa [prefixWord, tailWord_1111098, baseEnd_1111098] using wordTrace_append hprefix tailTrace_1111098
  have hstable : (prefixWord ++ tailWord_1111098).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1111098).length < 2 ^ (prefixWord ++ tailWord_1111098).sum := by decide
  have hdescent : baseEnd_1111098 < baseStart_1111098 := by decide
  rcases family_descends (prefixWord ++ tailWord_1111098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1111143 : List Nat := [1, 1, 5, 1, 1, 3, 4, 5]
def baseStart_1111143 : Nat := 118140960795 + 1111143 * 2 ^ 59
def prefixEnd_1111143 : Nat := 4983230072969 + 3 ^ 40 * 1111143 * 2
def baseEnd_1111143 : Nat := 84525990352422426904067

theorem tailTrace_1111143 : CollatzResearch.WordTrace tailWord_1111143 prefixEnd_1111143 84525990352422426904067 := by
  unfold tailWord_1111143
  simp only [CollatzResearch.WordTrace]
  refine ⟨40526714613526153961298083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27017809742350769307532055 40526714613526153961298083)
  ·
    refine ⟨60790071920289230941947125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40526714613526153961298083 60790071920289230941947125)
    ·
      refine ⟨5699069242527115400807543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 60790071920289230941947125 5699069242527115400807543)
      ·
        refine ⟨8548603863790673101211315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5699069242527115400807543 8548603863790673101211315)
        ·
          refine ⟨12822905795686009651816973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8548603863790673101211315 12822905795686009651816973)
          ·
            refine ⟨4808589673382253619431365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12822905795686009651816973 4808589673382253619431365)
            ·
              refine ⟨901610563759172553643381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4808589673382253619431365 901610563759172553643381)
              ·
                refine ⟨84525990352422426904067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 901610563759172553643381 84525990352422426904067)
                ·
                  rfl

theorem cell21_1111143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 4, 5].length) (baseStart_1111143 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1111143 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1111143 prefixEnd_1111143 := by exact prefixLift 1111143
  have htrace : WordTrace (prefixWord ++ tailWord_1111143) baseStart_1111143 baseEnd_1111143 := by
    simpa [prefixWord, tailWord_1111143, baseEnd_1111143] using wordTrace_append hprefix tailTrace_1111143
  have hstable : (prefixWord ++ tailWord_1111143).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1111143).length < 2 ^ (prefixWord ++ tailWord_1111143).sum := by decide
  have hdescent : baseEnd_1111143 < baseStart_1111143 := by decide
  rcases family_descends (prefixWord ++ tailWord_1111143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1111166 : List Nat := [4, 2, 4, 1, 2, 1, 1, 1, 5]
def baseStart_1111166 : Nat := 118140960795 + 1111166 * 2 ^ 59
def prefixEnd_1111166 : Nat := 4983230072969 + 3 ^ 40 * 1111166 * 2
def baseEnd_1111166 : Nat := 253583219970624351828821

theorem tailTrace_1111166 : CollatzResearch.WordTrace tailWord_1111166 prefixEnd_1111166 253583219970624351828821 := by
  unfold tailWord_1111166
  simp only [CollatzResearch.WordTrace]
  refine ⟨5065944186555353611173169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 27018368994961885926256901 5065944186555353611173169)
  ·
    refine ⟨3799458139916515208379877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5065944186555353611173169 3799458139916515208379877)
    ·
      refine ⟨712398401234346601571227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3799458139916515208379877 712398401234346601571227)
      ·
        refine ⟨1068597601851519902356841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 712398401234346601571227 1068597601851519902356841)
        ·
          refine ⟨801448201388639926767631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1068597601851519902356841 801448201388639926767631)
          ·
            refine ⟨1202172302082959890151447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 801448201388639926767631 1202172302082959890151447)
            ·
              refine ⟨1803258453124439835227171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1202172302082959890151447 1803258453124439835227171)
              ·
                refine ⟨2704887679686659752840757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1803258453124439835227171 2704887679686659752840757)
                ·
                  refine ⟨253583219970624351828821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2704887679686659752840757 253583219970624351828821)
                  ·
                    rfl

theorem cell21_1111166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 2, 1, 1, 1, 5].length) (baseStart_1111166 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1111166 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1111166 prefixEnd_1111166 := by exact prefixLift 1111166
  have htrace : WordTrace (prefixWord ++ tailWord_1111166) baseStart_1111166 baseEnd_1111166 := by
    simpa [prefixWord, tailWord_1111166, baseEnd_1111166] using wordTrace_append hprefix tailTrace_1111166
  have hstable : (prefixWord ++ tailWord_1111166).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1111166).length < 2 ^ (prefixWord ++ tailWord_1111166).sum := by decide
  have hdescent : baseEnd_1111166 < baseStart_1111166 := by decide
  rcases family_descends (prefixWord ++ tailWord_1111166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1111171 : List Nat := [1, 1, 1, 3, 3, 2, 1, 3, 6]
def baseStart_1111171 : Nat := 118140960795 + 1111171 * 2 ^ 59
def prefixEnd_1111171 : Nat := 4983230072969 + 3 ^ 40 * 1111171 * 2
def baseEnd_1111171 : Nat := 253584361038745454245477

theorem tailTrace_1111171 : CollatzResearch.WordTrace tailWord_1111171 prefixEnd_1111171 253584361038745454245477 := by
  unfold tailWord_1111171
  simp only [CollatzResearch.WordTrace]
  refine ⟨40527735857424714743317367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27018490571616476495544911 40527735857424714743317367)
  ·
    refine ⟨60791603786137072114976051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40527735857424714743317367 60791603786137072114976051)
    ·
      refine ⟨91187405679205608172464077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60791603786137072114976051 91187405679205608172464077)
      ·
        refine ⟨34195277129702103064674029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 91187405679205608172464077 34195277129702103064674029)
        ·
          refine ⟨12823228923638288649252761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34195277129702103064674029 12823228923638288649252761)
          ·
            refine ⟨9617421692728716486939571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12823228923638288649252761 9617421692728716486939571)
            ·
              refine ⟨14426132539093074730409357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9617421692728716486939571 14426132539093074730409357)
              ·
                refine ⟨5409799702159903023903509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14426132539093074730409357 5409799702159903023903509)
                ·
                  refine ⟨253584361038745454245477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5409799702159903023903509 253584361038745454245477)
                  ·
                    rfl

theorem cell21_1111171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 1, 3, 6].length) (baseStart_1111171 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1111171 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1111171 prefixEnd_1111171 := by exact prefixLift 1111171
  have htrace : WordTrace (prefixWord ++ tailWord_1111171) baseStart_1111171 baseEnd_1111171 := by
    simpa [prefixWord, tailWord_1111171, baseEnd_1111171] using wordTrace_append hprefix tailTrace_1111171
  have hstable : (prefixWord ++ tailWord_1111171).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1111171).length < 2 ^ (prefixWord ++ tailWord_1111171).sum := by decide
  have hdescent : baseEnd_1111171 < baseStart_1111171 := by decide
  rcases family_descends (prefixWord ++ tailWord_1111171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1111216 : List Nat := [2, 1, 1, 1, 2, 1, 2, 4, 7]
def baseStart_1111216 : Nat := 118140960795 + 1111216 * 2 ^ 59
def prefixEnd_1111216 : Nat := 4983230072969 + 3 ^ 40 * 1111216 * 2
def baseEnd_1111216 : Nat := 253594630651835375995385

theorem tailTrace_1111216 : CollatzResearch.WordTrace tailWord_1111216 prefixEnd_1111216 253594630651835375995385 := by
  unfold tailWord_1111216
  simp only [CollatzResearch.WordTrace]
  refine ⟨20264688571130843714352751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27019584761507791619137001 20264688571130843714352751)
  ·
    refine ⟨30397032856696265571529127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20264688571130843714352751 30397032856696265571529127)
    ·
      refine ⟨45595549285044398357293691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30397032856696265571529127 45595549285044398357293691)
      ·
        refine ⟨68393323927566597535940537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45595549285044398357293691 68393323927566597535940537)
        ·
          refine ⟨51294992945674948151955403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 68393323927566597535940537 51294992945674948151955403)
          ·
            refine ⟨76942489418512422227933105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51294992945674948151955403 76942489418512422227933105)
            ·
              refine ⟨57706867063884316670949829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 76942489418512422227933105 57706867063884316670949829)
              ·
                refine ⟨10820037574478309375803093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 57706867063884316670949829 10820037574478309375803093)
                ·
                  refine ⟨253594630651835375995385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10820037574478309375803093 253594630651835375995385)
                  ·
                    rfl

theorem cell21_1111216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 4, 7].length) (baseStart_1111216 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1111216 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1111216 prefixEnd_1111216 := by exact prefixLift 1111216
  have htrace : WordTrace (prefixWord ++ tailWord_1111216) baseStart_1111216 baseEnd_1111216 := by
    simpa [prefixWord, tailWord_1111216, baseEnd_1111216] using wordTrace_append hprefix tailTrace_1111216
  have hstable : (prefixWord ++ tailWord_1111216).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1111216).length < 2 ^ (prefixWord ++ tailWord_1111216).sum := by decide
  have hdescent : baseEnd_1111216 < baseStart_1111216 := by decide
  rcases family_descends (prefixWord ++ tailWord_1111216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1111236 : List Nat := [2, 3, 3, 1, 3, 2, 1, 6]
def baseStart_1111236 : Nat := 118140960795 + 1111236 * 2 ^ 59
def prefixEnd_1111236 : Nat := 4983230072969 + 3 ^ 40 * 1111236 * 2
def baseEnd_1111236 : Nat := 84533064974773261887337

theorem tailTrace_1111236 : CollatzResearch.WordTrace tailWord_1111236 prefixEnd_1111236 84533064974773261887337 := by
  unfold tailWord_1111236
  simp only [CollatzResearch.WordTrace]
  refine ⟨20265053301094615422216781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27020071068126153896289041 20265053301094615422216781)
  ·
    refine ⟨7599394987910480783331293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20265053301094615422216781 7599394987910480783331293)
    ·
      refine ⟨2849773120466430293749235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7599394987910480783331293 2849773120466430293749235)
      ·
        refine ⟨4274659680699645440623853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2849773120466430293749235 4274659680699645440623853)
        ·
          refine ⟨1602997380262367040233945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4274659680699645440623853 1602997380262367040233945)
          ·
            refine ⟨1202248035196775280175459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1602997380262367040233945 1202248035196775280175459)
            ·
              refine ⟨1803372052795162920263189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1202248035196775280175459 1803372052795162920263189)
              ·
                refine ⟨84533064974773261887337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1803372052795162920263189 84533064974773261887337)
                ·
                  rfl

theorem cell21_1111236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 2, 1, 6].length) (baseStart_1111236 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1111236 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1111236 prefixEnd_1111236 := by exact prefixLift 1111236
  have htrace : WordTrace (prefixWord ++ tailWord_1111236) baseStart_1111236 baseEnd_1111236 := by
    simpa [prefixWord, tailWord_1111236, baseEnd_1111236] using wordTrace_append hprefix tailTrace_1111236
  have hstable : (prefixWord ++ tailWord_1111236).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1111236).length < 2 ^ (prefixWord ++ tailWord_1111236).sum := by decide
  have hdescent : baseEnd_1111236 < baseStart_1111236 := by decide
  rcases family_descends (prefixWord ++ tailWord_1111236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1111354 : List Nat := [3, 1, 1, 1, 4, 1, 4, 6]
def baseStart_1111354 : Nat := 118140960795 + 1111354 * 2 ^ 59
def prefixEnd_1111354 : Nat := 4983230072969 + 3 ^ 40 * 1111354 * 2
def baseEnd_1111354 : Nat := 84542041377325934231701

theorem tailTrace_1111354 : CollatzResearch.WordTrace tailWord_1111354 prefixEnd_1111354 84542041377325934231701 := by
  unfold tailWord_1111354
  simp only [CollatzResearch.WordTrace]
  refine ⟨10133602603940434249307279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27022940277174491331486077 10133602603940434249307279)
  ·
    refine ⟨15200403905910651373960919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10133602603940434249307279 15200403905910651373960919)
    ·
      refine ⟨22800605858865977060941379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15200403905910651373960919 22800605858865977060941379)
      ·
        refine ⟨34200908788298965591412069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22800605858865977060941379 34200908788298965591412069)
        ·
          refine ⟨6412670397806056048389763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 34200908788298965591412069 6412670397806056048389763)
          ·
            refine ⟨9619005596709084072584645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6412670397806056048389763 9619005596709084072584645)
            ·
              refine ⟨1803563549382953263609621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9619005596709084072584645 1803563549382953263609621)
              ·
                refine ⟨84542041377325934231701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1803563549382953263609621 84542041377325934231701)
                ·
                  rfl

theorem cell21_1111354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 4, 6].length) (baseStart_1111354 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1111354 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1111354 prefixEnd_1111354 := by exact prefixLift 1111354
  have htrace : WordTrace (prefixWord ++ tailWord_1111354) baseStart_1111354 baseEnd_1111354 := by
    simpa [prefixWord, tailWord_1111354, baseEnd_1111354] using wordTrace_append hprefix tailTrace_1111354
  have hstable : (prefixWord ++ tailWord_1111354).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1111354).length < 2 ^ (prefixWord ++ tailWord_1111354).sum := by decide
  have hdescent : baseEnd_1111354 < baseStart_1111354 := by decide
  rcases family_descends (prefixWord ++ tailWord_1111354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1111368 : List Nat := [2, 1, 3, 1, 1, 2, 1, 3, 7]
def baseStart_1111368 : Nat := 118140960795 + 1111368 * 2 ^ 59
def prefixEnd_1111368 : Nat := 4983230072969 + 3 ^ 40 * 1111368 * 2
def baseEnd_1111368 : Nat := 253629319122716889461741

theorem tailTrace_1111368 : CollatzResearch.WordTrace tailWord_1111368 prefixEnd_1111368 253629319122716889461741 := by
  unfold tailWord_1111368
  simp only [CollatzResearch.WordTrace]
  refine ⟨20267460518855508694119379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27023280691807344925492505 20267460518855508694119379)
  ·
    refine ⟨30401190778283263041179069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20267460518855508694119379 30401190778283263041179069)
    ·
      refine ⟨11400446541856223640442151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30401190778283263041179069 11400446541856223640442151)
      ·
        refine ⟨17100669812784335460663227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11400446541856223640442151 17100669812784335460663227)
        ·
          refine ⟨25651004719176503190994841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17100669812784335460663227 25651004719176503190994841)
          ·
            refine ⟨19238253539382377393246131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25651004719176503190994841 19238253539382377393246131)
            ·
              refine ⟨28857380309073566089869197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19238253539382377393246131 28857380309073566089869197)
              ·
                refine ⟨10821517615902587283700949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28857380309073566089869197 10821517615902587283700949)
                ·
                  refine ⟨253629319122716889461741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10821517615902587283700949 253629319122716889461741)
                  ·
                    rfl

theorem cell21_1111368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 3, 7].length) (baseStart_1111368 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1111368 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1111368 prefixEnd_1111368 := by exact prefixLift 1111368
  have htrace : WordTrace (prefixWord ++ tailWord_1111368) baseStart_1111368 baseEnd_1111368 := by
    simpa [prefixWord, tailWord_1111368, baseEnd_1111368] using wordTrace_append hprefix tailTrace_1111368
  have hstable : (prefixWord ++ tailWord_1111368).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1111368).length < 2 ^ (prefixWord ++ tailWord_1111368).sum := by decide
  have hdescent : baseEnd_1111368 < baseStart_1111368 := by decide
  rcases family_descends (prefixWord ++ tailWord_1111368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1111475 : List Nat := [1, 1, 1, 2, 3, 1, 1, 7, 4]
def baseStart_1111475 : Nat := 118140960795 + 1111475 * 2 ^ 59
def prefixEnd_1111475 : Nat := 4983230072969 + 3 ^ 40 * 1111475 * 2
def baseEnd_1111475 : Nat := 253653737980508481178189

theorem tailTrace_1111475 : CollatzResearch.WordTrace tailWord_1111475 prefixEnd_1111475 253653737980508481178189 := by
  unfold tailWord_1111475
  simp only [CollatzResearch.WordTrace]
  refine ⟨40538823648323374662383879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27025882432215583108255919 40538823648323374662383879)
  ·
    refine ⟨60808235472485061993575819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40538823648323374662383879 60808235472485061993575819)
    ·
      refine ⟨91212353208727592990363729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60808235472485061993575819 91212353208727592990363729)
      ·
        refine ⟨68409264906545694742772797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 91212353208727592990363729 68409264906545694742772797)
        ·
          refine ⟨25653474339954635528539799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 68409264906545694742772797 25653474339954635528539799)
          ·
            refine ⟨38480211509931953292809699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25653474339954635528539799 38480211509931953292809699)
            ·
              refine ⟨57720317264897929939214549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38480211509931953292809699 57720317264897929939214549)
              ·
                refine ⟨1352819935896045232950341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 57720317264897929939214549 1352819935896045232950341)
                ·
                  refine ⟨253653737980508481178189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1352819935896045232950341 253653737980508481178189)
                  ·
                    rfl

theorem cell21_1111475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 7, 4].length) (baseStart_1111475 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1111475 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1111475 prefixEnd_1111475 := by exact prefixLift 1111475
  have htrace : WordTrace (prefixWord ++ tailWord_1111475) baseStart_1111475 baseEnd_1111475 := by
    simpa [prefixWord, tailWord_1111475, baseEnd_1111475] using wordTrace_append hprefix tailTrace_1111475
  have hstable : (prefixWord ++ tailWord_1111475).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1111475).length < 2 ^ (prefixWord ++ tailWord_1111475).sum := by decide
  have hdescent : baseEnd_1111475 < baseStart_1111475 := by decide
  rcases family_descends (prefixWord ++ tailWord_1111475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1111492 : List Nat := [2, 3, 3, 2, 1, 1, 1, 2, 6]
def baseStart_1111492 : Nat := 118140960795 + 1111492 * 2 ^ 59
def prefixEnd_1111492 : Nat := 4983230072969 + 3 ^ 40 * 1111492 * 2
def baseEnd_1111492 : Nat := 253657617612120229394821

theorem tailTrace_1111492 : CollatzResearch.WordTrace tailWord_1111492 prefixEnd_1111492 253657617612120229394821 := by
  unfold tailWord_1111492
  simp only [CollatzResearch.WordTrace]
  refine ⟨20269721844630893282876365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27026295792841191043835153 20269721844630893282876365)
  ·
    refine ⟨7601145691736584981078637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20269721844630893282876365 7601145691736584981078637)
    ·
      refine ⟨2850429634401219367904489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7601145691736584981078637 2850429634401219367904489)
      ·
        refine ⟨2137822225800914525928367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2850429634401219367904489 2137822225800914525928367)
        ·
          refine ⟨3206733338701371788892551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2137822225800914525928367 3206733338701371788892551)
          ·
            refine ⟨4810100008052057683338827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3206733338701371788892551 4810100008052057683338827)
            ·
              refine ⟨7215150012078086525008241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4810100008052057683338827 7215150012078086525008241)
              ·
                refine ⟨5411362509058564893756181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7215150012078086525008241 5411362509058564893756181)
                ·
                  refine ⟨253657617612120229394821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5411362509058564893756181 253657617612120229394821)
                  ·
                    rfl

theorem cell21_1111492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 1, 2, 6].length) (baseStart_1111492 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1111492 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1111492 prefixEnd_1111492 := by exact prefixLift 1111492
  have htrace : WordTrace (prefixWord ++ tailWord_1111492) baseStart_1111492 baseEnd_1111492 := by
    simpa [prefixWord, tailWord_1111492, baseEnd_1111492] using wordTrace_append hprefix tailTrace_1111492
  have hstable : (prefixWord ++ tailWord_1111492).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1111492).length < 2 ^ (prefixWord ++ tailWord_1111492).sum := by decide
  have hdescent : baseEnd_1111492 < baseStart_1111492 := by decide
  rcases family_descends (prefixWord ++ tailWord_1111492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1111520 : List Nat := [2, 1, 1, 3, 1, 1, 2, 5, 5]
def baseStart_1111520 : Nat := 118140960795 + 1111520 * 2 ^ 59
def prefixEnd_1111520 : Nat := 4983230072969 + 3 ^ 40 * 1111520 * 2
def baseEnd_1111520 : Nat := 253664007593598402928097

theorem tailTrace_1111520 : CollatzResearch.WordTrace tailWord_1111520 prefixEnd_1111520 253664007593598402928097 := by
  unfold tailWord_1111520
  simp only [CollatzResearch.WordTrace]
  refine ⟨20270232466580173673886007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27026976622106898231848009 20270232466580173673886007)
  ·
    refine ⟨30405348699870260510829011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20270232466580173673886007 30405348699870260510829011)
    ·
      refine ⟨45608023049805390766243517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30405348699870260510829011 45608023049805390766243517)
      ·
        refine ⟨17103008643677021537341319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 45608023049805390766243517 17103008643677021537341319)
        ·
          refine ⟨25654512965515532306011979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17103008643677021537341319 25654512965515532306011979)
          ·
            refine ⟨38481769448273298459017969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25654512965515532306011979 38481769448273298459017969)
            ·
              refine ⟨28861327086204973844263477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38481769448273298459017969 28861327086204973844263477)
              ·
                refine ⟨2705749414331716297899701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 28861327086204973844263477 2705749414331716297899701)
                ·
                  refine ⟨253664007593598402928097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2705749414331716297899701 253664007593598402928097)
                  ·
                    rfl

theorem cell21_1111520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 5, 5].length) (baseStart_1111520 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1111520 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1111520 prefixEnd_1111520 := by exact prefixLift 1111520
  have htrace : WordTrace (prefixWord ++ tailWord_1111520) baseStart_1111520 baseEnd_1111520 := by
    simpa [prefixWord, tailWord_1111520, baseEnd_1111520] using wordTrace_append hprefix tailTrace_1111520
  have hstable : (prefixWord ++ tailWord_1111520).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1111520).length < 2 ^ (prefixWord ++ tailWord_1111520).sum := by decide
  have hdescent : baseEnd_1111520 < baseStart_1111520 := by decide
  rcases family_descends (prefixWord ++ tailWord_1111520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1111571 : List Nat := [1, 1, 1, 2, 1, 8, 2, 2, 3]
def baseStart_1111571 : Nat := 118140960795 + 1111571 * 2 ^ 59
def prefixEnd_1111571 : Nat := 4983230072969 + 3 ^ 40 * 1111571 * 2
def baseEnd_1111571 : Nat := 253675646488433647577993

theorem tailTrace_1111571 : CollatzResearch.WordTrace tailWord_1111571 prefixEnd_1111571 253675646488433647577993 := by
  unfold tailWord_1111571
  simp only [CollatzResearch.WordTrace]
  refine ⟨40542325055975583057878567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27028216703983722038585711 40542325055975583057878567)
  ·
    refine ⟨60813487583963374586817851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40542325055975583057878567 60813487583963374586817851)
    ·
      refine ⟨91220231375945061880226777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60813487583963374586817851 91220231375945061880226777)
      ·
        refine ⟨68415173531958796410170083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 91220231375945061880226777 68415173531958796410170083)
        ·
          refine ⟨102622760297938194615255125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68415173531958796410170083 102622760297938194615255125)
          ·
            refine ⟨1202610472241463218147521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 102622760297938194615255125 1202610472241463218147521)
            ·
              refine ⟨901957854181097413610641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1202610472241463218147521 901957854181097413610641)
              ·
                refine ⟨676468390635823060207981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 901957854181097413610641 676468390635823060207981)
                ·
                  refine ⟨253675646488433647577993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 676468390635823060207981 253675646488433647577993)
                  ·
                    rfl

theorem cell21_1111571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 8, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 8, 2, 2, 3].length) (baseStart_1111571 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1111571 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1111571 prefixEnd_1111571 := by exact prefixLift 1111571
  have htrace : WordTrace (prefixWord ++ tailWord_1111571) baseStart_1111571 baseEnd_1111571 := by
    simpa [prefixWord, tailWord_1111571, baseEnd_1111571] using wordTrace_append hprefix tailTrace_1111571
  have hstable : (prefixWord ++ tailWord_1111571).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1111571).length < 2 ^ (prefixWord ++ tailWord_1111571).sum := by decide
  have hdescent : baseEnd_1111571 < baseStart_1111571 := by decide
  rcases family_descends (prefixWord ++ tailWord_1111571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1111658 : List Nat := [3, 1, 3, 2, 1, 3, 1, 7]
def baseStart_1111658 : Nat := 118140960795 + 1111658 * 2 ^ 59
def prefixEnd_1111658 : Nat := 4983230072969 + 3 ^ 40 * 1111658 * 2
def baseEnd_1111658 : Nat := 84565167024580276542605

theorem tailTrace_1111658 : CollatzResearch.WordTrace tailWord_1111658 prefixEnd_1111658 84565167024580276542605 := by
  unfold tailWord_1111658
  simp only [CollatzResearch.WordTrace]
  refine ⟨10136374551665099229073907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27030332137773597944197085 10136374551665099229073907)
  ·
    refine ⟨15204561827497648843610861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10136374551665099229073907 15204561827497648843610861)
    ·
      refine ⟨5701710685311618316354073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15204561827497648843610861 5701710685311618316354073)
      ·
        refine ⟨4276283013983713737265555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5701710685311618316354073 4276283013983713737265555)
        ·
          refine ⟨6414424520975570605898333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4276283013983713737265555 6414424520975570605898333)
          ·
            refine ⟨2405409195365838977211875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6414424520975570605898333 2405409195365838977211875)
            ·
              refine ⟨3608113793048758465817813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2405409195365838977211875 3608113793048758465817813)
              ·
                refine ⟨84565167024580276542605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3608113793048758465817813 84565167024580276542605)
                ·
                  rfl

theorem cell21_1111658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 3, 1, 7].length) (baseStart_1111658 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1111658 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1111658 prefixEnd_1111658 := by exact prefixLift 1111658
  have htrace : WordTrace (prefixWord ++ tailWord_1111658) baseStart_1111658 baseEnd_1111658 := by
    simpa [prefixWord, tailWord_1111658, baseEnd_1111658] using wordTrace_append hprefix tailTrace_1111658
  have hstable : (prefixWord ++ tailWord_1111658).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1111658).length < 2 ^ (prefixWord ++ tailWord_1111658).sum := by decide
  have hdescent : baseEnd_1111658 < baseStart_1111658 := by decide
  rcases family_descends (prefixWord ++ tailWord_1111658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1111689 : List Nat := [1, 2, 1, 1, 4, 1, 2, 6, 3]
def baseStart_1111689 : Nat := 118140960795 + 1111689 * 2 ^ 59
def prefixEnd_1111689 : Nat := 4983230072969 + 3 ^ 40 * 1111689 * 2
def baseEnd_1111689 : Nat := 253702575696091664611085

theorem tailTrace_1111689 : CollatzResearch.WordTrace tailWord_1111689 prefixEnd_1111689 253702575696091664611085 := by
  unfold tailWord_1111689
  simp only [CollatzResearch.WordTrace]
  refine ⟨40546628869548089210674121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27031085913032059473782747 40546628869548089210674121)
  ·
    refine ⟨30409971652161066908005591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40546628869548089210674121 30409971652161066908005591)
    ·
      refine ⟨45614957478241600362008387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30409971652161066908005591 45614957478241600362008387)
      ·
        refine ⟨68422436217362400543012581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45614957478241600362008387 68422436217362400543012581)
        ·
          refine ⟨12829206790755450101814859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 68422436217362400543012581 12829206790755450101814859)
          ·
            refine ⟨19243810186133175152722289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12829206790755450101814859 19243810186133175152722289)
            ·
              refine ⟨14432857639599881364541717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19243810186133175152722289 14432857639599881364541717)
              ·
                refine ⟨676540201856244438962893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 14432857639599881364541717 676540201856244438962893)
                ·
                  refine ⟨253702575696091664611085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 676540201856244438962893 253702575696091664611085)
                  ·
                    rfl

theorem cell21_1111689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 2, 6, 3].length) (baseStart_1111689 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1111689 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1111689 prefixEnd_1111689 := by exact prefixLift 1111689
  have htrace : WordTrace (prefixWord ++ tailWord_1111689) baseStart_1111689 baseEnd_1111689 := by
    simpa [prefixWord, tailWord_1111689, baseEnd_1111689] using wordTrace_append hprefix tailTrace_1111689
  have hstable : (prefixWord ++ tailWord_1111689).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1111689).length < 2 ^ (prefixWord ++ tailWord_1111689).sum := by decide
  have hdescent : baseEnd_1111689 < baseStart_1111689 := by decide
  rcases family_descends (prefixWord ++ tailWord_1111689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1111717 : List Nat := [1, 3, 1, 2, 1, 2, 4, 7]
def baseStart_1111717 : Nat := 118140960795 + 1111717 * 2 ^ 59
def prefixEnd_1111717 : Nat := 4983230072969 + 3 ^ 40 * 1111717 * 2
def baseEnd_1111717 : Nat := 84569655225856612714787

theorem tailTrace_1111717 : CollatzResearch.WordTrace tailWord_1111717 prefixEnd_1111717 84569655225856612714787 := by
  unfold tailWord_1111717
  simp only [CollatzResearch.WordTrace]
  refine ⟨40547650113446649992693405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27031766742297766661795603 40547650113446649992693405)
  ·
    refine ⟨15205368792542493747260027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40547650113446649992693405 15205368792542493747260027)
    ·
      refine ⟨22808053188813740620890041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15205368792542493747260027 22808053188813740620890041)
      ·
        refine ⟨17106039891610305465667531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22808053188813740620890041 17106039891610305465667531)
        ·
          refine ⟨25659059837415458198501297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17106039891610305465667531 25659059837415458198501297)
          ·
            refine ⟨19244294878061593648875973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25659059837415458198501297 19244294878061593648875973)
            ·
              refine ⟨3608305289636548809164245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19244294878061593648875973 3608305289636548809164245)
              ·
                refine ⟨84569655225856612714787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3608305289636548809164245 84569655225856612714787)
                ·
                  rfl

theorem cell21_1111717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 4, 7].length) (baseStart_1111717 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1111717 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1111717 prefixEnd_1111717 := by exact prefixLift 1111717
  have htrace : WordTrace (prefixWord ++ tailWord_1111717) baseStart_1111717 baseEnd_1111717 := by
    simpa [prefixWord, tailWord_1111717, baseEnd_1111717] using wordTrace_append hprefix tailTrace_1111717
  have hstable : (prefixWord ++ tailWord_1111717).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1111717).length < 2 ^ (prefixWord ++ tailWord_1111717).sum := by decide
  have hdescent : baseEnd_1111717 < baseStart_1111717 := by decide
  rcases family_descends (prefixWord ++ tailWord_1111717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1111793 : List Nat := [1, 2, 2, 2, 2, 4, 8]
def baseStart_1111793 : Nat := 118140960795 + 1111793 * 2 ^ 59
def prefixEnd_1111793 : Nat := 4983230072969 + 3 ^ 40 * 1111793 * 2
def baseEnd_1111793 : Nat := 28191812212556732764171

theorem tailTrace_1111793 : CollatzResearch.WordTrace tailWord_1111793 prefixEnd_1111793 28191812212556732764171 := by
  unfold tailWord_1111793
  simp only [CollatzResearch.WordTrace]
  refine ⟨40550422061171314972460033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27033614707447543314973355 40550422061171314972460033)
  ·
    refine ⟨30412816545878486229345025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40550422061171314972460033 30412816545878486229345025)
    ·
      refine ⟨22809612409408864672008769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30412816545878486229345025 22809612409408864672008769)
      ·
        refine ⟨17107209307056648504006577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22809612409408864672008769 17107209307056648504006577)
        ·
          refine ⟨12830406980292486378004933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17107209307056648504006577 12830406980292486378004933)
          ·
            refine ⟨2405701308804841195875925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12830406980292486378004933 2405701308804841195875925)
            ·
              refine ⟨28191812212556732764171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2405701308804841195875925 28191812212556732764171)
              ·
                rfl

theorem cell21_1111793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 4, 8].length) (baseStart_1111793 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1111793 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1111793 prefixEnd_1111793 := by exact prefixLift 1111793
  have htrace : WordTrace (prefixWord ++ tailWord_1111793) baseStart_1111793 baseEnd_1111793 := by
    simpa [prefixWord, tailWord_1111793, baseEnd_1111793] using wordTrace_append hprefix tailTrace_1111793
  have hstable : (prefixWord ++ tailWord_1111793).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1111793).length < 2 ^ (prefixWord ++ tailWord_1111793).sum := by decide
  have hdescent : baseEnd_1111793 < baseStart_1111793 := by decide
  rcases family_descends (prefixWord ++ tailWord_1111793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1111810 : List Nat := [3, 4, 1, 1, 1, 1, 2, 8]
def baseStart_1111810 : Nat := 118140960795 + 1111810 * 2 ^ 59
def prefixEnd_1111810 : Nat := 4983230072969 + 3 ^ 40 * 1111810 * 2
def baseEnd_1111810 : Nat := 84576729848207447698057

theorem tailTrace_1111810 : CollatzResearch.WordTrace tailWord_1111810 prefixEnd_1111810 84576729848207447698057 := by
  unfold tailWord_1111810
  simp only [CollatzResearch.WordTrace]
  refine ⟨10137760525527431718957221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27034028068073151250552589 10137760525527431718957221)
  ·
    refine ⟨1900830098536393447304479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10137760525527431718957221 1900830098536393447304479)
    ·
      refine ⟨2851245147804590170956719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1900830098536393447304479 2851245147804590170956719)
      ·
        refine ⟨4276867721706885256435079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2851245147804590170956719 4276867721706885256435079)
        ·
          refine ⟨6415301582560327884652619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4276867721706885256435079 6415301582560327884652619)
          ·
            refine ⟨9622952373840491826978929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6415301582560327884652619 9622952373840491826978929)
            ·
              refine ⟨7217214280380368870234197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9622952373840491826978929 7217214280380368870234197)
              ·
                refine ⟨84576729848207447698057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7217214280380368870234197 84576729848207447698057)
                ·
                  rfl

theorem cell21_1111810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 2, 8].length) (baseStart_1111810 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1111810 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1111810 prefixEnd_1111810 := by exact prefixLift 1111810
  have htrace : WordTrace (prefixWord ++ tailWord_1111810) baseStart_1111810 baseEnd_1111810 := by
    simpa [prefixWord, tailWord_1111810, baseEnd_1111810] using wordTrace_append hprefix tailTrace_1111810
  have hstable : (prefixWord ++ tailWord_1111810).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1111810).length < 2 ^ (prefixWord ++ tailWord_1111810).sum := by decide
  have hdescent : baseEnd_1111810 < baseStart_1111810 := by decide
  rcases family_descends (prefixWord ++ tailWord_1111810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1111934 : List Nat := [4, 2, 3, 1, 1, 2, 1, 2, 5]
def baseStart_1111934 : Nat := 118140960795 + 1111934 * 2 ^ 59
def prefixEnd_1111934 : Nat := 4983230072969 + 3 ^ 40 * 1111934 * 2
def baseEnd_1111934 : Nat := 253758488034025683027251

theorem tailTrace_1111934 : CollatzResearch.WordTrace tailWord_1111934 prefixEnd_1111934 253758488034025683027251 := by
  unfold tailWord_1111934
  simp only [CollatzResearch.WordTrace]
  refine ⟨5069445594207562006667857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 27037043169106997368895237 5069445594207562006667857)
  ·
    refine ⟨3802084195655671505000893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5069445594207562006667857 3802084195655671505000893)
    ·
      refine ⟨1425781573370876814375335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3802084195655671505000893 1425781573370876814375335)
      ·
        refine ⟨2138672360056315221563003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1425781573370876814375335 2138672360056315221563003)
        ·
          refine ⟨3208008540084472832344505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2138672360056315221563003 3208008540084472832344505)
          ·
            refine ⟨2406006405063354624258379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3208008540084472832344505 2406006405063354624258379)
            ·
              refine ⟨3609009607595031936387569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2406006405063354624258379 3609009607595031936387569)
              ·
                refine ⟨2706757205696273952290677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3609009607595031936387569 2706757205696273952290677)
                ·
                  refine ⟨253758488034025683027251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2706757205696273952290677 253758488034025683027251)
                  ·
                    rfl

theorem cell21_1111934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 2, 1, 2, 5].length) (baseStart_1111934 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1111934 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1111934 prefixEnd_1111934 := by exact prefixLift 1111934
  have htrace : WordTrace (prefixWord ++ tailWord_1111934) baseStart_1111934 baseEnd_1111934 := by
    simpa [prefixWord, tailWord_1111934, baseEnd_1111934] using wordTrace_append hprefix tailTrace_1111934
  have hstable : (prefixWord ++ tailWord_1111934).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1111934).length < 2 ^ (prefixWord ++ tailWord_1111934).sum := by decide
  have hdescent : baseEnd_1111934 < baseStart_1111934 := by decide
  rcases family_descends (prefixWord ++ tailWord_1111934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1111996 : List Nat := [2, 2, 2, 5, 1, 2, 2, 5]
def baseStart_1111996 : Nat := 118140960795 + 1111996 * 2 ^ 59
def prefixEnd_1111996 : Nat := 4983230072969 + 3 ^ 40 * 1111996 * 2
def baseEnd_1111996 : Nat := 84590879092909117664597

theorem tailTrace_1111996 : CollatzResearch.WordTrace tailWord_1111996 prefixEnd_1111996 84590879092909117664597 := by
  unfold tailWord_1111996
  simp only [CollatzResearch.WordTrace]
  refine ⟨20278913039717940321049921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27038550719623920428066561 20278913039717940321049921)
  ·
    refine ⟨15209184779788455240787441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20278913039717940321049921 15209184779788455240787441)
    ·
      refine ⟨11406888584841341430590581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15209184779788455240787441 11406888584841341430590581)
      ·
        refine ⟨1069395804828875759117867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 11406888584841341430590581 1069395804828875759117867)
        ·
          refine ⟨1604093707243313638676801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1069395804828875759117867 1604093707243313638676801)
          ·
            refine ⟨1203070280432485229007601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1604093707243313638676801 1203070280432485229007601)
            ·
              refine ⟨902302710324363921755701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1203070280432485229007601 902302710324363921755701)
              ·
                refine ⟨84590879092909117664597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 902302710324363921755701 84590879092909117664597)
                ·
                  rfl

theorem cell21_1111996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 2, 2, 5].length) (baseStart_1111996 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1111996 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1111996 prefixEnd_1111996 := by exact prefixLift 1111996
  have htrace : WordTrace (prefixWord ++ tailWord_1111996) baseStart_1111996 baseEnd_1111996 := by
    simpa [prefixWord, tailWord_1111996, baseEnd_1111996] using wordTrace_append hprefix tailTrace_1111996
  have hstable : (prefixWord ++ tailWord_1111996).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1111996).length < 2 ^ (prefixWord ++ tailWord_1111996).sum := by decide
  have hdescent : baseEnd_1111996 < baseStart_1111996 := by decide
  rcases family_descends (prefixWord ++ tailWord_1111996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1112021 : List Nat := [1, 3, 2, 3, 2, 1, 9]
def baseStart_1112021 : Nat := 118140960795 + 1112021 * 2 ^ 59
def prefixEnd_1112021 : Nat := 4983230072969 + 3 ^ 40 * 1112021 * 2
def baseEnd_1112021 : Nat := 28197593624370318341897

theorem tailTrace_1112021 : CollatzResearch.WordTrace tailWord_1112021 prefixEnd_1112021 28197593624370318341897 := by
  unfold tailWord_1112021
  simp only [CollatzResearch.WordTrace]
  refine ⟨40558737904345309911759917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27039158602896873274506611 40558737904345309911759917)
  ·
    refine ⟨15209526714129491216909969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40558737904345309911759917 15209526714129491216909969)
    ·
      refine ⟨11407145035597118412682477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15209526714129491216909969 11407145035597118412682477)
      ·
        refine ⟨4277679388348919404755929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11407145035597118412682477 4277679388348919404755929)
        ·
          refine ⟨3208259541261689553566947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4277679388348919404755929 3208259541261689553566947)
          ·
            refine ⟨4812389311892534330350421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3208259541261689553566947 4812389311892534330350421)
            ·
              refine ⟨28197593624370318341897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 4812389311892534330350421 28197593624370318341897)
              ·
                rfl

theorem cell21_1112021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 9].length) (baseStart_1112021 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1112021 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1112021 prefixEnd_1112021 := by exact prefixLift 1112021
  have htrace : WordTrace (prefixWord ++ tailWord_1112021) baseStart_1112021 baseEnd_1112021 := by
    simpa [prefixWord, tailWord_1112021, baseEnd_1112021] using wordTrace_append hprefix tailTrace_1112021
  have hstable : (prefixWord ++ tailWord_1112021).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1112021).length < 2 ^ (prefixWord ++ tailWord_1112021).sum := by decide
  have hdescent : baseEnd_1112021 < baseStart_1112021 := by decide
  rcases family_descends (prefixWord ++ tailWord_1112021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1112114 : List Nat := [3, 2, 1, 1, 2, 4, 3, 5]
def baseStart_1112114 : Nat := 118140960795 + 1112114 * 2 ^ 59
def prefixEnd_1112114 : Nat := 4983230072969 + 3 ^ 40 * 1112114 * 2
def baseEnd_1112114 : Nat := 84599855495461790008961

theorem tailTrace_1112114 : CollatzResearch.WordTrace tailWord_1112114 prefixEnd_1112114 84599855495461790008961 := by
  unfold tailWord_1112114
  simp only [CollatzResearch.WordTrace]
  refine ⟨10140532473252096698723849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27041419928672257863263597 10140532473252096698723849)
  ·
    refine ⟨7605399354939072524042887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10140532473252096698723849 7605399354939072524042887)
    ·
      refine ⟨11408099032408608786064331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7605399354939072524042887 11408099032408608786064331)
      ·
        refine ⟨17112148548612913179096497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11408099032408608786064331 17112148548612913179096497)
        ·
          refine ⟨12834111411459684884322373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17112148548612913179096497 12834111411459684884322373)
          ·
            refine ⟨2406395889648690915810445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12834111411459684884322373 2406395889648690915810445)
            ·
              refine ⟨902398458618259093428917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2406395889648690915810445 902398458618259093428917)
              ·
                refine ⟨84599855495461790008961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 902398458618259093428917 84599855495461790008961)
                ·
                  rfl

theorem cell21_1112114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 4, 3, 5].length) (baseStart_1112114 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1112114 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1112114 prefixEnd_1112114 := by exact prefixLift 1112114
  have htrace : WordTrace (prefixWord ++ tailWord_1112114) baseStart_1112114 baseEnd_1112114 := by
    simpa [prefixWord, tailWord_1112114, baseEnd_1112114] using wordTrace_append hprefix tailTrace_1112114
  have hstable : (prefixWord ++ tailWord_1112114).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1112114).length < 2 ^ (prefixWord ++ tailWord_1112114).sum := by decide
  have hdescent : baseEnd_1112114 < baseStart_1112114 := by decide
  rcases family_descends (prefixWord ++ tailWord_1112114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1112173 : List Nat := [1, 5, 1, 1, 2, 1, 3, 7]
def baseStart_1112173 : Nat := 118140960795 + 1112173 * 2 ^ 59
def prefixEnd_1112173 : Nat := 4983230072969 + 3 ^ 40 * 1112173 * 2
def baseEnd_1112173 : Nat := 84604343696738126181143

theorem tailTrace_1112173 : CollatzResearch.WordTrace tailWord_1112173 prefixEnd_1112173 84604343696738126181143 := by
  unfold tailWord_1112173
  simp only [CollatzResearch.WordTrace]
  refine ⟨40564281799794639871293173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27042854533196426580862115 40564281799794639871293173)
  ·
    refine ⟨3802901418730747487933735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 40564281799794639871293173 3802901418730747487933735)
    ·
      refine ⟨5704352128096121231900603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3802901418730747487933735 5704352128096121231900603)
      ·
        refine ⟨8556528192144181847850905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5704352128096121231900603 8556528192144181847850905)
        ·
          refine ⟨6417396144108136385888179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8556528192144181847850905 6417396144108136385888179)
          ·
            refine ⟨9626094216162204578832269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6417396144108136385888179 9626094216162204578832269)
            ·
              refine ⟨3609785331060826717062101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9626094216162204578832269 3609785331060826717062101)
              ·
                refine ⟨84604343696738126181143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3609785331060826717062101 84604343696738126181143)
                ·
                  rfl

theorem cell21_1112173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 3, 7].length) (baseStart_1112173 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1112173 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1112173 prefixEnd_1112173 := by exact prefixLift 1112173
  have htrace : WordTrace (prefixWord ++ tailWord_1112173) baseStart_1112173 baseEnd_1112173 := by
    simpa [prefixWord, tailWord_1112173, baseEnd_1112173] using wordTrace_append hprefix tailTrace_1112173
  have hstable : (prefixWord ++ tailWord_1112173).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1112173).length < 2 ^ (prefixWord ++ tailWord_1112173).sum := by decide
  have hdescent : baseEnd_1112173 < baseStart_1112173 := by decide
  rcases family_descends (prefixWord ++ tailWord_1112173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1112252 : List Nat := [2, 2, 2, 3, 3, 1, 2, 2, 4]
def baseStart_1112252 : Nat := 118140960795 + 1112252 * 2 ^ 59
def prefixEnd_1112252 : Nat := 4983230072969 + 3 ^ 40 * 1112252 * 2
def baseEnd_1112252 : Nat := 253831059966527796726601

theorem tailTrace_1112252 : CollatzResearch.WordTrace tailWord_1112252 prefixEnd_1112252 253831059966527796726601 := by
  unfold tailWord_1112252
  simp only [CollatzResearch.WordTrace]
  refine ⟨20283581583254218181709505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27044775444338957575612673 20283581583254218181709505)
  ·
    refine ⟨15212686187440663636282129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20283581583254218181709505 15212686187440663636282129)
    ·
      refine ⟨11409514640580497727211597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15212686187440663636282129 11409514640580497727211597)
      ·
        refine ⟨4278567990217686647704349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11409514640580497727211597 4278567990217686647704349)
        ·
          refine ⟨1604462996331632492889131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4278567990217686647704349 1604462996331632492889131)
          ·
            refine ⟨2406694494497448739333697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1604462996331632492889131 2406694494497448739333697)
            ·
              refine ⟨1805020870873086554500273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2406694494497448739333697 1805020870873086554500273)
              ·
                refine ⟨1353765653154814915875205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1805020870873086554500273 1353765653154814915875205)
                ·
                  refine ⟨253831059966527796726601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1353765653154814915875205 253831059966527796726601)
                  ·
                    rfl

theorem cell21_1112252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 1, 2, 2, 4].length) (baseStart_1112252 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1112252 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1112252 prefixEnd_1112252 := by exact prefixLift 1112252
  have htrace : WordTrace (prefixWord ++ tailWord_1112252) baseStart_1112252 baseEnd_1112252 := by
    simpa [prefixWord, tailWord_1112252, baseEnd_1112252] using wordTrace_append hprefix tailTrace_1112252
  have hstable : (prefixWord ++ tailWord_1112252).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1112252).length < 2 ^ (prefixWord ++ tailWord_1112252).sum := by decide
  have hdescent : baseEnd_1112252 < baseStart_1112252 := by decide
  rcases family_descends (prefixWord ++ tailWord_1112252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1112280 : List Nat := [2, 1, 2, 2, 4, 2, 1, 2, 5]
def baseStart_1112280 : Nat := 118140960795 + 1112280 * 2 ^ 59
def prefixEnd_1112280 : Nat := 4983230072969 + 3 ^ 40 * 1112280 * 2
def baseEnd_1112280 : Nat := 253837449948005970259877

theorem tailTrace_1112280 : CollatzResearch.WordTrace tailWord_1112280 prefixEnd_1112280 253837449948005970259877 := by
  unfold tailWord_1112280
  simp only [CollatzResearch.WordTrace]
  refine ⟨20284092205203498572719147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27045456273604664763625529 20284092205203498572719147)
  ·
    refine ⟨30426138307805247859078721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20284092205203498572719147 30426138307805247859078721)
    ·
      refine ⟨22819603730853935894309041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30426138307805247859078721 22819603730853935894309041)
      ·
        refine ⟨17114702798140451920731781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22819603730853935894309041 17114702798140451920731781)
        ·
          refine ⟨3209006774651334735137209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17114702798140451920731781 3209006774651334735137209)
          ·
            refine ⟨2406755080988501051352907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3209006774651334735137209 2406755080988501051352907)
            ·
              refine ⟨3610132621482751577029361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2406755080988501051352907 3610132621482751577029361)
              ·
                refine ⟨2707599466112063682772021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3610132621482751577029361 2707599466112063682772021)
                ·
                  refine ⟨253837449948005970259877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2707599466112063682772021 253837449948005970259877)
                  ·
                    rfl

theorem cell21_1112280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 2, 1, 2, 5].length) (baseStart_1112280 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1112280 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1112280 prefixEnd_1112280 := by exact prefixLift 1112280
  have htrace : WordTrace (prefixWord ++ tailWord_1112280) baseStart_1112280 baseEnd_1112280 := by
    simpa [prefixWord, tailWord_1112280, baseEnd_1112280] using wordTrace_append hprefix tailTrace_1112280
  have hstable : (prefixWord ++ tailWord_1112280).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1112280).length < 2 ^ (prefixWord ++ tailWord_1112280).sum := by decide
  have hdescent : baseEnd_1112280 < baseStart_1112280 := by decide
  rcases family_descends (prefixWord ++ tailWord_1112280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1112328 : List Nat := [2, 1, 3, 2, 3, 2, 3, 1, 4]
def baseStart_1112328 : Nat := 118140960795 + 1112328 * 2 ^ 59
def prefixEnd_1112328 : Nat := 4983230072969 + 3 ^ 40 * 1112328 * 2
def baseEnd_1112328 : Nat := 253848404201968553459779

theorem tailTrace_1112328 : CollatzResearch.WordTrace tailWord_1112328 prefixEnd_1112328 253848404201968553459779 := by
  unfold tailWord_1112328
  simp only [CollatzResearch.WordTrace]
  refine ⟨20284967557116550671592819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27046623409488734228790425 20284967557116550671592819)
  ·
    refine ⟨30427451335674826007389229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20284967557116550671592819 30427451335674826007389229)
    ·
      refine ⟨11410294250878059752770961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30427451335674826007389229 11410294250878059752770961)
      ·
        refine ⟨8557720688158544814578221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11410294250878059752770961 8557720688158544814578221)
        ·
          refine ⟨3209145258059454305466833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8557720688158544814578221 3209145258059454305466833)
          ·
            refine ⟨2406858943544590729100125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3209145258059454305466833 2406858943544590729100125)
            ·
              refine ⟨902572103829221523412547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2406858943544590729100125 902572103829221523412547)
              ·
                refine ⟨1353858155743832285118821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 902572103829221523412547 1353858155743832285118821)
                ·
                  refine ⟨253848404201968553459779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1353858155743832285118821 253848404201968553459779)
                  ·
                    rfl

theorem cell21_1112328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 2, 3, 1, 4].length) (baseStart_1112328 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1112328 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1112328 prefixEnd_1112328 := by exact prefixLift 1112328
  have htrace : WordTrace (prefixWord ++ tailWord_1112328) baseStart_1112328 baseEnd_1112328 := by
    simpa [prefixWord, tailWord_1112328, baseEnd_1112328] using wordTrace_append hprefix tailTrace_1112328
  have hstable : (prefixWord ++ tailWord_1112328).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1112328).length < 2 ^ (prefixWord ++ tailWord_1112328).sum := by decide
  have hdescent : baseEnd_1112328 < baseStart_1112328 := by decide
  rcases family_descends (prefixWord ++ tailWord_1112328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1112387 : List Nat := [1, 1, 1, 3, 1, 3, 6, 1, 4]
def baseStart_1112387 : Nat := 118140960795 + 1112387 * 2 ^ 59
def prefixEnd_1112387 : Nat := 4983230072969 + 3 ^ 40 * 1112387 * 2
def baseEnd_1112387 : Nat := 253861868805797561976325

theorem tailTrace_1112387 : CollatzResearch.WordTrace tailWord_1112387 prefixEnd_1112387 253861868805797561976325 := by
  unfold tailWord_1112387
  simp only [CollatzResearch.WordTrace]
  refine ⟨40572087021019354419583415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27048058014012902946388943 40572087021019354419583415)
  ·
    refine ⟨60858130531529031629375123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40572087021019354419583415 60858130531529031629375123)
    ·
      refine ⟨91287195797293547444062685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60858130531529031629375123 91287195797293547444062685)
      ·
        refine ⟨34232698423985080291523507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 91287195797293547444062685 34232698423985080291523507)
        ·
          refine ⟨51349047635977620437285261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34232698423985080291523507 51349047635977620437285261)
          ·
            refine ⟨19255892863491607663981973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 51349047635977620437285261 19255892863491607663981973)
            ·
              refine ⟨902619977976169109249155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 19255892863491607663981973 902619977976169109249155)
              ·
                refine ⟨1353929966964253663873733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 902619977976169109249155 1353929966964253663873733)
                ·
                  refine ⟨253861868805797561976325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1353929966964253663873733 253861868805797561976325)
                  ·
                    rfl

theorem cell21_1112387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 6, 1, 4].length) (baseStart_1112387 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1112387 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1112387 prefixEnd_1112387 := by exact prefixLift 1112387
  have htrace : WordTrace (prefixWord ++ tailWord_1112387) baseStart_1112387 baseEnd_1112387 := by
    simpa [prefixWord, tailWord_1112387, baseEnd_1112387] using wordTrace_append hprefix tailTrace_1112387
  have hstable : (prefixWord ++ tailWord_1112387).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1112387).length < 2 ^ (prefixWord ++ tailWord_1112387).sum := by decide
  have hdescent : baseEnd_1112387 < baseStart_1112387 := by decide
  rcases family_descends (prefixWord ++ tailWord_1112387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1112477 : List Nat := [1, 4, 2, 1, 4, 1, 8]
def baseStart_1112477 : Nat := 118140960795 + 1112477 * 2 ^ 59
def prefixEnd_1112477 : Nat := 4983230072969 + 3 ^ 40 * 1112477 * 2
def baseEnd_1112477 : Nat := 28209156447997489497349

theorem tailTrace_1112477 : CollatzResearch.WordTrace tailWord_1112477 prefixEnd_1112477 28209156447997489497349 := by
  unfold tailWord_1112477
  simp only [CollatzResearch.WordTrace]
  refine ⟨40575369590693299790359685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27050246393795533193573123 40575369590693299790359685)
  ·
    refine ⟨7607881798254993710692441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 40575369590693299790359685 7607881798254993710692441)
    ·
      refine ⟨5705911348691245283019331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7607881798254993710692441 5705911348691245283019331)
      ·
        refine ⟨8558867023036867924528997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5705911348691245283019331 8558867023036867924528997)
        ·
          refine ⟨1604787566819412735849187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8558867023036867924528997 1604787566819412735849187)
          ·
            refine ⟨2407181350229119103773781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1604787566819412735849187 2407181350229119103773781)
            ·
              refine ⟨28209156447997489497349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2407181350229119103773781 28209156447997489497349)
              ·
                rfl

theorem cell21_1112477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 1, 8].length) (baseStart_1112477 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1112477 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1112477 prefixEnd_1112477 := by exact prefixLift 1112477
  have htrace : WordTrace (prefixWord ++ tailWord_1112477) baseStart_1112477 baseEnd_1112477 := by
    simpa [prefixWord, tailWord_1112477, baseEnd_1112477] using wordTrace_append hprefix tailTrace_1112477
  have hstable : (prefixWord ++ tailWord_1112477).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1112477).length < 2 ^ (prefixWord ++ tailWord_1112477).sum := by decide
  have hdescent : baseEnd_1112477 < baseStart_1112477 := by decide
  rcases family_descends (prefixWord ++ tailWord_1112477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1112508 : List Nat := [2, 2, 2, 4, 1, 1, 2, 2, 5]
def baseStart_1112508 : Nat := 118140960795 + 1112508 * 2 ^ 59
def prefixEnd_1112508 : Nat := 4983230072969 + 3 ^ 40 * 1112508 * 2
def baseEnd_1112508 : Nat := 253889482654328240459411

theorem tailTrace_1112508 : CollatzResearch.WordTrace tailWord_1112508 prefixEnd_1112508 253889482654328240459411 := by
  unfold tailWord_1112508
  simp only [CollatzResearch.WordTrace]
  refine ⟨20288250126790496042369089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27051000169053994723158785 20288250126790496042369089)
  ·
    refine ⟨15216187595092872031776817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20288250126790496042369089 15216187595092872031776817)
    ·
      refine ⟨11412140696319654023832613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15216187595092872031776817 11412140696319654023832613)
      ·
        refine ⟨2139776380559935129468615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11412140696319654023832613 2139776380559935129468615)
        ·
          refine ⟨3209664570839902694202923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2139776380559935129468615 3209664570839902694202923)
          ·
            refine ⟨4814496856259854041304385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3209664570839902694202923 4814496856259854041304385)
            ·
              refine ⟨3610872642194890530978289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4814496856259854041304385 3610872642194890530978289)
              ·
                refine ⟨2708154481646167898233717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3610872642194890530978289 2708154481646167898233717)
                ·
                  refine ⟨253889482654328240459411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2708154481646167898233717 253889482654328240459411)
                  ·
                    rfl

theorem cell21_1112508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 2, 2, 5].length) (baseStart_1112508 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1112508 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1112508 prefixEnd_1112508 := by exact prefixLift 1112508
  have htrace : WordTrace (prefixWord ++ tailWord_1112508) baseStart_1112508 baseEnd_1112508 := by
    simpa [prefixWord, tailWord_1112508, baseEnd_1112508] using wordTrace_append hprefix tailTrace_1112508
  have hstable : (prefixWord ++ tailWord_1112508).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1112508).length < 2 ^ (prefixWord ++ tailWord_1112508).sum := by decide
  have hdescent : baseEnd_1112508 < baseStart_1112508 := by decide
  rcases family_descends (prefixWord ++ tailWord_1112508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1112581 : List Nat := [1, 3, 1, 1, 2, 2, 2, 1, 8]
def baseStart_1112581 : Nat := 118140960795 + 1112581 * 2 ^ 59
def prefixEnd_1112581 : Nat := 4983230072969 + 3 ^ 40 * 1112581 * 2
def baseEnd_1112581 : Nat := 253906142248896335742595

theorem tailTrace_1112581 : CollatzResearch.WordTrace tailWord_1112581 prefixEnd_1112581 253906142248896335742595 := by
  unfold tailWord_1112581
  simp only [CollatzResearch.WordTrace]
  refine ⟨40579162782316525552145597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27052775188211017034763731 40579162782316525552145597)
  ·
    refine ⟨15217186043368697082054599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40579162782316525552145597 15217186043368697082054599)
    ·
      refine ⟨22825779065053045623081899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15217186043368697082054599 22825779065053045623081899)
      ·
        refine ⟨34238668597579568434622849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22825779065053045623081899 34238668597579568434622849)
        ·
          refine ⟨25679001448184676325967137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34238668597579568434622849 25679001448184676325967137)
          ·
            refine ⟨19259251086138507244475353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25679001448184676325967137 19259251086138507244475353)
            ·
              refine ⟨14444438314603880433356515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19259251086138507244475353 14444438314603880433356515)
              ·
                refine ⟨21666657471905820650034773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14444438314603880433356515 21666657471905820650034773)
                ·
                  refine ⟨253906142248896335742595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 21666657471905820650034773 253906142248896335742595)
                  ·
                    rfl

theorem cell21_1112581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 2, 1, 8].length) (baseStart_1112581 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1112581 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1112581 prefixEnd_1112581 := by exact prefixLift 1112581
  have htrace : WordTrace (prefixWord ++ tailWord_1112581) baseStart_1112581 baseEnd_1112581 := by
    simpa [prefixWord, tailWord_1112581, baseEnd_1112581] using wordTrace_append hprefix tailTrace_1112581
  have hstable : (prefixWord ++ tailWord_1112581).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1112581).length < 2 ^ (prefixWord ++ tailWord_1112581).sum := by decide
  have hdescent : baseEnd_1112581 < baseStart_1112581 := by decide
  rcases family_descends (prefixWord ++ tailWord_1112581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1112584 : List Nat := [2, 1, 3, 2, 1, 1, 1, 7, 3]
def baseStart_1112584 : Nat := 118140960795 + 1112584 * 2 ^ 59
def prefixEnd_1112584 : Nat := 4983230072969 + 3 ^ 40 * 1112584 * 2
def baseEnd_1112584 : Nat := 253906826889768997192589

theorem tailTrace_1112584 : CollatzResearch.WordTrace tailWord_1112584 prefixEnd_1112584 253906826889768997192589 := by
  unfold tailWord_1112584
  simp only [CollatzResearch.WordTrace]
  refine ⟨20289636100652828532252403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27052848134203771376336537 20289636100652828532252403)
  ·
    refine ⟨30434454150979242798378605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20289636100652828532252403 30434454150979242798378605)
    ·
      refine ⟨11412920306617216049391977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30434454150979242798378605 11412920306617216049391977)
      ·
        refine ⟨8559690229962912037043983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11412920306617216049391977 8559690229962912037043983)
        ·
          refine ⟨12839535344944368055565975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8559690229962912037043983 12839535344944368055565975)
          ·
            refine ⟨19259303017416552083348963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12839535344944368055565975 19259303017416552083348963)
            ·
              refine ⟨28888954526124828125023445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19259303017416552083348963 28888954526124828125023445)
              ·
                refine ⟨677084871706050659180237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 28888954526124828125023445 677084871706050659180237)
                ·
                  refine ⟨253906826889768997192589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 677084871706050659180237 253906826889768997192589)
                  ·
                    rfl

theorem cell21_1112584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 7, 3].length) (baseStart_1112584 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1112584 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1112584 prefixEnd_1112584 := by exact prefixLift 1112584
  have htrace : WordTrace (prefixWord ++ tailWord_1112584) baseStart_1112584 baseEnd_1112584 := by
    simpa [prefixWord, tailWord_1112584, baseEnd_1112584] using wordTrace_append hprefix tailTrace_1112584
  have hstable : (prefixWord ++ tailWord_1112584).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1112584).length < 2 ^ (prefixWord ++ tailWord_1112584).sum := by decide
  have hdescent : baseEnd_1112584 < baseStart_1112584 := by decide
  rcases family_descends (prefixWord ++ tailWord_1112584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1112629 : List Nat := [1, 3, 3, 1, 1, 2, 5, 5]
def baseStart_1112629 : Nat := 118140960795 + 1112629 * 2 ^ 59
def prefixEnd_1112629 : Nat := 4983230072969 + 3 ^ 40 * 1112629 * 2
def baseEnd_1112629 : Nat := 84639032167619639647499

theorem tailTrace_1112629 : CollatzResearch.WordTrace tailWord_1112629 prefixEnd_1112629 84639032167619639647499 := by
  unfold tailWord_1112629
  simp only [CollatzResearch.WordTrace]
  refine ⟨40580913486142629749892941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27053942324095086499928627 40580913486142629749892941)
  ·
    refine ⟨15217842557303486156209853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40580913486142629749892941 15217842557303486156209853)
    ·
      refine ⟨5706690958988807308578695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15217842557303486156209853 5706690958988807308578695)
      ·
        refine ⟨8560036438483210962868043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5706690958988807308578695 8560036438483210962868043)
        ·
          refine ⟨12840054657724816444302065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8560036438483210962868043 12840054657724816444302065)
          ·
            refine ⟨9630040993293612333226549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12840054657724816444302065 9630040993293612333226549)
            ·
              refine ⟨902816343121276156239989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 9630040993293612333226549 902816343121276156239989)
              ·
                refine ⟨84639032167619639647499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 902816343121276156239989 84639032167619639647499)
                ·
                  rfl

theorem cell21_1112629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 5, 5].length) (baseStart_1112629 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1112629 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1112629 prefixEnd_1112629 := by exact prefixLift 1112629
  have htrace : WordTrace (prefixWord ++ tailWord_1112629) baseStart_1112629 baseEnd_1112629 := by
    simpa [prefixWord, tailWord_1112629, baseEnd_1112629] using wordTrace_append hprefix tailTrace_1112629
  have hstable : (prefixWord ++ tailWord_1112629).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1112629).length < 2 ^ (prefixWord ++ tailWord_1112629).sum := by decide
  have hdescent : baseEnd_1112629 < baseStart_1112629 := by decide
  rcases family_descends (prefixWord ++ tailWord_1112629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1112646 : List Nat := [6, 1, 1, 1, 2, 2, 8]
def baseStart_1112646 : Nat := 118140960795 + 1112646 * 2 ^ 59
def prefixEnd_1112646 : Nat := 4983230072969 + 3 ^ 40 * 1112646 * 2
def baseEnd_1112646 : Nat := 28213441792718963017681

theorem tailTrace_1112646 : CollatzResearch.WordTrace tailWord_1112646 prefixEnd_1112646 28213441792718963017681 := by
  unfold tailWord_1112646
  simp only [CollatzResearch.WordTrace]
  refine ⟨1268172922721282551664431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 27054355684720694435507861 1268172922721282551664431)
  ·
    refine ⟨1902259384081923827496647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1268172922721282551664431 1902259384081923827496647)
    ·
      refine ⟨2853389076122885741244971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1902259384081923827496647 2853389076122885741244971)
      ·
        refine ⟨4280083614184328611867457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2853389076122885741244971 4280083614184328611867457)
        ·
          refine ⟨3210062710638246458900593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4280083614184328611867457 3210062710638246458900593)
          ·
            refine ⟨2407547032978684844175445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3210062710638246458900593 2407547032978684844175445)
            ·
              refine ⟨28213441792718963017681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2407547032978684844175445 28213441792718963017681)
              ·
                rfl

theorem cell21_1112646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 2, 8].length) (baseStart_1112646 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1112646 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1112646 prefixEnd_1112646 := by exact prefixLift 1112646
  have htrace : WordTrace (prefixWord ++ tailWord_1112646) baseStart_1112646 baseEnd_1112646 := by
    simpa [prefixWord, tailWord_1112646, baseEnd_1112646] using wordTrace_append hprefix tailTrace_1112646
  have hstable : (prefixWord ++ tailWord_1112646).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1112646).length < 2 ^ (prefixWord ++ tailWord_1112646).sum := by decide
  have hdescent : baseEnd_1112646 < baseStart_1112646 := by decide
  rcases family_descends (prefixWord ++ tailWord_1112646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1112660 : List Nat := [2, 4, 1, 1, 1, 4, 2, 1, 5]
def baseStart_1112660 : Nat := 118140960795 + 1112660 * 2 ^ 59
def prefixEnd_1112660 : Nat := 4983230072969 + 3 ^ 40 * 1112660 * 2
def baseEnd_1112660 : Nat := 253924171125209753925767

theorem tailTrace_1112660 : CollatzResearch.WordTrace tailWord_1112660 prefixEnd_1112660 253924171125209753925767 := by
  unfold tailWord_1112660
  simp only [CollatzResearch.WordTrace]
  refine ⟨20291022074515161022135717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27054696099353548029514289 20291022074515161022135717)
  ·
    refine ⟨3804566638971592691650447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 20291022074515161022135717 3804566638971592691650447)
    ·
      refine ⟨5706849958457389037475671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3804566638971592691650447 5706849958457389037475671)
      ·
        refine ⟨8560274937686083556213507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5706849958457389037475671 8560274937686083556213507)
        ·
          refine ⟨12840412406529125334320261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8560274937686083556213507 12840412406529125334320261)
          ·
            refine ⟨2407577326224211000185049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12840412406529125334320261 2407577326224211000185049)
            ·
              refine ⟨1805682994668158250138787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2407577326224211000185049 1805682994668158250138787)
              ·
                refine ⟨2708524492002237375208181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1805682994668158250138787 2708524492002237375208181)
                ·
                  refine ⟨253924171125209753925767, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2708524492002237375208181 253924171125209753925767)
                  ·
                    rfl

theorem cell21_1112660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 4, 2, 1, 5].length) (baseStart_1112660 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1112660 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1112660 prefixEnd_1112660 := by exact prefixLift 1112660
  have htrace : WordTrace (prefixWord ++ tailWord_1112660) baseStart_1112660 baseEnd_1112660 := by
    simpa [prefixWord, tailWord_1112660, baseEnd_1112660] using wordTrace_append hprefix tailTrace_1112660
  have hstable : (prefixWord ++ tailWord_1112660).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1112660).length < 2 ^ (prefixWord ++ tailWord_1112660).sum := by decide
  have hdescent : baseEnd_1112660 < baseStart_1112660 := by decide
  rcases family_descends (prefixWord ++ tailWord_1112660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1112826 : List Nat := [3, 1, 1, 1, 1, 3, 5, 2, 4]
def baseStart_1112826 : Nat := 118140960795 + 1112826 * 2 ^ 59
def prefixEnd_1112826 : Nat := 4983230072969 + 3 ^ 40 * 1112826 * 2
def baseEnd_1112826 : Nat := 253962054586830354158761

theorem tailTrace_1112826 : CollatzResearch.WordTrace tailWord_1112826 prefixEnd_1112826 253962054586830354158761 := by
  unfold tailWord_1112826
  simp only [CollatzResearch.WordTrace]
  refine ⟨10147024666607233098703583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27058732444285954929876221 10147024666607233098703583)
  ·
    refine ⟨15220536999910849648055375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10147024666607233098703583 15220536999910849648055375)
    ·
      refine ⟨22830805499866274472083063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15220536999910849648055375 22830805499866274472083063)
      ·
        refine ⟨34246208249799411708124595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22830805499866274472083063 34246208249799411708124595)
        ·
          refine ⟨51369312374699117562186893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34246208249799411708124595 51369312374699117562186893)
          ·
            refine ⟨19263492140512169085820085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 51369312374699117562186893 19263492140512169085820085)
            ·
              refine ⟨1805952388173015851795633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 19263492140512169085820085 1805952388173015851795633)
              ·
                refine ⟨1354464291129761888846725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1805952388173015851795633 1354464291129761888846725)
                ·
                  refine ⟨253962054586830354158761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1354464291129761888846725 253962054586830354158761)
                  ·
                    rfl

theorem cell21_1112826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 5, 2, 4].length) (baseStart_1112826 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1112826 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1112826 prefixEnd_1112826 := by exact prefixLift 1112826
  have htrace : WordTrace (prefixWord ++ tailWord_1112826) baseStart_1112826 baseEnd_1112826 := by
    simpa [prefixWord, tailWord_1112826, baseEnd_1112826] using wordTrace_append hprefix tailTrace_1112826
  have hstable : (prefixWord ++ tailWord_1112826).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1112826).length < 2 ^ (prefixWord ++ tailWord_1112826).sum := by decide
  have hdescent : baseEnd_1112826 < baseStart_1112826 := by decide
  rcases family_descends (prefixWord ++ tailWord_1112826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1112874 : List Nat := [3, 1, 4, 3, 1, 2, 7]
def baseStart_1112874 : Nat := 118140960795 + 1112874 * 2 ^ 59
def prefixEnd_1112874 : Nat := 4983230072969 + 3 ^ 40 * 1112874 * 2
def baseEnd_1112874 : Nat := 28219223204532548595407

theorem tailTrace_1112874 : CollatzResearch.WordTrace tailWord_1112874 prefixEnd_1112874 28219223204532548595407 := by
  unfold tailWord_1112874
  simp only [CollatzResearch.WordTrace]
  refine ⟨10147462342563759148140419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27059899580170024395041117 10147462342563759148140419)
  ·
    refine ⟨15221193513845638722210629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10147462342563759148140419 15221193513845638722210629)
    ·
      refine ⟨2853973783846057260414493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15221193513845638722210629 2853973783846057260414493)
      ·
        refine ⟨1070240168942271472655435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2853973783846057260414493 1070240168942271472655435)
        ·
          refine ⟨1605360253413407208983153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1070240168942271472655435 1605360253413407208983153)
          ·
            refine ⟨1204020190060055406737365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1605360253413407208983153 1204020190060055406737365)
            ·
              refine ⟨28219223204532548595407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1204020190060055406737365 28219223204532548595407)
              ·
                rfl

theorem cell21_1112874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 2, 7].length) (baseStart_1112874 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1112874 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1112874 prefixEnd_1112874 := by exact prefixLift 1112874
  have htrace : WordTrace (prefixWord ++ tailWord_1112874) baseStart_1112874 baseEnd_1112874 := by
    simpa [prefixWord, tailWord_1112874, baseEnd_1112874] using wordTrace_append hprefix tailTrace_1112874
  have hstable : (prefixWord ++ tailWord_1112874).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1112874).length < 2 ^ (prefixWord ++ tailWord_1112874).sum := by decide
  have hdescent : baseEnd_1112874 < baseStart_1112874 := by decide
  rcases family_descends (prefixWord ++ tailWord_1112874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1112950 : List Nat := [5, 1, 1, 3, 1, 3, 1, 6]
def baseStart_1112950 : Nat := 118140960795 + 1112950 * 2 ^ 59
def prefixEnd_1112950 : Nat := 4983230072969 + 3 ^ 40 * 1112950 * 2
def baseEnd_1112950 : Nat := 84663451025411231363947

theorem tailTrace_1112950 : CollatzResearch.WordTrace tailWord_1112950 prefixEnd_1112950 84663451025411231363947 := by
  unfold tailWord_1112950
  simp only [CollatzResearch.WordTrace]
  refine ⟨2537038832373731348270519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 27061747545319801048218869 2537038832373731348270519)
  ·
    refine ⟨3805558248560597022405779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2537038832373731348270519 3805558248560597022405779)
    ·
      refine ⟨5708337372840895533608669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3805558248560597022405779 5708337372840895533608669)
      ·
        refine ⟨2140626514815335825103251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5708337372840895533608669 2140626514815335825103251)
        ·
          refine ⟨3210939772223003737654877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2140626514815335825103251 3210939772223003737654877)
          ·
            refine ⟨1204102414583626401620579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3210939772223003737654877 1204102414583626401620579)
            ·
              refine ⟨1806153621875439602430869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1204102414583626401620579 1806153621875439602430869)
              ·
                refine ⟨84663451025411231363947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1806153621875439602430869 84663451025411231363947)
                ·
                  rfl

theorem cell21_1112950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 3, 1, 6].length) (baseStart_1112950 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1112950 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1112950 prefixEnd_1112950 := by exact prefixLift 1112950
  have htrace : WordTrace (prefixWord ++ tailWord_1112950) baseStart_1112950 baseEnd_1112950 := by
    simpa [prefixWord, tailWord_1112950, baseEnd_1112950] using wordTrace_append hprefix tailTrace_1112950
  have hstable : (prefixWord ++ tailWord_1112950).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1112950).length < 2 ^ (prefixWord ++ tailWord_1112950).sum := by decide
  have hdescent : baseEnd_1112950 < baseStart_1112950 := by decide
  rcases family_descends (prefixWord ++ tailWord_1112950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1113071 : List Nat := [1, 1, 2, 1, 4, 5, 2, 1, 4]
def baseStart_1113071 : Nat := 118140960795 + 1113071 * 2 ^ 59
def prefixEnd_1113071 : Nat := 4983230072969 + 3 ^ 40 * 1113071 * 2
def baseEnd_1113071 : Nat := 254017966924764372574927

theorem tailTrace_1113071 : CollatzResearch.WordTrace tailWord_1113071 prefixEnd_1113071 254017966924764372574927 := by
  unfold tailWord_1113071
  simp only [CollatzResearch.WordTrace]
  refine ⟨40597034550541339237483067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27064689700360892824988711 40597034550541339237483067)
  ·
    refine ⟨60895551825812008856224601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40597034550541339237483067 60895551825812008856224601)
    ·
      refine ⟨45671663869359006642168451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60895551825812008856224601 45671663869359006642168451)
      ·
        refine ⟨68507495804038509963252677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45671663869359006642168451 68507495804038509963252677)
        ·
          refine ⟨12845155463257220618109877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 68507495804038509963252677 12845155463257220618109877)
          ·
            refine ⟨1204233324680364432947801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 12845155463257220618109877 1204233324680364432947801)
            ·
              refine ⟨903174993510273324710851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1204233324680364432947801 903174993510273324710851)
              ·
                refine ⟨1354762490265409987066277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 903174993510273324710851 1354762490265409987066277)
                ·
                  refine ⟨254017966924764372574927, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1354762490265409987066277 254017966924764372574927)
                  ·
                    rfl

theorem cell21_1113071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 5, 2, 1, 4].length) (baseStart_1113071 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1113071 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1113071 prefixEnd_1113071 := by exact prefixLift 1113071
  have htrace : WordTrace (prefixWord ++ tailWord_1113071) baseStart_1113071 baseEnd_1113071 := by
    simpa [prefixWord, tailWord_1113071, baseEnd_1113071] using wordTrace_append hprefix tailTrace_1113071
  have hstable : (prefixWord ++ tailWord_1113071).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1113071).length < 2 ^ (prefixWord ++ tailWord_1113071).sum := by decide
  have hdescent : baseEnd_1113071 < baseStart_1113071 := by decide
  rcases family_descends (prefixWord ++ tailWord_1113071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1113082 : List Nat := [3, 1, 1, 1, 1, 2, 1, 6, 5]
def baseStart_1113082 : Nat := 118140960795 + 1113082 * 2 ^ 59
def prefixEnd_1113082 : Nat := 4983230072969 + 3 ^ 40 * 1113082 * 2
def baseEnd_1113082 : Nat := 254020477274630797891571

theorem tailTrace_1113082 : CollatzResearch.WordTrace tailWord_1113082 prefixEnd_1113082 254020477274630797891571 := by
  unfold tailWord_1113082
  simp only [CollatzResearch.WordTrace]
  refine ⟨10149358938375372029033375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27064957169000992077422333 10149358938375372029033375)
  ·
    refine ⟨15224038407563058043550063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10149358938375372029033375 15224038407563058043550063)
    ·
      refine ⟨22836057611344587065325095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15224038407563058043550063 22836057611344587065325095)
      ·
        refine ⟨34254086417016880597987643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22836057611344587065325095 34254086417016880597987643)
        ·
          refine ⟨51381129625525320896981465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34254086417016880597987643 51381129625525320896981465)
          ·
            refine ⟨38535847219143990672736099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51381129625525320896981465 38535847219143990672736099)
            ·
              refine ⟨57803770828715986009104149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38535847219143990672736099 57803770828715986009104149)
              ·
                refine ⟨2709551757596061844176757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 57803770828715986009104149 2709551757596061844176757)
                ·
                  refine ⟨254020477274630797891571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2709551757596061844176757 254020477274630797891571)
                  ·
                    rfl

theorem cell21_1113082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 6, 5].length) (baseStart_1113082 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1113082 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1113082 prefixEnd_1113082 := by exact prefixLift 1113082
  have htrace : WordTrace (prefixWord ++ tailWord_1113082) baseStart_1113082 baseEnd_1113082 := by
    simpa [prefixWord, tailWord_1113082, baseEnd_1113082] using wordTrace_append hprefix tailTrace_1113082
  have hstable : (prefixWord ++ tailWord_1113082).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1113082).length < 2 ^ (prefixWord ++ tailWord_1113082).sum := by decide
  have hdescent : baseEnd_1113082 < baseStart_1113082 := by decide
  rcases family_descends (prefixWord ++ tailWord_1113082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1113113 : List Nat := [1, 2, 1, 2, 1, 1, 5, 4, 4]
def baseStart_1113113 : Nat := 118140960795 + 1113113 * 2 ^ 59
def prefixEnd_1113113 : Nat := 4983230072969 + 3 ^ 40 * 1113113 * 2
def baseEnd_1113113 : Nat := 254027551896981632874841

theorem tailTrace_1113113 : CollatzResearch.WordTrace tailWord_1113113 prefixEnd_1113113 254027551896981632874841 := by
  unfold tailWord_1113113
  simp only [CollatzResearch.WordTrace]
  refine ⟨40598566416389180410511993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27065710944259453607007995 40598566416389180410511993)
  ·
    refine ⟨30448924812291885307883995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40598566416389180410511993 30448924812291885307883995)
    ·
      refine ⟨45673387218437827961825993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30448924812291885307883995 45673387218437827961825993)
      ·
        refine ⟨34255040413828370971369495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45673387218437827961825993 34255040413828370971369495)
        ·
          refine ⟨51382560620742556457054243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34255040413828370971369495 51382560620742556457054243)
          ·
            refine ⟨77073840931113834685581365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51382560620742556457054243 77073840931113834685581365)
            ·
              refine ⟨7225672587291922001773253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 77073840931113834685581365 7225672587291922001773253)
              ·
                refine ⟨1354813610117235375332485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7225672587291922001773253 1354813610117235375332485)
                ·
                  refine ⟨254027551896981632874841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1354813610117235375332485 254027551896981632874841)
                  ·
                    rfl

theorem cell21_1113113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 5, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 5, 4, 4].length) (baseStart_1113113 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1113113 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1113113 prefixEnd_1113113 := by exact prefixLift 1113113
  have htrace : WordTrace (prefixWord ++ tailWord_1113113) baseStart_1113113 baseEnd_1113113 := by
    simpa [prefixWord, tailWord_1113113, baseEnd_1113113] using wordTrace_append hprefix tailTrace_1113113
  have hstable : (prefixWord ++ tailWord_1113113).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1113113).length < 2 ^ (prefixWord ++ tailWord_1113113).sum := by decide
  have hdescent : baseEnd_1113113 < baseStart_1113113 := by decide
  rcases family_descends (prefixWord ++ tailWord_1113113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1113209 : List Nat := [1, 2, 1, 3, 5, 2, 1, 3, 3]
def baseStart_1113209 : Nat := 118140960795 + 1113209 * 2 ^ 59
def prefixEnd_1113209 : Nat := 4983230072969 + 3 ^ 40 * 1113209 * 2
def baseEnd_1113209 : Nat := 254049460404906799274645

theorem tailTrace_1113209 : CollatzResearch.WordTrace tailWord_1113209 prefixEnd_1113209 254049460404906799274645 := by
  unfold tailWord_1113209
  simp only [CollatzResearch.WordTrace]
  refine ⟨40602067824041388806006681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27068045216027592537337787 40602067824041388806006681)
  ·
    refine ⟨30451550868031041604505011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40602067824041388806006681 30451550868031041604505011)
    ·
      refine ⟨45677326302046562406757517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30451550868031041604505011 45677326302046562406757517)
      ·
        refine ⟨17128997363267460902534069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 45677326302046562406757517 17128997363267460902534069)
        ·
          refine ⟨1605843502806324459612569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 17128997363267460902534069 1605843502806324459612569)
          ·
            refine ⟨1204382627104743344709427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1605843502806324459612569 1204382627104743344709427)
            ·
              refine ⟨1806573940657115017064141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1204382627104743344709427 1806573940657115017064141)
              ·
                refine ⟨677465227746418131399053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1806573940657115017064141 677465227746418131399053)
                ·
                  refine ⟨254049460404906799274645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 677465227746418131399053 254049460404906799274645)
                  ·
                    rfl

theorem cell21_1113209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 2, 1, 3, 3].length) (baseStart_1113209 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1113209 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1113209 prefixEnd_1113209 := by exact prefixLift 1113209
  have htrace : WordTrace (prefixWord ++ tailWord_1113209) baseStart_1113209 baseEnd_1113209 := by
    simpa [prefixWord, tailWord_1113209, baseEnd_1113209] using wordTrace_append hprefix tailTrace_1113209
  have hstable : (prefixWord ++ tailWord_1113209).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1113209).length < 2 ^ (prefixWord ++ tailWord_1113209).sum := by decide
  have hdescent : baseEnd_1113209 < baseStart_1113209 := by decide
  rcases family_descends (prefixWord ++ tailWord_1113209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1113220 : List Nat := [2, 3, 2, 1, 2, 4, 7]
def baseStart_1113220 : Nat := 118140960795 + 1113220 * 2 ^ 59
def prefixEnd_1113220 : Nat := 4983230072969 + 3 ^ 40 * 1113220 * 2
def baseEnd_1113220 : Nat := 28227996750530358287921

theorem tailTrace_1113220 : CollatzResearch.WordTrace tailWord_1113220 prefixEnd_1113220 28227996750530358287921 := by
  unfold tailWord_1113220
  simp only [CollatzResearch.WordTrace]
  refine ⟨20301234513500768842328557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27068312684667691789771409 20301234513500768842328557)
  ·
    refine ⟨7612962942562788315873209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20301234513500768842328557 7612962942562788315873209)
    ·
      refine ⟨5709722206922091236904907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7612962942562788315873209 5709722206922091236904907)
      ·
        refine ⟨8564583310383136855357361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5709722206922091236904907 8564583310383136855357361)
        ·
          refine ⟨6423437482787352641518021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8564583310383136855357361 6423437482787352641518021)
          ·
            refine ⟨1204394528022628620284629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6423437482787352641518021 1204394528022628620284629)
            ·
              refine ⟨28227996750530358287921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1204394528022628620284629 28227996750530358287921)
              ·
                rfl

theorem cell21_1113220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 4, 7].length) (baseStart_1113220 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1113220 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1113220 prefixEnd_1113220 := by exact prefixLift 1113220
  have htrace : WordTrace (prefixWord ++ tailWord_1113220) baseStart_1113220 baseEnd_1113220 := by
    simpa [prefixWord, tailWord_1113220, baseEnd_1113220] using wordTrace_append hprefix tailTrace_1113220
  have hstable : (prefixWord ++ tailWord_1113220).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1113220).length < 2 ^ (prefixWord ++ tailWord_1113220).sum := by decide
  have hdescent : baseEnd_1113220 < baseStart_1113220 := by decide
  rcases family_descends (prefixWord ++ tailWord_1113220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1113372 : List Nat := [2, 2, 3, 1, 1, 1, 6, 5]
def baseStart_1113372 : Nat := 118140960795 + 1113372 * 2 ^ 59
def prefixEnd_1113372 : Nat := 4983230072969 + 3 ^ 40 * 1113372 * 2
def baseEnd_1113372 : Nat := 84695553075218246019215

theorem tailTrace_1113372 : CollatzResearch.WordTrace tailWord_1113372 prefixEnd_1113372 84695553075218246019215 := by
  unfold tailWord_1113372
  simp only [CollatzResearch.WordTrace]
  refine ⟨20304006461225433822095185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27072008614967245096126913 20304006461225433822095185)
  ·
    refine ⟨15228004845919075366571389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20304006461225433822095185 15228004845919075366571389)
    ·
      refine ⟨5710501817219653262464271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15228004845919075366571389 5710501817219653262464271)
      ·
        refine ⟨8565752725829479893696407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5710501817219653262464271 8565752725829479893696407)
        ·
          refine ⟨12848629088744219840544611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8565752725829479893696407 12848629088744219840544611)
          ·
            refine ⟨19272943633116329760816917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12848629088744219840544611 19272943633116329760816917)
            ·
              refine ⟨903419232802327957538293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 19272943633116329760816917 903419232802327957538293)
              ·
                refine ⟨84695553075218246019215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 903419232802327957538293 84695553075218246019215)
                ·
                  rfl

theorem cell21_1113372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 6, 5].length) (baseStart_1113372 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1113372 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1113372 prefixEnd_1113372 := by exact prefixLift 1113372
  have htrace : WordTrace (prefixWord ++ tailWord_1113372) baseStart_1113372 baseEnd_1113372 := by
    simpa [prefixWord, tailWord_1113372, baseEnd_1113372] using wordTrace_append hprefix tailTrace_1113372
  have hstable : (prefixWord ++ tailWord_1113372).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1113372).length < 2 ^ (prefixWord ++ tailWord_1113372).sum := by decide
  have hdescent : baseEnd_1113372 < baseStart_1113372 := by decide
  rcases family_descends (prefixWord ++ tailWord_1113372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1113378 : List Nat := [3, 3, 1, 1, 5, 1, 1, 3, 3]
def baseStart_1113378 : Nat := 118140960795 + 1113378 * 2 ^ 59
def prefixEnd_1113378 : Nat := 4983230072969 + 3 ^ 40 * 1113378 * 2
def baseEnd_1113378 : Nat := 254088028507400060957633

theorem tailTrace_1113378 : CollatzResearch.WordTrace tailWord_1113378 prefixEnd_1113378 254088028507400060957633 := by
  unfold tailWord_1113378
  simp only [CollatzResearch.WordTrace]
  refine ⟨10152057940107282667227197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27072154506952753779272525 10152057940107282667227197)
  ·
    refine ⟨3807021727540231000210199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10152057940107282667227197 3807021727540231000210199)
    ·
      refine ⟨5710532591310346500315299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3807021727540231000210199 5710532591310346500315299)
      ·
        refine ⟨8565798886965519750472949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5710532591310346500315299 8565798886965519750472949)
        ·
          refine ⟨803043645653017476606839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 8565798886965519750472949 803043645653017476606839)
          ·
            refine ⟨1204565468479526214910259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 803043645653017476606839 1204565468479526214910259)
            ·
              refine ⟨1806848202719289322365389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1204565468479526214910259 1806848202719289322365389)
              ·
                refine ⟨677568076019733495887021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1806848202719289322365389 677568076019733495887021)
                ·
                  refine ⟨254088028507400060957633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 677568076019733495887021 254088028507400060957633)
                  ·
                    rfl

theorem cell21_1113378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 5, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 5, 1, 1, 3, 3].length) (baseStart_1113378 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1113378 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1113378 prefixEnd_1113378 := by exact prefixLift 1113378
  have htrace : WordTrace (prefixWord ++ tailWord_1113378) baseStart_1113378 baseEnd_1113378 := by
    simpa [prefixWord, tailWord_1113378, baseEnd_1113378] using wordTrace_append hprefix tailTrace_1113378
  have hstable : (prefixWord ++ tailWord_1113378).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1113378).length < 2 ^ (prefixWord ++ tailWord_1113378).sum := by decide
  have hdescent : baseEnd_1113378 < baseStart_1113378 := by decide
  rcases family_descends (prefixWord ++ tailWord_1113378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1113389 : List Nat := [1, 5, 3, 1, 1, 3, 7]
def baseStart_1113389 : Nat := 118140960795 + 1113389 * 2 ^ 59
def prefixEnd_1113389 : Nat := 4983230072969 + 3 ^ 40 * 1113389 * 2
def baseEnd_1113389 : Nat := 28232282095251831808253

theorem tailTrace_1113389 : CollatzResearch.WordTrace tailWord_1113389 prefixEnd_1113389 28232282095251831808253 := by
  unfold tailWord_1113389
  simp only [CollatzResearch.WordTrace]
  refine ⟨40608632963389279547559221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27072421975592853031706147 40608632963389279547559221)
  ·
    refine ⟨3807059340317744957583677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 40608632963389279547559221 3807059340317744957583677)
    ·
      refine ⟨1427647252619154359093879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3807059340317744957583677 1427647252619154359093879)
      ·
        refine ⟨2141470878928731538640819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1427647252619154359093879 2141470878928731538640819)
        ·
          refine ⟨3212206318393097307961229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2141470878928731538640819 3212206318393097307961229)
          ·
            refine ⟨1204577369397411490485461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3212206318393097307961229 1204577369397411490485461)
            ·
              refine ⟨28232282095251831808253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1204577369397411490485461 28232282095251831808253)
              ·
                rfl

theorem cell21_1113389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 3, 7].length) (baseStart_1113389 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1113389 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1113389 prefixEnd_1113389 := by exact prefixLift 1113389
  have htrace : WordTrace (prefixWord ++ tailWord_1113389) baseStart_1113389 baseEnd_1113389 := by
    simpa [prefixWord, tailWord_1113389, baseEnd_1113389] using wordTrace_append hprefix tailTrace_1113389
  have hstable : (prefixWord ++ tailWord_1113389).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1113389).length < 2 ^ (prefixWord ++ tailWord_1113389).sum := by decide
  have hdescent : baseEnd_1113389 < baseStart_1113389 := by decide
  rcases family_descends (prefixWord ++ tailWord_1113389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1113431 : List Nat := [1, 1, 3, 2, 3, 2, 2, 7]
def baseStart_1113431 : Nat := 118140960795 + 1113431 * 2 ^ 59
def prefixEnd_1113431 : Nat := 4983230072969 + 3 ^ 40 * 1113431 * 2
def baseEnd_1113431 : Nat := 84700041276494582191397

theorem tailTrace_1113431 : CollatzResearch.WordTrace tailWord_1113431 prefixEnd_1113431 84700041276494582191397 := by
  unfold tailWord_1113431
  simp only [CollatzResearch.WordTrace]
  refine ⟨40610164829237120720588147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27073443219491413813725431 40610164829237120720588147)
  ·
    refine ⟨60915247243855681080882221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40610164829237120720588147 60915247243855681080882221)
    ·
      refine ⟨22843217716445880405330833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 60915247243855681080882221 22843217716445880405330833)
      ·
        refine ⟨17132413287334410303998125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22843217716445880405330833 17132413287334410303998125)
        ·
          refine ⟨6424654982750403863999297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17132413287334410303998125 6424654982750403863999297)
          ·
            refine ⟨4818491237062802897999473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6424654982750403863999297 4818491237062802897999473)
            ·
              refine ⟨3613868427797102173499605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4818491237062802897999473 3613868427797102173499605)
              ·
                refine ⟨84700041276494582191397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3613868427797102173499605 84700041276494582191397)
                ·
                  rfl

theorem cell21_1113431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 2, 7].length) (baseStart_1113431 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1113431 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1113431 prefixEnd_1113431 := by exact prefixLift 1113431
  have htrace : WordTrace (prefixWord ++ tailWord_1113431) baseStart_1113431 baseEnd_1113431 := by
    simpa [prefixWord, tailWord_1113431, baseEnd_1113431] using wordTrace_append hprefix tailTrace_1113431
  have hstable : (prefixWord ++ tailWord_1113431).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1113431).length < 2 ^ (prefixWord ++ tailWord_1113431).sum := by decide
  have hdescent : baseEnd_1113431 < baseStart_1113431 := by decide
  rcases family_descends (prefixWord ++ tailWord_1113431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1113448 : List Nat := [2, 1, 4, 2, 4, 8]
def baseStart_1113448 : Nat := 118140960795 + 1113448 * 2 ^ 59
def prefixEnd_1113448 : Nat := 4983230072969 + 3 ^ 40 * 1113448 * 2
def baseEnd_1113448 : Nat := 9411259387447981288549

theorem tailTrace_1113448 : CollatzResearch.WordTrace tailWord_1113448 prefixEnd_1113448 9411259387447981288549 := by
  unfold tailWord_1113448
  simp only [CollatzResearch.WordTrace]
  refine ⟨20305392435087766311978499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27073856580117021749304665 20305392435087766311978499)
  ·
    refine ⟨30458088652631649467967749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20305392435087766311978499 30458088652631649467967749)
    ·
      refine ⟨5710891622368434275243953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 30458088652631649467967749 5710891622368434275243953)
      ·
        refine ⟨4283168716776325706432965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5710891622368434275243953 4283168716776325706432965)
        ·
          refine ⟨803094134395561069956181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4283168716776325706432965 803094134395561069956181)
          ·
            refine ⟨9411259387447981288549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 803094134395561069956181 9411259387447981288549)
            ·
              rfl

theorem cell21_1113448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 4, 8].length) (baseStart_1113448 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1113448 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1113448 prefixEnd_1113448 := by exact prefixLift 1113448
  have htrace : WordTrace (prefixWord ++ tailWord_1113448) baseStart_1113448 baseEnd_1113448 := by
    simpa [prefixWord, tailWord_1113448, baseEnd_1113448] using wordTrace_append hprefix tailTrace_1113448
  have hstable : (prefixWord ++ tailWord_1113448).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1113448).length < 2 ^ (prefixWord ++ tailWord_1113448).sum := by decide
  have hdescent : baseEnd_1113448 < baseStart_1113448 := by decide
  rcases family_descends (prefixWord ++ tailWord_1113448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1113586 : List Nat := [3, 2, 1, 4, 1, 2, 1, 3, 4]
def baseStart_1113586 : Nat := 118140960795 + 1113586 * 2 ^ 59
def prefixEnd_1113586 : Nat := 4983230072969 + 3 ^ 40 * 1113586 * 2
def baseEnd_1113586 : Nat := 254135496941237921490541

theorem tailTrace_1113586 : CollatzResearch.WordTrace tailWord_1113586 prefixEnd_1113586 254135496941237921490541 := by
  unfold tailWord_1113586
  simp only [CollatzResearch.WordTrace]
  refine ⟨10153954535918895548120153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27077212095783721461653741 10153954535918895548120153)
  ·
    refine ⟨7615465901939171661090115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10153954535918895548120153 7615465901939171661090115)
    ·
      refine ⟨11423198852908757491635173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7615465901939171661090115 11423198852908757491635173)
      ·
        refine ⟨2141849784920392029681595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11423198852908757491635173 2141849784920392029681595)
        ·
          refine ⟨3212774677380588044522393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2141849784920392029681595 3212774677380588044522393)
          ·
            refine ⟨2409581008035441033391795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3212774677380588044522393 2409581008035441033391795)
            ·
              refine ⟨3614371512053161550087693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2409581008035441033391795 3614371512053161550087693)
              ·
                refine ⟨1355389317019935581282885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3614371512053161550087693 1355389317019935581282885)
                ·
                  refine ⟨254135496941237921490541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1355389317019935581282885 254135496941237921490541)
                  ·
                    rfl

theorem cell21_1113586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 2, 1, 3, 4].length) (baseStart_1113586 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1113586 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1113586 prefixEnd_1113586 := by exact prefixLift 1113586
  have htrace : WordTrace (prefixWord ++ tailWord_1113586) baseStart_1113586 baseEnd_1113586 := by
    simpa [prefixWord, tailWord_1113586, baseEnd_1113586] using wordTrace_append hprefix tailTrace_1113586
  have hstable : (prefixWord ++ tailWord_1113586).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1113586).length < 2 ^ (prefixWord ++ tailWord_1113586).sum := by decide
  have hdescent : baseEnd_1113586 < baseStart_1113586 := by decide
  rcases family_descends (prefixWord ++ tailWord_1113586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1113710 : List Nat := [4, 1, 2, 2, 4, 1, 2, 5]
def baseStart_1113710 : Nat := 118140960795 + 1113710 * 2 ^ 59
def prefixEnd_1113710 : Nat := 4983230072969 + 3 ^ 40 * 1113710 * 2
def baseEnd_1113710 : Nat := 84721265143547087141207

theorem tailTrace_1113710 : CollatzResearch.WordTrace tailWord_1113710 prefixEnd_1113710 84721265143547087141207 := by
  unfold tailWord_1113710
  simp only [CollatzResearch.WordTrace]
  refine ⟨5077542599403293921249323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 27080227196817567579996389 5077542599403293921249323)
  ·
    refine ⟨7616313899104940881873985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5077542599403293921249323 7616313899104940881873985)
    ·
      refine ⟨5712235424328705661405489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7616313899104940881873985 5712235424328705661405489)
      ·
        refine ⟨4284176568246529246054117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5712235424328705661405489 4284176568246529246054117)
        ·
          refine ⟨803283106546224233635147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4284176568246529246054117 803283106546224233635147)
          ·
            refine ⟨1204924659819336350452721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 803283106546224233635147 1204924659819336350452721)
            ·
              refine ⟨903693494864502262839541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1204924659819336350452721 903693494864502262839541)
              ·
                refine ⟨84721265143547087141207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 903693494864502262839541 84721265143547087141207)
                ·
                  rfl

theorem cell21_1113710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 4, 1, 2, 5].length) (baseStart_1113710 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1113710 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1113710 prefixEnd_1113710 := by exact prefixLift 1113710
  have htrace : WordTrace (prefixWord ++ tailWord_1113710) baseStart_1113710 baseEnd_1113710 := by
    simpa [prefixWord, tailWord_1113710, baseEnd_1113710] using wordTrace_append hprefix tailTrace_1113710
  have hstable : (prefixWord ++ tailWord_1113710).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1113710).length < 2 ^ (prefixWord ++ tailWord_1113710).sum := by decide
  have hdescent : baseEnd_1113710 < baseStart_1113710 := by decide
  rcases family_descends (prefixWord ++ tailWord_1113710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1113735 : List Nat := [1, 1, 4, 2, 1, 5, 7]
def baseStart_1113735 : Nat := 118140960795 + 1113735 * 2 ^ 59
def prefixEnd_1113735 : Nat := 4983230072969 + 3 ^ 40 * 1113735 * 2
def baseEnd_1113735 : Nat := 28241055641249641500767

theorem tailTrace_1113735 : CollatzResearch.WordTrace tailWord_1113735 prefixEnd_1113735 28241055641249641500767 := by
  unfold tailWord_1113735
  simp only [CollatzResearch.WordTrace]
  refine ⟨40621252620135780639654659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27080835080090520426436439 40621252620135780639654659)
  ·
    refine ⟨60931878930203670959481989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40621252620135780639654659 60931878930203670959481989)
    ·
      refine ⟨11424727299413188304902873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 60931878930203670959481989 11424727299413188304902873)
      ·
        refine ⟨8568545474559891228677155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11424727299413188304902873 8568545474559891228677155)
        ·
          refine ⟨12852818211839836843015733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8568545474559891228677155 12852818211839836843015733)
          ·
            refine ⟨1204951707359984704032725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 12852818211839836843015733 1204951707359984704032725)
            ·
              refine ⟨28241055641249641500767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1204951707359984704032725 28241055641249641500767)
              ·
                rfl

theorem cell21_1113735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 5, 7].length) (baseStart_1113735 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1113735 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1113735 prefixEnd_1113735 := by exact prefixLift 1113735
  have htrace : WordTrace (prefixWord ++ tailWord_1113735) baseStart_1113735 baseEnd_1113735 := by
    simpa [prefixWord, tailWord_1113735, baseEnd_1113735] using wordTrace_append hprefix tailTrace_1113735
  have hstable : (prefixWord ++ tailWord_1113735).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1113735).length < 2 ^ (prefixWord ++ tailWord_1113735).sum := by decide
  have hdescent : baseEnd_1113735 < baseStart_1113735 := by decide
  rcases family_descends (prefixWord ++ tailWord_1113735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1113946 : List Nat := [3, 1, 1, 2, 1, 3, 1, 9]
def baseStart_1113946 : Nat := 118140960795 + 1113946 * 2 ^ 59
def prefixEnd_1113946 : Nat := 4983230072969 + 3 ^ 40 * 1113946 * 2
def baseEnd_1113946 : Nat := 84739217948652431829935

theorem tailTrace_1113946 : CollatzResearch.WordTrace tailWord_1113946 prefixEnd_1113946 84739217948652431829935 := by
  unfold tailWord_1113946
  simp only [CollatzResearch.WordTrace]
  refine ⟨10157237105592840918896423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27085965614914242450390461 10157237105592840918896423)
  ·
    refine ⟨15235855658389261378344635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10157237105592840918896423 15235855658389261378344635)
    ·
      refine ⟨22853783487583892067516953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15235855658389261378344635 22853783487583892067516953)
      ·
        refine ⟨17140337615687919050637715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22853783487583892067516953 17140337615687919050637715)
        ·
          refine ⟨25710506423531878575956573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17140337615687919050637715 25710506423531878575956573)
          ·
            refine ⟨9641439908824454465983715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25710506423531878575956573 9641439908824454465983715)
            ·
              refine ⟨14462159863236681698975573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9641439908824454465983715 14462159863236681698975573)
              ·
                refine ⟨84739217948652431829935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 14462159863236681698975573 84739217948652431829935)
                ·
                  rfl

theorem cell21_1113946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 1, 9].length) (baseStart_1113946 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1113946 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1113946 prefixEnd_1113946 := by exact prefixLift 1113946
  have htrace : WordTrace (prefixWord ++ tailWord_1113946) baseStart_1113946 baseEnd_1113946 := by
    simpa [prefixWord, tailWord_1113946, baseEnd_1113946] using wordTrace_append hprefix tailTrace_1113946
  have hstable : (prefixWord ++ tailWord_1113946).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1113946).length < 2 ^ (prefixWord ++ tailWord_1113946).sum := by decide
  have hdescent : baseEnd_1113946 < baseStart_1113946 := by decide
  rcases family_descends (prefixWord ++ tailWord_1113946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1113966 : List Nat := [4, 1, 2, 3, 1, 2, 2, 2, 4]
def baseStart_1113966 : Nat := 118140960795 + 1113966 * 2 ^ 59
def prefixEnd_1113966 : Nat := 4983230072969 + 3 ^ 40 * 1113966 * 2
def baseEnd_1113966 : Nat := 254222218118441705156431

theorem tailTrace_1113966 : CollatzResearch.WordTrace tailWord_1113966 prefixEnd_1113966 254222218118441705156431 := by
  unfold tailWord_1113966
  simp only [CollatzResearch.WordTrace]
  refine ⟨5078709735287363386414219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 27086451921532604727542501 5078709735287363386414219)
  ·
    refine ⟨7618064602931045079621329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5078709735287363386414219 7618064602931045079621329)
    ·
      refine ⟨5713548452198283809715997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7618064602931045079621329 5713548452198283809715997)
      ·
        refine ⟨2142580669574356428643499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5713548452198283809715997 2142580669574356428643499)
        ·
          refine ⟨3213871004361534642965249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2142580669574356428643499 3213871004361534642965249)
          ·
            refine ⟨2410403253271150982223937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3213871004361534642965249 2410403253271150982223937)
            ·
              refine ⟨1807802439953363236667953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2410403253271150982223937 1807802439953363236667953)
              ·
                refine ⟨1355851829965022427500965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1807802439953363236667953 1355851829965022427500965)
                ·
                  refine ⟨254222218118441705156431, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1355851829965022427500965 254222218118441705156431)
                  ·
                    rfl

theorem cell21_1113966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 2, 2, 2, 4].length) (baseStart_1113966 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1113966 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1113966 prefixEnd_1113966 := by exact prefixLift 1113966
  have htrace : WordTrace (prefixWord ++ tailWord_1113966) baseStart_1113966 baseEnd_1113966 := by
    simpa [prefixWord, tailWord_1113966, baseEnd_1113966] using wordTrace_append hprefix tailTrace_1113966
  have hstable : (prefixWord ++ tailWord_1113966).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1113966).length < 2 ^ (prefixWord ++ tailWord_1113966).sum := by decide
  have hdescent : baseEnd_1113966 < baseStart_1113966 := by decide
  rcases family_descends (prefixWord ++ tailWord_1113966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1113977 : List Nat := [1, 2, 1, 3, 2, 2, 2, 3, 5]
def baseStart_1113977 : Nat := 118140960795 + 1113977 * 2 ^ 59
def prefixEnd_1113977 : Nat := 4983230072969 + 3 ^ 40 * 1113977 * 2
def baseEnd_1113977 : Nat := 254224728468308130473075

theorem tailTrace_1113977 : CollatzResearch.WordTrace tailWord_1113977 prefixEnd_1113977 254224728468308130473075 := by
  unfold tailWord_1113977
  simp only [CollatzResearch.WordTrace]
  refine ⟨40630079085259055969964185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27086719390172703979976123 40630079085259055969964185)
  ·
    refine ⟨30472559313944291977473139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40630079085259055969964185 30472559313944291977473139)
    ·
      refine ⟨45708838970916437966209709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30472559313944291977473139 45708838970916437966209709)
      ·
        refine ⟨17140814614093664237328641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 45708838970916437966209709 17140814614093664237328641)
        ·
          refine ⟨12855610960570248177996481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17140814614093664237328641 12855610960570248177996481)
          ·
            refine ⟨9641708220427686133497361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12855610960570248177996481 9641708220427686133497361)
            ·
              refine ⟨7231281165320764600123021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9641708220427686133497361 7231281165320764600123021)
              ·
                refine ⟨2711730436995286725046133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7231281165320764600123021 2711730436995286725046133)
                ·
                  refine ⟨254224728468308130473075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2711730436995286725046133 254224728468308130473075)
                  ·
                    rfl

theorem cell21_1113977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 2, 3, 5].length) (baseStart_1113977 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1113977 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1113977 prefixEnd_1113977 := by exact prefixLift 1113977
  have htrace : WordTrace (prefixWord ++ tailWord_1113977) baseStart_1113977 baseEnd_1113977 := by
    simpa [prefixWord, tailWord_1113977, baseEnd_1113977] using wordTrace_append hprefix tailTrace_1113977
  have hstable : (prefixWord ++ tailWord_1113977).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1113977).length < 2 ^ (prefixWord ++ tailWord_1113977).sum := by decide
  have hdescent : baseEnd_1113977 < baseStart_1113977 := by decide
  rcases family_descends (prefixWord ++ tailWord_1113977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1114056 : List Nat := [2, 1, 3, 1, 4, 3, 2, 5]
def baseStart_1114056 : Nat := 118140960795 + 1114056 * 2 ^ 59
def prefixEnd_1114056 : Nat := 4983230072969 + 3 ^ 40 * 1114056 * 2
def baseEnd_1114056 : Nat := 84747585781540516218749

theorem tailTrace_1114056 : CollatzResearch.WordTrace tailWord_1114056 prefixEnd_1114056 84747585781540516218749 := by
  unfold tailWord_1114056
  simp only [CollatzResearch.WordTrace]
  refine ⟨20316480225986426231045011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27088640301315234974726681 20316480225986426231045011)
  ·
    refine ⟨30474720338979639346567517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20316480225986426231045011 30474720338979639346567517)
    ·
      refine ⟨11428020127117364754962819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30474720338979639346567517 11428020127117364754962819)
      ·
        refine ⟨17142030190676047132444229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11428020127117364754962819 17142030190676047132444229)
        ·
          refine ⟨3214130660751758837333293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17142030190676047132444229 3214130660751758837333293)
          ·
            refine ⟨1205298997781909563999985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3214130660751758837333293 1205298997781909563999985)
            ·
              refine ⟨903974248336432172999989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1205298997781909563999985 903974248336432172999989)
              ·
                refine ⟨84747585781540516218749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 903974248336432172999989 84747585781540516218749)
                ·
                  rfl

theorem cell21_1114056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 3, 2, 5].length) (baseStart_1114056 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1114056 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1114056 prefixEnd_1114056 := by exact prefixLift 1114056
  have htrace : WordTrace (prefixWord ++ tailWord_1114056) baseStart_1114056 baseEnd_1114056 := by
    simpa [prefixWord, tailWord_1114056, baseEnd_1114056] using wordTrace_append hprefix tailTrace_1114056
  have hstable : (prefixWord ++ tailWord_1114056).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1114056).length < 2 ^ (prefixWord ++ tailWord_1114056).sum := by decide
  have hdescent : baseEnd_1114056 < baseStart_1114056 := by decide
  rcases family_descends (prefixWord ++ tailWord_1114056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1114084 : List Nat := [2, 3, 1, 1, 1, 1, 4, 4, 4]
def baseStart_1114084 : Nat := 118140960795 + 1114084 * 2 ^ 59
def prefixEnd_1114084 : Nat := 4983230072969 + 3 ^ 40 * 1114084 * 2
def baseEnd_1114084 : Nat := 254249147326099722189523

theorem tailTrace_1114084 : CollatzResearch.WordTrace tailWord_1114084 prefixEnd_1114084 254249147326099722189523 := by
  unfold tailWord_1114084
  simp only [CollatzResearch.WordTrace]
  refine ⟨20316990847935706622054653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27089321130580942162739537 20316990847935706622054653)
  ·
    refine ⟨7618871567975889983270495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20316990847935706622054653 7618871567975889983270495)
    ·
      refine ⟨11428307351963834974905743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7618871567975889983270495 11428307351963834974905743)
      ·
        refine ⟨17142461027945752462358615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11428307351963834974905743 17142461027945752462358615)
        ·
          refine ⟨25713691541918628693537923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17142461027945752462358615 25713691541918628693537923)
          ·
            refine ⟨38570537312877943040306885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25713691541918628693537923 38570537312877943040306885)
            ·
              refine ⟨7231975746164614320057541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 38570537312877943040306885 7231975746164614320057541)
              ·
                refine ⟨1355995452405865185010789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7231975746164614320057541 1355995452405865185010789)
                ·
                  refine ⟨254249147326099722189523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1355995452405865185010789 254249147326099722189523)
                  ·
                    rfl

theorem cell21_1114084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 4, 4, 4].length) (baseStart_1114084 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1114084 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1114084 prefixEnd_1114084 := by exact prefixLift 1114084
  have htrace : WordTrace (prefixWord ++ tailWord_1114084) baseStart_1114084 baseEnd_1114084 := by
    simpa [prefixWord, tailWord_1114084, baseEnd_1114084] using wordTrace_append hprefix tailTrace_1114084
  have hstable : (prefixWord ++ tailWord_1114084).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1114084).length < 2 ^ (prefixWord ++ tailWord_1114084).sum := by decide
  have hdescent : baseEnd_1114084 < baseStart_1114084 := by decide
  rcases family_descends (prefixWord ++ tailWord_1114084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1114087 : List Nat := [1, 1, 5, 2, 3, 2, 1, 1, 5]
def baseStart_1114087 : Nat := 118140960795 + 1114087 * 2 ^ 59
def prefixEnd_1114087 : Nat := 4983230072969 + 3 ^ 40 * 1114087 * 2
def baseEnd_1114087 : Nat := 254249831966972383639517

theorem tailTrace_1114087 : CollatzResearch.WordTrace tailWord_1114087 prefixEnd_1114087 254249831966972383639517 := by
  unfold tailWord_1114087
  simp only [CollatzResearch.WordTrace]
  refine ⟨40634091114860544756468515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27089394076573696504312343 40634091114860544756468515)
  ·
    refine ⟨60951136672290817134702773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40634091114860544756468515 60951136672290817134702773)
    ·
      refine ⟨5714169063027264106378385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 60951136672290817134702773 5714169063027264106378385)
      ·
        refine ⟨4285626797270448079783789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5714169063027264106378385 4285626797270448079783789)
        ·
          refine ⟨1607110048976418029918921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4285626797270448079783789 1607110048976418029918921)
          ·
            refine ⟨1205332536732313522439191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1607110048976418029918921 1205332536732313522439191)
            ·
              refine ⟨1807998805098470283658787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1205332536732313522439191 1807998805098470283658787)
              ·
                refine ⟨2711998207647705425488181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1807998805098470283658787 2711998207647705425488181)
                ·
                  refine ⟨254249831966972383639517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2711998207647705425488181 254249831966972383639517)
                  ·
                    rfl

theorem cell21_1114087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 2, 1, 1, 5].length) (baseStart_1114087 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1114087 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1114087 prefixEnd_1114087 := by exact prefixLift 1114087
  have htrace : WordTrace (prefixWord ++ tailWord_1114087) baseStart_1114087 baseEnd_1114087 := by
    simpa [prefixWord, tailWord_1114087, baseEnd_1114087] using wordTrace_append hprefix tailTrace_1114087
  have hstable : (prefixWord ++ tailWord_1114087).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1114087).length < 2 ^ (prefixWord ++ tailWord_1114087).sum := by decide
  have hdescent : baseEnd_1114087 < baseStart_1114087 := by decide
  rcases family_descends (prefixWord ++ tailWord_1114087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1114132 : List Nat := [2, 4, 3, 2, 1, 9]
def baseStart_1114132 : Nat := 118140960795 + 1114132 * 2 ^ 59
def prefixEnd_1114132 : Nat := 4983230072969 + 3 ^ 40 * 1114132 * 2
def baseEnd_1114132 : Nat := 9417040799261566866275

theorem tailTrace_1114132 : CollatzResearch.WordTrace tailWord_1114132 prefixEnd_1114132 9417040799261566866275 := by
  unfold tailWord_1114132
  simp only [CollatzResearch.WordTrace]
  refine ⟨20317866199848758720928325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27090488266465011627904433 20317866199848758720928325)
  ·
    refine ⟨3809599912471642260174061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 20317866199848758720928325 3809599912471642260174061)
    ·
      refine ⟨1428599967176865847565273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3809599912471642260174061 1428599967176865847565273)
      ·
        refine ⟨1071449975382649385673955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1428599967176865847565273 1071449975382649385673955)
        ·
          refine ⟨1607174963073974078510933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1071449975382649385673955 1607174963073974078510933)
          ·
            refine ⟨9417040799261566866275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1607174963073974078510933 9417040799261566866275)
            ·
              rfl

theorem cell21_1114132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 9].length) (baseStart_1114132 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1114132 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1114132 prefixEnd_1114132 := by exact prefixLift 1114132
  have htrace : WordTrace (prefixWord ++ tailWord_1114132) baseStart_1114132 baseEnd_1114132 := by
    simpa [prefixWord, tailWord_1114132, baseEnd_1114132] using wordTrace_append hprefix tailTrace_1114132
  have hstable : (prefixWord ++ tailWord_1114132).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1114132).length < 2 ^ (prefixWord ++ tailWord_1114132).sum := by decide
  have hdescent : baseEnd_1114132 < baseStart_1114132 := by decide
  rcases family_descends (prefixWord ++ tailWord_1114132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1114160 : List Nat := [2, 1, 1, 1, 2, 5, 2, 3, 4]
def baseStart_1114160 : Nat := 118140960795 + 1114160 * 2 ^ 59
def prefixEnd_1114160 : Nat := 4983230072969 + 3 ^ 40 * 1114160 * 2
def baseEnd_1114160 : Nat := 254266491561540478922701

theorem tailTrace_1114160 : CollatzResearch.WordTrace tailWord_1114160 prefixEnd_1114160 254266491561540478922701 := by
  unfold tailWord_1114160
  simp only [CollatzResearch.WordTrace]
  refine ⟨20318376821798039111937967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27091169095730718815917289 20318376821798039111937967)
  ·
    refine ⟨30477565232697058667906951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20318376821798039111937967 30477565232697058667906951)
    ·
      refine ⟨45716347849045588001860427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30477565232697058667906951 45716347849045588001860427)
      ·
        refine ⟨68574521773568382002790641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45716347849045588001860427 68574521773568382002790641)
        ·
          refine ⟨51430891330176286502092981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 68574521773568382002790641 51430891330176286502092981)
          ·
            refine ⟨4821646062204026859571217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 51430891330176286502092981 4821646062204026859571217)
            ·
              refine ⟨3616234546653020144678413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4821646062204026859571217 3616234546653020144678413)
              ·
                refine ⟨1356087954994882554254405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3616234546653020144678413 1356087954994882554254405)
                ·
                  refine ⟨254266491561540478922701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1356087954994882554254405 254266491561540478922701)
                  ·
                    rfl

theorem cell21_1114160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 2, 3, 4].length) (baseStart_1114160 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1114160 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1114160 prefixEnd_1114160 := by exact prefixLift 1114160
  have htrace : WordTrace (prefixWord ++ tailWord_1114160) baseStart_1114160 baseEnd_1114160 := by
    simpa [prefixWord, tailWord_1114160, baseEnd_1114160] using wordTrace_append hprefix tailTrace_1114160
  have hstable : (prefixWord ++ tailWord_1114160).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1114160).length < 2 ^ (prefixWord ++ tailWord_1114160).sum := by decide
  have hdescent : baseEnd_1114160 < baseStart_1114160 := by decide
  rcases family_descends (prefixWord ++ tailWord_1114160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1114194 : List Nat := [3, 2, 2, 1, 4, 2, 1, 2, 4]
def baseStart_1114194 : Nat := 118140960795 + 1114194 * 2 ^ 59
def prefixEnd_1114194 : Nat := 4983230072969 + 3 ^ 40 * 1114194 * 2
def baseEnd_1114194 : Nat := 254274250824763975355965

theorem tailTrace_1114194 : CollatzResearch.WordTrace tailWord_1114194 prefixEnd_1114194 254274250824763975355965 := by
  unfold tailWord_1114194
  simp only [CollatzResearch.WordTrace]
  refine ⟨10159498431368225507653409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27091995816981934687075757 10159498431368225507653409)
  ·
    refine ⟨7619623823526169130740057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10159498431368225507653409 7619623823526169130740057)
    ·
      refine ⟨5714717867644626848055043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7619623823526169130740057 5714717867644626848055043)
      ·
        refine ⟨8572076801466940272082565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5714717867644626848055043 8572076801466940272082565)
        ·
          refine ⟨1607264400275051301015481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8572076801466940272082565 1607264400275051301015481)
          ·
            refine ⟨1205448300206288475761611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1607264400275051301015481 1205448300206288475761611)
            ·
              refine ⟨1808172450309432713642417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1205448300206288475761611 1808172450309432713642417)
              ·
                refine ⟨1356129337732074535231813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1808172450309432713642417 1356129337732074535231813)
                ·
                  refine ⟨254274250824763975355965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1356129337732074535231813 254274250824763975355965)
                  ·
                    rfl

theorem cell21_1114194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 2, 1, 2, 4].length) (baseStart_1114194 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1114194 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1114194 prefixEnd_1114194 := by exact prefixLift 1114194
  have htrace : WordTrace (prefixWord ++ tailWord_1114194) baseStart_1114194 baseEnd_1114194 := by
    simpa [prefixWord, tailWord_1114194, baseEnd_1114194] using wordTrace_append hprefix tailTrace_1114194
  have hstable : (prefixWord ++ tailWord_1114194).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1114194).length < 2 ^ (prefixWord ++ tailWord_1114194).sum := by decide
  have hdescent : baseEnd_1114194 < baseStart_1114194 := by decide
  rcases family_descends (prefixWord ++ tailWord_1114194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1114250 : List Nat := [3, 1, 2, 3, 1, 2, 9]
def baseStart_1114250 : Nat := 118140960795 + 1114250 * 2 ^ 59
def prefixEnd_1114250 : Nat := 4983230072969 + 3 ^ 40 * 1114250 * 2
def baseEnd_1114250 : Nat := 28254114531968924713613

theorem tailTrace_1114250 : CollatzResearch.WordTrace tailWord_1114250 prefixEnd_1114250 28254114531968924713613 := by
  unfold tailWord_1114250
  simp only [CollatzResearch.WordTrace]
  refine ⟨10160009053317505898663051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27093357475513349063101469 10160009053317505898663051)
  ·
    refine ⟨15240013579976258847994577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10160009053317505898663051 15240013579976258847994577)
    ·
      refine ⟨11430010184982194135995933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15240013579976258847994577 11430010184982194135995933)
      ·
        refine ⟨4286253819368322800998475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11430010184982194135995933 4286253819368322800998475)
        ·
          refine ⟨6429380729052484201497713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4286253819368322800998475 6429380729052484201497713)
          ·
            refine ⟨4822035546789363151123285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6429380729052484201497713 4822035546789363151123285)
            ·
              refine ⟨28254114531968924713613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 4822035546789363151123285 28254114531968924713613)
              ·
                rfl

theorem cell21_1114250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 9].length) (baseStart_1114250 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1114250 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1114250 prefixEnd_1114250 := by exact prefixLift 1114250
  have htrace : WordTrace (prefixWord ++ tailWord_1114250) baseStart_1114250 baseEnd_1114250 := by
    simpa [prefixWord, tailWord_1114250, baseEnd_1114250] using wordTrace_append hprefix tailTrace_1114250
  have hstable : (prefixWord ++ tailWord_1114250).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1114250).length < 2 ^ (prefixWord ++ tailWord_1114250).sum := by decide
  have hdescent : baseEnd_1114250 < baseStart_1114250 := by decide
  rcases family_descends (prefixWord ++ tailWord_1114250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1114262 : List Nat := [5, 3, 2, 1, 1, 2, 2, 1, 4]
def baseStart_1114262 : Nat := 118140960795 + 1114262 * 2 ^ 59
def prefixEnd_1114262 : Nat := 4983230072969 + 3 ^ 40 * 1114262 * 2
def baseEnd_1114262 : Nat := 254289769351210968222493

theorem tailTrace_1114262 : CollatzResearch.WordTrace tailWord_1114262 prefixEnd_1114262 254289769351210968222493 := by
  unfold tailWord_1114262
  simp only [CollatzResearch.WordTrace]
  refine ⟨2540029618076659352755565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 27093649259484366429392693 2540029618076659352755565)
  ·
    refine ⟨952511106778747257283337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2540029618076659352755565 952511106778747257283337)
    ·
      refine ⟨714383330084060442962503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 952511106778747257283337 714383330084060442962503)
      ·
        refine ⟨1071574995126090664443755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 714383330084060442962503 1071574995126090664443755)
        ·
          refine ⟨1607362492689135996665633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1071574995126090664443755 1607362492689135996665633)
          ·
            refine ⟨1205521869516851997499225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1607362492689135996665633 1205521869516851997499225)
            ·
              refine ⟨904141402137638998124419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1205521869516851997499225 904141402137638998124419)
              ·
                refine ⟨1356212103206458497186629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 904141402137638998124419 1356212103206458497186629)
                ·
                  refine ⟨254289769351210968222493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1356212103206458497186629 254289769351210968222493)
                  ·
                    rfl

theorem cell21_1114262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 2, 2, 1, 4].length) (baseStart_1114262 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1114262 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1114262 prefixEnd_1114262 := by exact prefixLift 1114262
  have htrace : WordTrace (prefixWord ++ tailWord_1114262) baseStart_1114262 baseEnd_1114262 := by
    simpa [prefixWord, tailWord_1114262, baseEnd_1114262] using wordTrace_append hprefix tailTrace_1114262
  have hstable : (prefixWord ++ tailWord_1114262).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1114262).length < 2 ^ (prefixWord ++ tailWord_1114262).sum := by decide
  have hdescent : baseEnd_1114262 < baseStart_1114262 := by decide
  rcases family_descends (prefixWord ++ tailWord_1114262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1114270 : List Nat := [4, 3, 1, 1, 3, 1, 1, 3, 4]
def baseStart_1114270 : Nat := 118140960795 + 1114270 * 2 ^ 59
def prefixEnd_1114270 : Nat := 4983230072969 + 3 ^ 40 * 1114270 * 2
def baseEnd_1114270 : Nat := 254291595060204732089143

theorem tailTrace_1114270 : CollatzResearch.WordTrace tailWord_1114270 prefixEnd_1114270 254291595060204732089143 := by
  unfold tailWord_1114270
  simp only [CollatzResearch.WordTrace]
  refine ⟨5080095709149695876297533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 27093843782131711340253509 5080095709149695876297533)
  ·
    refine ⟨1905035890931135953611575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5080095709149695876297533 1905035890931135953611575)
    ·
      refine ⟨2857553836396703930417363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1905035890931135953611575 2857553836396703930417363)
      ·
        refine ⟨4286330754595055895626045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2857553836396703930417363 4286330754595055895626045)
        ·
          refine ⟨1607374032973145960859767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4286330754595055895626045 1607374032973145960859767)
          ·
            refine ⟨2411061049459718941289651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1607374032973145960859767 2411061049459718941289651)
            ·
              refine ⟨3616591574189578411934477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2411061049459718941289651 3616591574189578411934477)
              ·
                refine ⟨1356221840321091904475429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3616591574189578411934477 1356221840321091904475429)
                ·
                  refine ⟨254291595060204732089143, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1356221840321091904475429 254291595060204732089143)
                  ·
                    rfl

theorem cell21_1114270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 1, 1, 3, 4].length) (baseStart_1114270 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1114270 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1114270 prefixEnd_1114270 := by exact prefixLift 1114270
  have htrace : WordTrace (prefixWord ++ tailWord_1114270) baseStart_1114270 baseEnd_1114270 := by
    simpa [prefixWord, tailWord_1114270, baseEnd_1114270] using wordTrace_append hprefix tailTrace_1114270
  have hstable : (prefixWord ++ tailWord_1114270).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1114270).length < 2 ^ (prefixWord ++ tailWord_1114270).sum := by decide
  have hdescent : baseEnd_1114270 < baseStart_1114270 := by decide
  rcases family_descends (prefixWord ++ tailWord_1114270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1114371 : List Nat := [1, 1, 1, 3, 2, 3, 3, 1, 6]
def baseStart_1114371 : Nat := 118140960795 + 1114371 * 2 ^ 59
def prefixEnd_1114371 : Nat := 4983230072969 + 3 ^ 40 * 1114371 * 2
def baseEnd_1114371 : Nat := 254314644636251000905603

theorem tailTrace_1114371 : CollatzResearch.WordTrace tailWord_1114371 prefixEnd_1114371 254314644636251000905603 := by
  unfold tailWord_1114371
  simp only [CollatzResearch.WordTrace]
  refine ⟨40644449445831661259806967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27096299630554440839871311 40644449445831661259806967)
  ·
    refine ⟨60966674168747491889710451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40644449445831661259806967 60966674168747491889710451)
    ·
      refine ⟨91450011253121237834565677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60966674168747491889710451 91450011253121237834565677)
      ·
        refine ⟨34293754219920464187962129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 91450011253121237834565677 34293754219920464187962129)
        ·
          refine ⟨25720315664940348140971597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34293754219920464187962129 25720315664940348140971597)
          ·
            refine ⟨9645118374352630552864349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25720315664940348140971597 9645118374352630552864349)
            ·
              refine ⟨3616919390382236457324131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9645118374352630552864349 3616919390382236457324131)
              ·
                refine ⟨5425379085573354685986197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3616919390382236457324131 5425379085573354685986197)
                ·
                  refine ⟨254314644636251000905603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5425379085573354685986197 254314644636251000905603)
                  ·
                    rfl

theorem cell21_1114371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 3, 1, 6].length) (baseStart_1114371 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1114371 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1114371 prefixEnd_1114371 := by exact prefixLift 1114371
  have htrace : WordTrace (prefixWord ++ tailWord_1114371) baseStart_1114371 baseEnd_1114371 := by
    simpa [prefixWord, tailWord_1114371, baseEnd_1114371] using wordTrace_append hprefix tailTrace_1114371
  have hstable : (prefixWord ++ tailWord_1114371).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1114371).length < 2 ^ (prefixWord ++ tailWord_1114371).sum := by decide
  have hdescent : baseEnd_1114371 < baseStart_1114371 := by decide
  rcases family_descends (prefixWord ++ tailWord_1114371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1114408 : List Nat := [2, 1, 5, 1, 3, 2, 1, 3, 3]
def baseStart_1114408 : Nat := 118140960795 + 1114408 * 2 ^ 59
def prefixEnd_1114408 : Nat := 4983230072969 + 3 ^ 40 * 1114408 * 2
def baseEnd_1114408 : Nat := 254323088540347158788861

theorem tailTrace_1114408 : CollatzResearch.WordTrace tailWord_1114408 prefixEnd_1114408 254323088540347158788861 := by
  unfold tailWord_1114408
  simp only [CollatzResearch.WordTrace]
  refine ⟨20322899473348808289451939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27097199297798411052602585 20322899473348808289451939)
  ·
    refine ⟨30484349210023212434177909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20322899473348808289451939 30484349210023212434177909)
    ·
      refine ⟨2857907738439676165704179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 30484349210023212434177909 2857907738439676165704179)
      ·
        refine ⟨4286861607659514248556269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2857907738439676165704179 4286861607659514248556269)
        ·
          refine ⟨1607573102872317843208601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4286861607659514248556269 1607573102872317843208601)
          ·
            refine ⟨1205679827154238382406451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1607573102872317843208601 1205679827154238382406451)
            ·
              refine ⟨1808519740731357573609677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1205679827154238382406451 1808519740731357573609677)
              ·
                refine ⟨678194902774259090103629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1808519740731357573609677 678194902774259090103629)
                ·
                  refine ⟨254323088540347158788861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 678194902774259090103629 254323088540347158788861)
                  ·
                    rfl

theorem cell21_1114408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 2, 1, 3, 3].length) (baseStart_1114408 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1114408 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1114408 prefixEnd_1114408 := by exact prefixLift 1114408
  have htrace : WordTrace (prefixWord ++ tailWord_1114408) baseStart_1114408 baseEnd_1114408 := by
    simpa [prefixWord, tailWord_1114408, baseEnd_1114408] using wordTrace_append hprefix tailTrace_1114408
  have hstable : (prefixWord ++ tailWord_1114408).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1114408).length < 2 ^ (prefixWord ++ tailWord_1114408).sum := by decide
  have hdescent : baseEnd_1114408 < baseStart_1114408 := by decide
  rcases family_descends (prefixWord ++ tailWord_1114408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1114436 : List Nat := [2, 3, 4, 1, 2, 1, 2, 6]
def baseStart_1114436 : Nat := 118140960795 + 1114436 * 2 ^ 59
def prefixEnd_1114436 : Nat := 4983230072969 + 3 ^ 40 * 1114436 * 2
def baseEnd_1114436 : Nat := 84776492840608444107379

theorem tailTrace_1114436 : CollatzResearch.WordTrace tailWord_1114436 prefixEnd_1114436 84776492840608444107379 := by
  unfold tailWord_1114436
  simp only [CollatzResearch.WordTrace]
  refine ⟨20323410095298088680461581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27097880127064118240615441 20323410095298088680461581)
  ·
    refine ⟨7621278785736783255173093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20323410095298088680461581 7621278785736783255173093)
    ·
      refine ⟨1428989772325646860344955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7621278785736783255173093 1428989772325646860344955)
      ·
        refine ⟨2143484658488470290517433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1428989772325646860344955 2143484658488470290517433)
        ·
          refine ⟨1607613493866352717888075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2143484658488470290517433 1607613493866352717888075)
          ·
            refine ⟨2411420240799529076832113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1607613493866352717888075 2411420240799529076832113)
            ·
              refine ⟨1808565180599646807624085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2411420240799529076832113 1808565180599646807624085)
              ·
                refine ⟨84776492840608444107379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1808565180599646807624085 84776492840608444107379)
                ·
                  rfl

theorem cell21_1114436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 1, 2, 6].length) (baseStart_1114436 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1114436 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1114436 prefixEnd_1114436 := by exact prefixLift 1114436
  have htrace : WordTrace (prefixWord ++ tailWord_1114436) baseStart_1114436 baseEnd_1114436 := by
    simpa [prefixWord, tailWord_1114436, baseEnd_1114436] using wordTrace_append hprefix tailTrace_1114436
  have hstable : (prefixWord ++ tailWord_1114436).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1114436).length < 2 ^ (prefixWord ++ tailWord_1114436).sum := by decide
  have hdescent : baseEnd_1114436 < baseStart_1114436 := by decide
  rcases family_descends (prefixWord ++ tailWord_1114436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1114518 : List Nat := [5, 3, 1, 2, 1, 1, 2, 3, 3]
def baseStart_1114518 : Nat := 118140960795 + 1114518 * 2 ^ 59
def prefixEnd_1114518 : Nat := 4983230072969 + 3 ^ 40 * 1114518 * 2
def baseEnd_1114518 : Nat := 254348192039011411955303

theorem tailTrace_1114518 : CollatzResearch.WordTrace tailWord_1114518 prefixEnd_1114518 254348192039011411955303 := by
  unfold tailWord_1114518
  simp only [CollatzResearch.WordTrace]
  refine ⟨2540613186018694085338013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 27099873984199403576938805 2540613186018694085338013)
  ·
    refine ⟨952729944757010282001755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2540613186018694085338013 952729944757010282001755)
    ·
      refine ⟨1429094917135515423002633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 952729944757010282001755 1429094917135515423002633)
      ·
        refine ⟨1071821187851636567251975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1429094917135515423002633 1071821187851636567251975)
        ·
          refine ⟨1607731781777454850877963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1071821187851636567251975 1607731781777454850877963)
          ·
            refine ⟨2411597672666182276316945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1607731781777454850877963 2411597672666182276316945)
            ·
              refine ⟨1808698254499636707237709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2411597672666182276316945 1808698254499636707237709)
              ·
                refine ⟨678261845437363765214141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1808698254499636707237709 678261845437363765214141)
                ·
                  refine ⟨254348192039011411955303, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 678261845437363765214141 254348192039011411955303)
                  ·
                    rfl

theorem cell21_1114518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 1, 2, 3, 3].length) (baseStart_1114518 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1114518 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1114518 prefixEnd_1114518 := by exact prefixLift 1114518
  have htrace : WordTrace (prefixWord ++ tailWord_1114518) baseStart_1114518 baseEnd_1114518 := by
    simpa [prefixWord, tailWord_1114518, baseEnd_1114518] using wordTrace_append hprefix tailTrace_1114518
  have hstable : (prefixWord ++ tailWord_1114518).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1114518).length < 2 ^ (prefixWord ++ tailWord_1114518).sum := by decide
  have hdescent : baseEnd_1114518 < baseStart_1114518 := by decide
  rcases family_descends (prefixWord ++ tailWord_1114518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan21Incremental
