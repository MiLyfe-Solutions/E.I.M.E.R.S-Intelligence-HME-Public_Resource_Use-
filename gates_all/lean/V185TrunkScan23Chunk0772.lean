import V185TrunkScan23Chunk0771

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_4565849 : List Nat := [1, 2, 1, 2, 2, 5, 3, 2, 1, 4]
def baseStart_4565849 : Nat := 118140960795 + 4565849 * 2 ^ 59
def prefixEnd_4565849 : Nat := 4983230072969 + 3 ^ 40 * 4565849 * 2
def baseEnd_4565849 : Nat := 781491710950137276163183

theorem tailTrace_4565849 : CollatzResearch.WordTrace tailWord_4565849 prefixEnd_4565849 781491710950137276163183 := by
  unfold tailWord_4565849
  simp only [CollatzResearch.WordTrace]
  refine ⟨166530194035716332772460601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111020129357144221848307067 166530194035716332772460601)
  ·
    refine ⟨124897645526787249579345451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 166530194035716332772460601 124897645526787249579345451)
    ·
      refine ⟨187346468290180874369018177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 124897645526787249579345451 187346468290180874369018177)
      ·
        refine ⟨140509851217635655776763633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 187346468290180874369018177 140509851217635655776763633)
        ·
          refine ⟨105382388413226741832572725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 140509851217635655776763633 105382388413226741832572725)
          ·
            refine ⟨9879598913740007046803693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 105382388413226741832572725 9879598913740007046803693)
            ·
              refine ⟨3704849592652502642551385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9879598913740007046803693 3704849592652502642551385)
              ·
                refine ⟨2778637194489376981913539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3704849592652502642551385 2778637194489376981913539)
                ·
                  refine ⟨4167955791734065472870309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2778637194489376981913539 4167955791734065472870309)
                  ·
                    refine ⟨781491710950137276163183, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4167955791734065472870309 781491710950137276163183)
                    ·
                      rfl

theorem cell23_4565849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 5, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 5, 3, 2, 1, 4].length) (baseStart_4565849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4565849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4565849 prefixEnd_4565849 := by exact prefixLift 4565849
  have htrace : WordTrace (prefixWord ++ tailWord_4565849) baseStart_4565849 baseEnd_4565849 := by
    simpa [prefixWord, tailWord_4565849, baseEnd_4565849] using wordTrace_append hprefix tailTrace_4565849
  have hstable : (prefixWord ++ tailWord_4565849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4565849).length < 2 ^ (prefixWord ++ tailWord_4565849).sum := by decide
  have hdescent : baseEnd_4565849 < baseStart_4565849 := by decide
  rcases family_descends (prefixWord ++ tailWord_4565849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4565875 : List Nat := [1, 1, 1, 2, 2, 1, 7, 2, 1, 5]
def baseStart_4565875 : Nat := 118140960795 + 4565875 * 2 ^ 59
def prefixEnd_4565875 : Nat := 4983230072969 + 3 ^ 40 * 4565875 * 2
def baseEnd_4565875 : Nat := 781496161115809575588143

theorem tailTrace_4565875 : CollatzResearch.WordTrace tailWord_4565875 prefixEnd_4565875 781496161115809575588143 := by
  unfold tailWord_4565875
  simp only [CollatzResearch.WordTrace]
  refine ⟨166531142333622139212907079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111020761555748092808604719 166531142333622139212907079)
  ·
    refine ⟨249796713500433208819360619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 166531142333622139212907079 249796713500433208819360619)
    ·
      refine ⟨374695070250649813229040929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 249796713500433208819360619 374695070250649813229040929)
      ·
        refine ⟨281021302687987359921780697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 374695070250649813229040929 281021302687987359921780697)
        ·
          refine ⟨210765977015990519941335523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 281021302687987359921780697 210765977015990519941335523)
          ·
            refine ⟨316148965523985779912003285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 210765977015990519941335523 316148965523985779912003285)
            ·
              refine ⟨7409741379468416716687577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 316148965523985779912003285 7409741379468416716687577)
              ·
                refine ⟨5557306034601312537515683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7409741379468416716687577 5557306034601312537515683)
                ·
                  refine ⟨8335959051901968806273525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5557306034601312537515683 8335959051901968806273525)
                  ·
                    refine ⟨781496161115809575588143, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8335959051901968806273525 781496161115809575588143)
                    ·
                      rfl

theorem cell23_4565875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 7, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 7, 2, 1, 5].length) (baseStart_4565875 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4565875 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4565875 prefixEnd_4565875 := by exact prefixLift 4565875
  have htrace : WordTrace (prefixWord ++ tailWord_4565875) baseStart_4565875 baseEnd_4565875 := by
    simpa [prefixWord, tailWord_4565875, baseEnd_4565875] using wordTrace_append hprefix tailTrace_4565875
  have hstable : (prefixWord ++ tailWord_4565875).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4565875).length < 2 ^ (prefixWord ++ tailWord_4565875).sum := by decide
  have hdescent : baseEnd_4565875 < baseStart_4565875 := by decide
  rcases family_descends (prefixWord ++ tailWord_4565875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4565922 : List Nat := [3, 3, 1, 2, 2, 2, 2, 1, 1, 6]
def baseStart_4565922 : Nat := 118140960795 + 4565922 * 2 ^ 59
def prefixEnd_4565922 : Nat := 4983230072969 + 3 ^ 40 * 4565922 * 2
def baseEnd_4565922 : Nat := 781504205646063347625571

theorem tailTrace_4565922 : CollatzResearch.WordTrace tailWord_4565922 prefixEnd_4565922 781504205646063347625571 := by
  unfold tailWord_4565922
  simp only [CollatzResearch.WordTrace]
  refine ⟨41633214141112966559967005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 111021904376301244159912013 41633214141112966559967005)
  ·
    refine ⟨15612455302917362459987627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41633214141112966559967005 15612455302917362459987627)
    ·
      refine ⟨23418682954376043689981441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15612455302917362459987627 23418682954376043689981441)
      ·
        refine ⟨17564012215782032767486081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23418682954376043689981441 17564012215782032767486081)
        ·
          refine ⟨13173009161836524575614561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17564012215782032767486081 13173009161836524575614561)
          ·
            refine ⟨9879756871377393431710921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13173009161836524575614561 9879756871377393431710921)
            ·
              refine ⟨7409817653533045073783191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9879756871377393431710921 7409817653533045073783191)
              ·
                refine ⟨11114726480299567610674787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7409817653533045073783191 11114726480299567610674787)
                ·
                  refine ⟨16672089720449351416012181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11114726480299567610674787 16672089720449351416012181)
                  ·
                    refine ⟨781504205646063347625571, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16672089720449351416012181 781504205646063347625571)
                    ·
                      rfl

theorem cell23_4565922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 2, 2, 1, 1, 6].length) (baseStart_4565922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4565922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4565922 prefixEnd_4565922 := by exact prefixLift 4565922
  have htrace : WordTrace (prefixWord ++ tailWord_4565922) baseStart_4565922 baseEnd_4565922 := by
    simpa [prefixWord, tailWord_4565922, baseEnd_4565922] using wordTrace_append hprefix tailTrace_4565922
  have hstable : (prefixWord ++ tailWord_4565922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4565922).length < 2 ^ (prefixWord ++ tailWord_4565922).sum := by decide
  have hdescent : baseEnd_4565922 < baseStart_4565922 := by decide
  rcases family_descends (prefixWord ++ tailWord_4565922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4565933 : List Nat := [1, 5, 2, 3, 1, 2, 1, 1, 2, 3, 2]
def baseStart_4565933 : Nat := 118140960795 + 4565933 * 2 ^ 59
def prefixEnd_4565933 : Nat := 4983230072969 + 3 ^ 40 * 4565933 * 2
def baseEnd_4565933 : Nat := 2344518265225389499839163

theorem tailTrace_4565933 : CollatzResearch.WordTrace tailWord_4565933 prefixEnd_4565933 2344518265225389499839163 := by
  unfold tailWord_4565933
  simp only [CollatzResearch.WordTrace]
  refine ⟨166533257767412015118518453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111022171844941343412345635 166533257767412015118518453)
  ·
    refine ⟨15612492915694876417361105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 166533257767412015118518453 15612492915694876417361105)
    ·
      refine ⟨11709369686771157313020829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15612492915694876417361105 11709369686771157313020829)
      ·
        refine ⟨4391013632539183992382811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11709369686771157313020829 4391013632539183992382811)
        ·
          refine ⟨6586520448808775988574217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4391013632539183992382811 6586520448808775988574217)
          ·
            refine ⟨4939890336606581991430663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6586520448808775988574217 4939890336606581991430663)
            ·
              refine ⟨7409835504909872987145995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4939890336606581991430663 7409835504909872987145995)
              ·
                refine ⟨11114753257364809480718993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7409835504909872987145995 11114753257364809480718993)
                ·
                  refine ⟨8336064943023607110539245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11114753257364809480718993 8336064943023607110539245)
                  ·
                    refine ⟨3126024353633852666452217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8336064943023607110539245 3126024353633852666452217)
                    ·
                      refine ⟨2344518265225389499839163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3126024353633852666452217 2344518265225389499839163)
                      ·
                        rfl

theorem cell23_4565933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 2, 1, 1, 2, 3, 2].length) (baseStart_4565933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4565933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4565933 prefixEnd_4565933 := by exact prefixLift 4565933
  have htrace : WordTrace (prefixWord ++ tailWord_4565933) baseStart_4565933 baseEnd_4565933 := by
    simpa [prefixWord, tailWord_4565933, baseEnd_4565933] using wordTrace_append hprefix tailTrace_4565933
  have hstable : (prefixWord ++ tailWord_4565933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4565933).length < 2 ^ (prefixWord ++ tailWord_4565933).sum := by decide
  have hdescent : baseEnd_4565933 < baseStart_4565933 := by decide
  rcases family_descends (prefixWord ++ tailWord_4565933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4565946 : List Nat := [3, 1, 1, 1, 2, 1, 6, 3, 1, 2, 2]
def baseStart_4565946 : Nat := 118140960795 + 4565946 * 2 ^ 59
def prefixEnd_4565946 : Nat := 4983230072969 + 3 ^ 40 * 4565946 * 2
def baseEnd_4565946 : Nat := 2344524940473897948976603

theorem tailTrace_4565946 : CollatzResearch.WordTrace tailWord_4565946 prefixEnd_4565946 2344524940473897948976603 := by
  unfold tailWord_4565946
  simp only [CollatzResearch.WordTrace]
  refine ⟨41633432979091229584685423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 111022487944243278892494461 41633432979091229584685423)
  ·
    refine ⟨62450149468636844377028135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41633432979091229584685423 62450149468636844377028135)
    ·
      refine ⟨93675224202955266565542203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62450149468636844377028135 93675224202955266565542203)
      ·
        refine ⟨140512836304432899848313305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93675224202955266565542203 140512836304432899848313305)
        ·
          refine ⟨105384627228324674886234979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 140512836304432899848313305 105384627228324674886234979)
          ·
            refine ⟨158076940842487012329352469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 105384627228324674886234979 158076940842487012329352469)
            ·
              refine ⟨7409856601991578702938397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 158076940842487012329352469 7409856601991578702938397)
              ·
                refine ⟨2778696225746842013601899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7409856601991578702938397 2778696225746842013601899)
                ·
                  refine ⟨4168044338620263020402849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2778696225746842013601899 4168044338620263020402849)
                  ·
                    refine ⟨3126033253965197265302137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4168044338620263020402849 3126033253965197265302137)
                    ·
                      refine ⟨2344524940473897948976603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3126033253965197265302137 2344524940473897948976603)
                      ·
                        rfl

theorem cell23_4565946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 6, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 6, 3, 1, 2, 2].length) (baseStart_4565946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4565946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4565946 prefixEnd_4565946 := by exact prefixLift 4565946
  have htrace : WordTrace (prefixWord ++ tailWord_4565946) baseStart_4565946 baseEnd_4565946 := by
    simpa [prefixWord, tailWord_4565946, baseEnd_4565946] using wordTrace_append hprefix tailTrace_4565946
  have hstable : (prefixWord ++ tailWord_4565946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4565946).length < 2 ^ (prefixWord ++ tailWord_4565946).sum := by decide
  have hdescent : baseEnd_4565946 < baseStart_4565946 := by decide
  rcases family_descends (prefixWord ++ tailWord_4565946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4565949 : List Nat := [1, 4, 1, 2, 4, 1, 1, 3, 1, 2, 3]
def baseStart_4565949 : Nat := 118140960795 + 4565949 * 2 ^ 59
def prefixEnd_4565949 : Nat := 4983230072969 + 3 ^ 40 * 4565949 * 2
def baseEnd_4565949 : Nat := 2344526480915861437239089

theorem tailTrace_4565949 : CollatzResearch.WordTrace tailWord_4565949 prefixEnd_4565949 2344526480915861437239089 := by
  unfold tailWord_4565949
  simp only [CollatzResearch.WordTrace]
  refine ⟨166533841335354049851100901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111022560890236033234067267 166533841335354049851100901)
  ·
    refine ⟨31225095250378884347081419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 166533841335354049851100901 31225095250378884347081419)
    ·
      refine ⟨46837642875568326520622129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31225095250378884347081419 46837642875568326520622129)
      ·
        refine ⟨35128232156676244890466597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46837642875568326520622129 35128232156676244890466597)
        ·
          refine ⟨6586543529376795916962487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 35128232156676244890466597 6586543529376795916962487)
          ·
            refine ⟨9879815294065193875443731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6586543529376795916962487 9879815294065193875443731)
            ·
              refine ⟨14819722941097790813165597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9879815294065193875443731 14819722941097790813165597)
              ·
                refine ⟨5557396102911671554937099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14819722941097790813165597 5557396102911671554937099)
                ·
                  refine ⟨8336094154367507332405649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5557396102911671554937099 8336094154367507332405649)
                  ·
                    refine ⟨6252070615775630499304237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8336094154367507332405649 6252070615775630499304237)
                    ·
                      refine ⟨2344526480915861437239089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6252070615775630499304237 2344526480915861437239089)
                      ·
                        rfl

theorem cell23_4565949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 1, 1, 3, 1, 2, 3].length) (baseStart_4565949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4565949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4565949 prefixEnd_4565949 := by exact prefixLift 4565949
  have htrace : WordTrace (prefixWord ++ tailWord_4565949) baseStart_4565949 baseEnd_4565949 := by
    simpa [prefixWord, tailWord_4565949, baseEnd_4565949] using wordTrace_append hprefix tailTrace_4565949
  have hstable : (prefixWord ++ tailWord_4565949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4565949).length < 2 ^ (prefixWord ++ tailWord_4565949).sum := by decide
  have hdescent : baseEnd_4565949 < baseStart_4565949 := by decide
  rcases family_descends (prefixWord ++ tailWord_4565949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4566006 : List Nat := [5, 1, 1, 1, 3, 1, 2, 3, 1, 3, 2]
def baseStart_4566006 : Nat := 118140960795 + 4566006 * 2 ^ 59
def prefixEnd_4566006 : Nat := 4983230072969 + 3 ^ 40 * 4566006 * 2
def baseEnd_4566006 : Nat := 2344555749313167714226327

theorem tailTrace_4566006 : CollatzResearch.WordTrace tailWord_4566006 prefixEnd_4566006 2344555749313167714226327 := by
  unfold tailWord_4566006
  simp only [CollatzResearch.WordTrace]
  refine ⟨10408495018509221786620367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 111023946864098365723950581 10408495018509221786620367)
  ·
    refine ⟨15612742527763832679930551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10408495018509221786620367 15612742527763832679930551)
    ·
      refine ⟨23419113791645749019895827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15612742527763832679930551 23419113791645749019895827)
      ·
        refine ⟨35128670687468623529843741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23419113791645749019895827 35128670687468623529843741)
        ·
          refine ⟨13173251507800733823691403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35128670687468623529843741 13173251507800733823691403)
          ·
            refine ⟨19759877261701100735537105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13173251507800733823691403 19759877261701100735537105)
            ·
              refine ⟨14819907946275825551652829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19759877261701100735537105 14819907946275825551652829)
              ·
                refine ⟨5557465479853434581869811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14819907946275825551652829 5557465479853434581869811)
                ·
                  refine ⟨8336198219780151872804717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5557465479853434581869811 8336198219780151872804717)
                  ·
                    refine ⟨3126074332417556952301769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8336198219780151872804717 3126074332417556952301769)
                    ·
                      refine ⟨2344555749313167714226327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3126074332417556952301769 2344555749313167714226327)
                      ·
                        rfl

theorem cell23_4566006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 2, 3, 1, 3, 2].length) (baseStart_4566006 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4566006 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4566006 prefixEnd_4566006 := by exact prefixLift 4566006
  have htrace : WordTrace (prefixWord ++ tailWord_4566006) baseStart_4566006 baseEnd_4566006 := by
    simpa [prefixWord, tailWord_4566006, baseEnd_4566006] using wordTrace_append hprefix tailTrace_4566006
  have hstable : (prefixWord ++ tailWord_4566006).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4566006).length < 2 ^ (prefixWord ++ tailWord_4566006).sum := by decide
  have hdescent : baseEnd_4566006 < baseStart_4566006 := by decide
  rcases family_descends (prefixWord ++ tailWord_4566006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4566035 : List Nat := [1, 1, 1, 2, 1, 4, 1, 3, 1, 5, 3]
def baseStart_4566035 : Nat := 118140960795 + 4566035 * 2 ^ 59
def prefixEnd_4566035 : Nat := 4983230072969 + 3 ^ 40 * 4566035 * 2
def baseEnd_4566035 : Nat := 2344570640252148100763693

theorem tailTrace_4566035 : CollatzResearch.WordTrace tailWord_4566035 prefixEnd_4566035 2344570640252148100763693 := by
  unfold tailWord_4566035
  simp only [CollatzResearch.WordTrace]
  refine ⟨166536978013042486538731559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111024652008694991025821039 166536978013042486538731559)
  ·
    refine ⟨249805467019563729808097339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 166536978013042486538731559 249805467019563729808097339)
    ·
      refine ⟨374708200529345594712146009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 249805467019563729808097339 374708200529345594712146009)
      ·
        refine ⟨281031150397009196034109507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 374708200529345594712146009 281031150397009196034109507)
        ·
          refine ⟨421546725595513794051164261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 281031150397009196034109507 421546725595513794051164261)
          ·
            refine ⟨79040011049158836384593299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 421546725595513794051164261 79040011049158836384593299)
            ·
              refine ⟨118560016573738254576889949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 79040011049158836384593299 118560016573738254576889949)
              ·
                refine ⟨44460006215151845466333731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 118560016573738254576889949 44460006215151845466333731)
                ·
                  refine ⟨66690009322727768199500597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 44460006215151845466333731 66690009322727768199500597)
                  ·
                    refine ⟨6252188374005728268703181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 66690009322727768199500597 6252188374005728268703181)
                    ·
                      refine ⟨2344570640252148100763693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6252188374005728268703181 2344570640252148100763693)
                      ·
                        rfl

theorem cell23_4566035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 3, 1, 5, 3].length) (baseStart_4566035 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4566035 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4566035 prefixEnd_4566035 := by exact prefixLift 4566035
  have htrace : WordTrace (prefixWord ++ tailWord_4566035) baseStart_4566035 baseEnd_4566035 := by
    simpa [prefixWord, tailWord_4566035, baseEnd_4566035] using wordTrace_append hprefix tailTrace_4566035
  have hstable : (prefixWord ++ tailWord_4566035).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4566035).length < 2 ^ (prefixWord ++ tailWord_4566035).sum := by decide
  have hdescent : baseEnd_4566035 < baseStart_4566035 := by decide
  rcases family_descends (prefixWord ++ tailWord_4566035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4566065 : List Nat := [1, 2, 2, 3, 1, 2, 1, 1, 3, 2, 5]
def baseStart_4566065 : Nat := 118140960795 + 4566065 * 2 ^ 59
def prefixEnd_4566065 : Nat := 4983230072969 + 3 ^ 40 * 4566065 * 2
def baseEnd_4566065 : Nat := 2344586044671782983388555

theorem tailTrace_4566065 : CollatzResearch.WordTrace tailWord_4566065 prefixEnd_4566065 2344586044671782983388555 := by
  unfold tailWord_4566065
  simp only [CollatzResearch.WordTrace]
  refine ⟨166538072202933801662323649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111025381468622534441549099 166538072202933801662323649)
  ·
    refine ⟨124903554152200351246742737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 166538072202933801662323649 124903554152200351246742737)
    ·
      refine ⟨93677665614150263435057053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 124903554152200351246742737 93677665614150263435057053)
      ·
        refine ⟨35129124605306348788146395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 93677665614150263435057053 35129124605306348788146395)
        ·
          refine ⟨52693686907959523182219593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35129124605306348788146395 52693686907959523182219593)
          ·
            refine ⟨39520265180969642386664695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52693686907959523182219593 39520265180969642386664695)
            ·
              refine ⟨59280397771454463579997043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39520265180969642386664695 59280397771454463579997043)
              ·
                refine ⟨88920596657181695369995565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 59280397771454463579997043 88920596657181695369995565)
                ·
                  refine ⟨33345223746443135763748337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 88920596657181695369995565 33345223746443135763748337)
                  ·
                    refine ⟨25008917809832351822811253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 33345223746443135763748337 25008917809832351822811253)
                    ·
                      refine ⟨2344586044671782983388555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25008917809832351822811253 2344586044671782983388555)
                      ·
                        rfl

theorem cell23_4566065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 1, 1, 3, 2, 5].length) (baseStart_4566065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4566065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4566065 prefixEnd_4566065 := by exact prefixLift 4566065
  have htrace : WordTrace (prefixWord ++ tailWord_4566065) baseStart_4566065 baseEnd_4566065 := by
    simpa [prefixWord, tailWord_4566065, baseEnd_4566065] using wordTrace_append hprefix tailTrace_4566065
  have hstable : (prefixWord ++ tailWord_4566065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4566065).length < 2 ^ (prefixWord ++ tailWord_4566065).sum := by decide
  have hdescent : baseEnd_4566065 < baseStart_4566065 := by decide
  rcases family_descends (prefixWord ++ tailWord_4566065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4566072 : List Nat := [2, 1, 2, 1, 5, 1, 2, 2, 2, 5]
def baseStart_4566072 : Nat := 118140960795 + 4566072 * 2 ^ 59
def prefixEnd_4566072 : Nat := 4983230072969 + 3 ^ 40 * 4566072 * 2
def baseEnd_4566072 : Nat := 781529879678788152000341

theorem tailTrace_4566072 : CollatzResearch.WordTrace tailWord_4566072 prefixEnd_4566072 781529879678788152000341 := by
  unfold tailWord_4566072
  simp only [CollatzResearch.WordTrace]
  refine ⟨83269163756954220928914235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111025551675938961238552313 83269163756954220928914235)
  ·
    refine ⟨124903745635431331393371353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83269163756954220928914235 124903745635431331393371353)
    ·
      refine ⟨93677809226573498545028515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 124903745635431331393371353 93677809226573498545028515)
      ·
        refine ⟨140516713839860247817542773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93677809226573498545028515 140516713839860247817542773)
        ·
          refine ⟨13173441922486898232894635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 140516713839860247817542773 13173441922486898232894635)
          ·
            refine ⟨19760162883730347349341953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13173441922486898232894635 19760162883730347349341953)
            ·
              refine ⟨14820122162797760512006465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19760162883730347349341953 14820122162797760512006465)
              ·
                refine ⟨11115091622098320384004849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14820122162797760512006465 11115091622098320384004849)
                ·
                  refine ⟨8336318716573740288003637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11115091622098320384004849 8336318716573740288003637)
                  ·
                    refine ⟨781529879678788152000341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8336318716573740288003637 781529879678788152000341)
                    ·
                      rfl

theorem cell23_4566072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 2, 2, 2, 5].length) (baseStart_4566072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4566072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4566072 prefixEnd_4566072 := by exact prefixLift 4566072
  have htrace : WordTrace (prefixWord ++ tailWord_4566072) baseStart_4566072 baseEnd_4566072 := by
    simpa [prefixWord, tailWord_4566072, baseEnd_4566072] using wordTrace_append hprefix tailTrace_4566072
  have hstable : (prefixWord ++ tailWord_4566072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4566072).length < 2 ^ (prefixWord ++ tailWord_4566072).sum := by decide
  have hdescent : baseEnd_4566072 < baseStart_4566072 := by decide
  rcases family_descends (prefixWord ++ tailWord_4566072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4566076 : List Nat := [2, 2, 2, 2, 2, 4, 2, 2, 5]
def baseStart_4566076 : Nat := 118140960795 + 4566076 * 2 ^ 59
def prefixEnd_4566076 : Nat := 4983230072969 + 3 ^ 40 * 4566076 * 2
def baseEnd_4566076 : Nat := 260510188106553604483445

theorem tailTrace_4566076 : CollatzResearch.WordTrace tailWord_4566076 prefixEnd_4566076 260510188106553604483445 := by
  unfold tailWord_4566076
  simp only [CollatzResearch.WordTrace]
  refine ⟨83269236702946975270487041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111025648937262633693982721 83269236702946975270487041)
  ·
    refine ⟨62451927527210231452865281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83269236702946975270487041 62451927527210231452865281)
    ·
      refine ⟨46838945645407673589648961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62451927527210231452865281 46838945645407673589648961)
      ·
        refine ⟨35129209234055755192236721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46838945645407673589648961 35129209234055755192236721)
        ·
          refine ⟨26346906925541816394177541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35129209234055755192236721 26346906925541816394177541)
          ·
            refine ⟨4940045048539090573908289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 26346906925541816394177541 4940045048539090573908289)
            ·
              refine ⟨3705033786404317930431217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4940045048539090573908289 3705033786404317930431217)
              ·
                refine ⟨2778775339803238447823413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3705033786404317930431217 2778775339803238447823413)
                ·
                  refine ⟨260510188106553604483445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2778775339803238447823413 260510188106553604483445)
                  ·
                    rfl

theorem cell23_4566076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 4, 2, 2, 5].length) (baseStart_4566076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4566076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4566076 prefixEnd_4566076 := by exact prefixLift 4566076
  have htrace : WordTrace (prefixWord ++ tailWord_4566076) baseStart_4566076 baseEnd_4566076 := by
    simpa [prefixWord, tailWord_4566076, baseEnd_4566076] using wordTrace_append hprefix tailTrace_4566076
  have hstable : (prefixWord ++ tailWord_4566076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4566076).length < 2 ^ (prefixWord ++ tailWord_4566076).sum := by decide
  have hdescent : baseEnd_4566076 < baseStart_4566076 := by decide
  rcases family_descends (prefixWord ++ tailWord_4566076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4566086 : List Nat := [6, 1, 1, 1, 1, 3, 1, 1, 2, 3, 3]
def baseStart_4566086 : Nat := 118140960795 + 4566086 * 2 ^ 59
def prefixEnd_4566086 : Nat := 4983230072969 + 3 ^ 40 * 4566086 * 2
def baseEnd_4566086 : Nat := 2344596827765527401225959

theorem tailTrace_4566086 : CollatzResearch.WordTrace tailWord_4566086 prefixEnd_4566086 2344596827765527401225959 := by
  unfold tailWord_4566086
  simp only [CollatzResearch.WordTrace]
  refine ⟨5204338691745553820276191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 111025892090571814832558741 5204338691745553820276191)
  ·
    refine ⟨7806508037618330730414287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5204338691745553820276191 7806508037618330730414287)
    ·
      refine ⟨11709762056427496095621431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7806508037618330730414287 11709762056427496095621431)
      ·
        refine ⟨17564643084641244143432147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11709762056427496095621431 17564643084641244143432147)
        ·
          refine ⟨26346964626961866215148221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17564643084641244143432147 26346964626961866215148221)
          ·
            refine ⟨9880111735110699830680583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26346964626961866215148221 9880111735110699830680583)
            ·
              refine ⟨14820167602666049746020875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9880111735110699830680583 14820167602666049746020875)
              ·
                refine ⟨22230251403999074619031313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14820167602666049746020875 22230251403999074619031313)
                ·
                  refine ⟨16672688552999305964273485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22230251403999074619031313 16672688552999305964273485)
                  ·
                    refine ⟨6252258207374739736602557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16672688552999305964273485 6252258207374739736602557)
                    ·
                      refine ⟨2344596827765527401225959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6252258207374739736602557 2344596827765527401225959)
                      ·
                        rfl

theorem cell23_4566086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 3, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 3, 1, 1, 2, 3, 3].length) (baseStart_4566086 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4566086 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4566086 prefixEnd_4566086 := by exact prefixLift 4566086
  have htrace : WordTrace (prefixWord ++ tailWord_4566086) baseStart_4566086 baseEnd_4566086 := by
    simpa [prefixWord, tailWord_4566086, baseEnd_4566086] using wordTrace_append hprefix tailTrace_4566086
  have hstable : (prefixWord ++ tailWord_4566086).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4566086).length < 2 ^ (prefixWord ++ tailWord_4566086).sum := by decide
  have hdescent : baseEnd_4566086 < baseStart_4566086 := by decide
  rcases family_descends (prefixWord ++ tailWord_4566086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4566105 : List Nat := [1, 2, 1, 2, 2, 1, 2, 1, 1, 6, 4]
def baseStart_4566105 : Nat := 118140960795 + 4566105 * 2 ^ 59
def prefixEnd_4566105 : Nat := 4983230072969 + 3 ^ 40 * 4566105 * 2
def baseEnd_4566105 : Nat := 2344606583897962826888371

theorem tailTrace_4566105 : CollatzResearch.WordTrace tailWord_4566105 prefixEnd_4566105 2344606583897962826888371 := by
  unfold tailWord_4566105
  simp only [CollatzResearch.WordTrace]
  refine ⟨166539531122788888493779769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111026354081859258995853179 166539531122788888493779769)
  ·
    refine ⟨124904648342091666370334827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 166539531122788888493779769 124904648342091666370334827)
    ·
      refine ⟨187356972513137499555502241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 124904648342091666370334827 187356972513137499555502241)
      ·
        refine ⟨140517729384853124666626681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 187356972513137499555502241 140517729384853124666626681)
        ·
          refine ⟨105388297038639843499970011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 140517729384853124666626681 105388297038639843499970011)
          ·
            refine ⟨158082445557959765249955017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 105388297038639843499970011 158082445557959765249955017)
            ·
              refine ⟨118561834168469823937466263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 158082445557959765249955017 118561834168469823937466263)
              ·
                refine ⟨177842751252704735906199395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 118561834168469823937466263 177842751252704735906199395)
                ·
                  refine ⟨266764126879057103859299093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 177842751252704735906199395 266764126879057103859299093)
                  ·
                    refine ⟨12504568447455801743404645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 266764126879057103859299093 12504568447455801743404645)
                    ·
                      refine ⟨2344606583897962826888371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12504568447455801743404645 2344606583897962826888371)
                      ·
                        rfl

theorem cell23_4566105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 1, 1, 6, 4].length) (baseStart_4566105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4566105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4566105 prefixEnd_4566105 := by exact prefixLift 4566105
  have htrace : WordTrace (prefixWord ++ tailWord_4566105) baseStart_4566105 baseEnd_4566105 := by
    simpa [prefixWord, tailWord_4566105, baseEnd_4566105] using wordTrace_append hprefix tailTrace_4566105
  have hstable : (prefixWord ++ tailWord_4566105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4566105).length < 2 ^ (prefixWord ++ tailWord_4566105).sum := by decide
  have hdescent : baseEnd_4566105 < baseStart_4566105 := by decide
  rcases family_descends (prefixWord ++ tailWord_4566105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4566112 : List Nat := [2, 1, 1, 3, 2, 2, 3, 1, 1, 4, 3]
def baseStart_4566112 : Nat := 118140960795 + 4566112 * 2 ^ 59
def prefixEnd_4566112 : Nat := 4983230072969 + 3 ^ 40 * 4566112 * 2
def baseEnd_4566112 : Nat := 2344610178262544299500839

theorem tailTrace_4566112 : CollatzResearch.WordTrace tailWord_4566112 prefixEnd_4566112 2344610178262544299500839 := by
  unfold tailWord_4566112
  simp only [CollatzResearch.WordTrace]
  refine ⟨83269893216881764344642295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111026524289175685792856393 83269893216881764344642295)
  ·
    refine ⟨124904839825322646516963443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83269893216881764344642295 124904839825322646516963443)
    ·
      refine ⟨187357259737983969775445165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 124904839825322646516963443 187357259737983969775445165)
      ·
        refine ⟨70258972401743988665791937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 187357259737983969775445165 70258972401743988665791937)
        ·
          refine ⟨52694229301307991499343953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 70258972401743988665791937 52694229301307991499343953)
          ·
            refine ⟨39520671975980993624507965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52694229301307991499343953 39520671975980993624507965)
            ·
              refine ⟨14820251990992872609190487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 39520671975980993624507965 14820251990992872609190487)
              ·
                refine ⟨22230377986489308913785731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14820251990992872609190487 22230377986489308913785731)
                ·
                  refine ⟨33345566979733963370678597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22230377986489308913785731 33345566979733963370678597)
                  ·
                    refine ⟨6252293808700118132002237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 33345566979733963370678597 6252293808700118132002237)
                    ·
                      refine ⟨2344610178262544299500839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6252293808700118132002237 2344610178262544299500839)
                      ·
                        rfl

theorem cell23_4566112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 3, 1, 1, 4, 3].length) (baseStart_4566112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4566112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4566112 prefixEnd_4566112 := by exact prefixLift 4566112
  have htrace : WordTrace (prefixWord ++ tailWord_4566112) baseStart_4566112 baseEnd_4566112 := by
    simpa [prefixWord, tailWord_4566112, baseEnd_4566112] using wordTrace_append hprefix tailTrace_4566112
  have hstable : (prefixWord ++ tailWord_4566112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4566112).length < 2 ^ (prefixWord ++ tailWord_4566112).sum := by decide
  have hdescent : baseEnd_4566112 < baseStart_4566112 := by decide
  rcases family_descends (prefixWord ++ tailWord_4566112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4566115 : List Nat := [1, 1, 1, 5, 1, 1, 1, 4, 8]
def baseStart_4566115 : Nat := 118140960795 + 4566115 * 2 ^ 59
def prefixEnd_4566115 : Nat := 4983230072969 + 3 ^ 40 * 4566115 * 2
def baseEnd_4566115 : Nat := 260512413189389754195925

theorem tailTrace_4566115 : CollatzResearch.WordTrace tailWord_4566115 prefixEnd_4566115 260512413189389754195925 := by
  unfold tailWord_4566115
  simp only [CollatzResearch.WordTrace]
  refine ⟨166539895852752660201643799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111026597235168440134429199 166539895852752660201643799)
  ·
    refine ⟨249809843779128990302465699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 166539895852752660201643799 249809843779128990302465699)
    ·
      refine ⟨374714765668693485453698549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 249809843779128990302465699 374714765668693485453698549)
      ·
        refine ⟨35129509281440014261284239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 374714765668693485453698549 35129509281440014261284239)
        ·
          refine ⟨52694263922160021391926359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35129509281440014261284239 52694263922160021391926359)
          ·
            refine ⟨79041395883240032087889539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52694263922160021391926359 79041395883240032087889539)
            ·
              refine ⟨118562093824860048131834309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 79041395883240032087889539 118562093824860048131834309)
              ·
                refine ⟨22230392592161259024718933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 118562093824860048131834309 22230392592161259024718933)
                ·
                  refine ⟨260512413189389754195925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 22230392592161259024718933 260512413189389754195925)
                  ·
                    rfl

theorem cell23_4566115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 4, 8].length) (baseStart_4566115 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4566115 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4566115 prefixEnd_4566115 := by exact prefixLift 4566115
  have htrace : WordTrace (prefixWord ++ tailWord_4566115) baseStart_4566115 baseEnd_4566115 := by
    simpa [prefixWord, tailWord_4566115, baseEnd_4566115] using wordTrace_append hprefix tailTrace_4566115
  have hstable : (prefixWord ++ tailWord_4566115).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4566115).length < 2 ^ (prefixWord ++ tailWord_4566115).sum := by decide
  have hdescent : baseEnd_4566115 < baseStart_4566115 := by decide
  rcases family_descends (prefixWord ++ tailWord_4566115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4566122 : List Nat := [3, 1, 3, 2, 2, 1, 1, 1, 2, 1, 6]
def baseStart_4566122 : Nat := 118140960795 + 4566122 * 2 ^ 59
def prefixEnd_4566122 : Nat := 4983230072969 + 3 ^ 40 * 4566122 * 2
def baseEnd_4566122 : Nat := 2344615313069089260375793

theorem tailTrace_4566122 : CollatzResearch.WordTrace tailWord_4566122 prefixEnd_4566122 2344615313069089260375793 := by
  unfold tailWord_4566122
  simp only [CollatzResearch.WordTrace]
  refine ⟨41635037790931825099287155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 111026767442484866931432413 41635037790931825099287155)
  ·
    refine ⟨62452556686397737648930733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41635037790931825099287155 62452556686397737648930733)
    ·
      refine ⟨23419708757399151618349025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 62452556686397737648930733 23419708757399151618349025)
      ·
        refine ⟨17564781568049363713761769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23419708757399151618349025 17564781568049363713761769)
        ·
          refine ⟨13173586176037022785321327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17564781568049363713761769 13173586176037022785321327)
          ·
            refine ⟨19760379264055534177981991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13173586176037022785321327 19760379264055534177981991)
            ·
              refine ⟨29640568896083301266972987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19760379264055534177981991 29640568896083301266972987)
              ·
                refine ⟨44460853344124951900459481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29640568896083301266972987 44460853344124951900459481)
                ·
                  refine ⟨33345640008093713925344611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 44460853344124951900459481 33345640008093713925344611)
                  ·
                    refine ⟨50018460012140570888016917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 33345640008093713925344611 50018460012140570888016917)
                    ·
                      refine ⟨2344615313069089260375793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 50018460012140570888016917 2344615313069089260375793)
                      ·
                        rfl

theorem cell23_4566122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 1, 1, 2, 1, 6].length) (baseStart_4566122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4566122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4566122 prefixEnd_4566122 := by exact prefixLift 4566122
  have htrace : WordTrace (prefixWord ++ tailWord_4566122) baseStart_4566122 baseEnd_4566122 := by
    simpa [prefixWord, tailWord_4566122, baseEnd_4566122] using wordTrace_append hprefix tailTrace_4566122
  have hstable : (prefixWord ++ tailWord_4566122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4566122).length < 2 ^ (prefixWord ++ tailWord_4566122).sum := by decide
  have hdescent : baseEnd_4566122 < baseStart_4566122 := by decide
  rcases family_descends (prefixWord ++ tailWord_4566122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4566135 : List Nat := [1, 1, 3, 1, 1, 4, 1, 1, 1, 1, 8]
def baseStart_4566135 : Nat := 118140960795 + 4566135 * 2 ^ 59
def prefixEnd_4566135 : Nat := 4983230072969 + 3 ^ 40 * 4566135 * 2
def baseEnd_4566135 : Nat := 2344621988317597709513233

theorem tailTrace_4566135 : CollatzResearch.WordTrace tailWord_4566135 prefixEnd_4566135 2344621988317597709513233 := by
  unfold tailWord_4566135
  simp only [CollatzResearch.WordTrace]
  refine ⟨166540625312680203617371859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111027083541786802411581239 166540625312680203617371859)
  ·
    refine ⟨249810937969020305426057789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 166540625312680203617371859 249810937969020305426057789)
    ·
      refine ⟨93679101738382614534771671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 249810937969020305426057789 93679101738382614534771671)
      ·
        refine ⟨140518652607573921802157507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93679101738382614534771671 140518652607573921802157507)
        ·
          refine ⟨210777978911360882703236261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 140518652607573921802157507 210777978911360882703236261)
          ·
            refine ⟨39520871045880165506856799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 210777978911360882703236261 39520871045880165506856799)
            ·
              refine ⟨59281306568820248260285199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39520871045880165506856799 59281306568820248260285199)
              ·
                refine ⟨88921959853230372390427799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 59281306568820248260285199 88921959853230372390427799)
                ·
                  refine ⟨133382939779845558585641699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 88921959853230372390427799 133382939779845558585641699)
                  ·
                    refine ⟨200074409669768337878462549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 133382939779845558585641699 200074409669768337878462549)
                    ·
                      refine ⟨2344621988317597709513233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 200074409669768337878462549 2344621988317597709513233)
                      ·
                        rfl

theorem cell23_4566135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 1, 1, 1, 1, 8].length) (baseStart_4566135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4566135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4566135 prefixEnd_4566135 := by exact prefixLift 4566135
  have htrace : WordTrace (prefixWord ++ tailWord_4566135) baseStart_4566135 baseEnd_4566135 := by
    simpa [prefixWord, tailWord_4566135, baseEnd_4566135] using wordTrace_append hprefix tailTrace_4566135
  have hstable : (prefixWord ++ tailWord_4566135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4566135).length < 2 ^ (prefixWord ++ tailWord_4566135).sum := by decide
  have hdescent : baseEnd_4566135 < baseStart_4566135 := by decide
  rcases family_descends (prefixWord ++ tailWord_4566135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4566155 : List Nat := [1, 1, 1, 1, 4, 1, 1, 3, 2, 1, 7]
def baseStart_4566155 : Nat := 118140960795 + 4566155 * 2 ^ 59
def prefixEnd_4566155 : Nat := 4983230072969 + 3 ^ 40 * 4566155 * 2
def baseEnd_4566155 : Nat := 2344632257930687631263141

theorem tailTrace_4566155 : CollatzResearch.WordTrace tailWord_4566155 prefixEnd_4566155 2344632257930687631263141 := by
  unfold tailWord_4566155
  simp only [CollatzResearch.WordTrace]
  refine ⟨166541354772607747033099919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111027569848405164688733279 166541354772607747033099919)
  ·
    refine ⟨249812032158911620549649879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 166541354772607747033099919 249812032158911620549649879)
    ·
      refine ⟨374718048238367430824474819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 249812032158911620549649879 374718048238367430824474819)
      ·
        refine ⟨562077072357551146236712229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 374718048238367430824474819 562077072357551146236712229)
        ·
          refine ⟨105389451067040839919383543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 562077072357551146236712229 105389451067040839919383543)
          ·
            refine ⟨158084176600561259879075315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 105389451067040839919383543 158084176600561259879075315)
            ·
              refine ⟨237126264900841889818612973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 158084176600561259879075315 237126264900841889818612973)
              ·
                refine ⟨88922349337815708681979865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 237126264900841889818612973 88922349337815708681979865)
                ·
                  refine ⟨66691762003361781511484899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 88922349337815708681979865 66691762003361781511484899)
                  ·
                    refine ⟨100037643005042672267227349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 66691762003361781511484899 100037643005042672267227349)
                    ·
                      refine ⟨2344632257930687631263141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 100037643005042672267227349 2344632257930687631263141)
                      ·
                        rfl

theorem cell23_4566155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 3, 2, 1, 7].length) (baseStart_4566155 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4566155 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4566155 prefixEnd_4566155 := by exact prefixLift 4566155
  have htrace : WordTrace (prefixWord ++ tailWord_4566155) baseStart_4566155 baseEnd_4566155 := by
    simpa [prefixWord, tailWord_4566155, baseEnd_4566155] using wordTrace_append hprefix tailTrace_4566155
  have hstable : (prefixWord ++ tailWord_4566155).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4566155).length < 2 ^ (prefixWord ++ tailWord_4566155).sum := by decide
  have hdescent : baseEnd_4566155 < baseStart_4566155 := by decide
  rcases family_descends (prefixWord ++ tailWord_4566155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4566193 : List Nat := [1, 2, 2, 5, 1, 3, 1, 1, 3, 1, 3]
def baseStart_4566193 : Nat := 118140960795 + 4566193 * 2 ^ 59
def prefixEnd_4566193 : Nat := 4983230072969 + 3 ^ 40 * 4566193 * 2
def baseEnd_4566193 : Nat := 2344651770195558482587967

theorem tailTrace_4566193 : CollatzResearch.WordTrace tailWord_4566193 prefixEnd_4566193 2344651770195558482587967 := by
  unfold tailWord_4566193
  simp only [CollatzResearch.WordTrace]
  refine ⟨166542740746470079522983233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111028493830980053015322155 166542740746470079522983233)
  ·
    refine ⟨124907055559852559642237425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 166542740746470079522983233 124907055559852559642237425)
    ·
      refine ⟨93680291669889419731678069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 124907055559852559642237425 93680291669889419731678069)
      ·
        refine ⟨8782527344052133099844819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 93680291669889419731678069 8782527344052133099844819)
        ·
          refine ⟨13173791016078199649767229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8782527344052133099844819 13173791016078199649767229)
          ·
            refine ⟨4940171631029324868662711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13173791016078199649767229 4940171631029324868662711)
            ·
              refine ⟨7410257446543987302994067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4940171631029324868662711 7410257446543987302994067)
              ·
                refine ⟨11115386169815980954491101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7410257446543987302994067 11115386169815980954491101)
                ·
                  refine ⟨4168269813680992857934163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11115386169815980954491101 4168269813680992857934163)
                  ·
                    refine ⟨6252404720521489286901245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4168269813680992857934163 6252404720521489286901245)
                    ·
                      refine ⟨2344651770195558482587967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6252404720521489286901245 2344651770195558482587967)
                      ·
                        rfl

theorem cell23_4566193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 3, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 3, 1, 1, 3, 1, 3].length) (baseStart_4566193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4566193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4566193 prefixEnd_4566193 := by exact prefixLift 4566193
  have htrace : WordTrace (prefixWord ++ tailWord_4566193) baseStart_4566193 baseEnd_4566193 := by
    simpa [prefixWord, tailWord_4566193, baseEnd_4566193] using wordTrace_append hprefix tailTrace_4566193
  have hstable : (prefixWord ++ tailWord_4566193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4566193).length < 2 ^ (prefixWord ++ tailWord_4566193).sum := by decide
  have hdescent : baseEnd_4566193 < baseStart_4566193 := by decide
  rcases family_descends (prefixWord ++ tailWord_4566193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4566202 : List Nat := [3, 1, 1, 1, 2, 2, 1, 1, 2, 6, 3]
def baseStart_4566202 : Nat := 118140960795 + 4566202 * 2 ^ 59
def prefixEnd_4566202 : Nat := 4983230072969 + 3 ^ 40 * 4566202 * 2
def baseEnd_4566202 : Nat := 2344656391521448947375425

theorem tailTrace_4566202 : CollatzResearch.WordTrace tailWord_4566202 prefixEnd_4566202 2344656391521448947375425 := by
  unfold tailWord_4566202
  simp only [CollatzResearch.WordTrace]
  refine ⟨41635767250859368515015215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 111028712668958316040040573 41635767250859368515015215)
  ·
    refine ⟨62453650876289052772522823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41635767250859368515015215 62453650876289052772522823)
    ·
      refine ⟨93680476314433579158784235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62453650876289052772522823 93680476314433579158784235)
      ·
        refine ⟨140520714471650368738176353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93680476314433579158784235 140520714471650368738176353)
        ·
          refine ⟨105390535853737776553632265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 140520714471650368738176353 105390535853737776553632265)
          ·
            refine ⟨79042901890303332415224199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 105390535853737776553632265 79042901890303332415224199)
            ·
              refine ⟨118564352835454998622836299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 79042901890303332415224199 118564352835454998622836299)
              ·
                refine ⟨177846529253182497934254449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 118564352835454998622836299 177846529253182497934254449)
                ·
                  refine ⟨133384896939886873450690837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 177846529253182497934254449 133384896939886873450690837)
                  ·
                    refine ⟨6252417044057197193001133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 133384896939886873450690837 6252417044057197193001133)
                    ·
                      refine ⟨2344656391521448947375425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6252417044057197193001133 2344656391521448947375425)
                      ·
                        rfl

theorem cell23_4566202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 1, 2, 6, 3].length) (baseStart_4566202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4566202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4566202 prefixEnd_4566202 := by exact prefixLift 4566202
  have htrace : WordTrace (prefixWord ++ tailWord_4566202) baseStart_4566202 baseEnd_4566202 := by
    simpa [prefixWord, tailWord_4566202, baseEnd_4566202] using wordTrace_append hprefix tailTrace_4566202
  have hstable : (prefixWord ++ tailWord_4566202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4566202).length < 2 ^ (prefixWord ++ tailWord_4566202).sum := by decide
  have hdescent : baseEnd_4566202 < baseStart_4566202 := by decide
  rcases family_descends (prefixWord ++ tailWord_4566202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4566216 : List Nat := [2, 1, 3, 1, 2, 1, 2, 4, 3, 2, 2]
def baseStart_4566216 : Nat := 118140960795 + 4566216 * 2 ^ 59
def prefixEnd_4566216 : Nat := 4983230072969 + 3 ^ 40 * 4566216 * 2
def baseEnd_4566216 : Nat := 2344663580250611892600361

theorem tailTrace_4566216 : CollatzResearch.WordTrace tailWord_4566216 prefixEnd_4566216 2344663580250611892600361 := by
  unfold tailWord_4566216
  simp only [CollatzResearch.WordTrace]
  refine ⟨83271789812693377225535251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111029053083591169634047001 83271789812693377225535251)
  ·
    refine ⟨124907684719040065838302877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83271789812693377225535251 124907684719040065838302877)
    ·
      refine ⟨46840381769640024689363579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 124907684719040065838302877 46840381769640024689363579)
      ·
        refine ⟨70260572654460037034045369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46840381769640024689363579 70260572654460037034045369)
        ·
          refine ⟨52695429490845027775534027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 70260572654460037034045369 52695429490845027775534027)
          ·
            refine ⟨79043144236267541663301041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52695429490845027775534027 79043144236267541663301041)
            ·
              refine ⟨59282358177200656247475781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 79043144236267541663301041 59282358177200656247475781)
              ·
                refine ⟨11115442158225123046401709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 59282358177200656247475781 11115442158225123046401709)
                ·
                  refine ⟨4168290809334421142400641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11115442158225123046401709 4168290809334421142400641)
                  ·
                    refine ⟨3126218107000815856800481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4168290809334421142400641 3126218107000815856800481)
                    ·
                      refine ⟨2344663580250611892600361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3126218107000815856800481 2344663580250611892600361)
                      ·
                        rfl

theorem cell23_4566216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 2, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 2, 4, 3, 2, 2].length) (baseStart_4566216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4566216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4566216 prefixEnd_4566216 := by exact prefixLift 4566216
  have htrace : WordTrace (prefixWord ++ tailWord_4566216) baseStart_4566216 baseEnd_4566216 := by
    simpa [prefixWord, tailWord_4566216, baseEnd_4566216] using wordTrace_append hprefix tailTrace_4566216
  have hstable : (prefixWord ++ tailWord_4566216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4566216).length < 2 ^ (prefixWord ++ tailWord_4566216).sum := by decide
  have hdescent : baseEnd_4566216 < baseStart_4566216 := by decide
  rcases family_descends (prefixWord ++ tailWord_4566216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4566219 : List Nat := [1, 1, 1, 1, 3, 2, 2, 6, 1, 2, 3]
def baseStart_4566219 : Nat := 118140960795 + 4566219 * 2 ^ 59
def prefixEnd_4566219 : Nat := 4983230072969 + 3 ^ 40 * 4566219 * 2
def baseEnd_4566219 : Nat := 2344665120692575380862847

theorem tailTrace_4566219 : CollatzResearch.WordTrace tailWord_4566219 prefixEnd_4566219 2344665120692575380862847 := by
  unfold tailWord_4566219
  simp only [CollatzResearch.WordTrace]
  refine ⟨166543689044375885963429711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111029126029583923975619807 166543689044375885963429711)
  ·
    refine ⟨249815533566563828945144567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 166543689044375885963429711 249815533566563828945144567)
    ·
      refine ⟨374723300349845743417716851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 249815533566563828945144567 374723300349845743417716851)
      ·
        refine ⟨562084950524768615126575277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 374723300349845743417716851 562084950524768615126575277)
        ·
          refine ⟨210781856446788230672465729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 562084950524768615126575277 210781856446788230672465729)
          ·
            refine ⟨158086392335091173004349297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 210781856446788230672465729 158086392335091173004349297)
            ·
              refine ⟨118564794251318379753261973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 158086392335091173004349297 118564794251318379753261973)
              ·
                refine ⟨5557724730530549050934155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 118564794251318379753261973 5557724730530549050934155)
                ·
                  refine ⟨8336587095795823576401233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5557724730530549050934155 8336587095795823576401233)
                  ·
                    refine ⟨6252440321846867682300925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8336587095795823576401233 6252440321846867682300925)
                    ·
                      refine ⟨2344665120692575380862847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6252440321846867682300925 2344665120692575380862847)
                      ·
                        rfl

theorem cell23_4566219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 6, 1, 2, 3].length) (baseStart_4566219 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4566219 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4566219 prefixEnd_4566219 := by exact prefixLift 4566219
  have htrace : WordTrace (prefixWord ++ tailWord_4566219) baseStart_4566219 baseEnd_4566219 := by
    simpa [prefixWord, tailWord_4566219, baseEnd_4566219] using wordTrace_append hprefix tailTrace_4566219
  have hstable : (prefixWord ++ tailWord_4566219).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4566219).length < 2 ^ (prefixWord ++ tailWord_4566219).sum := by decide
  have hdescent : baseEnd_4566219 < baseStart_4566219 := by decide
  rcases family_descends (prefixWord ++ tailWord_4566219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4566229 : List Nat := [1, 3, 2, 4, 1, 1, 1, 1, 3, 2, 4]
def baseStart_4566229 : Nat := 118140960795 + 4566229 * 2 ^ 59
def prefixEnd_4566229 : Nat := 4983230072969 + 3 ^ 40 * 4566229 * 2
def baseEnd_4566229 : Nat := 2344670255499120341737801

theorem tailTrace_4566229 : CollatzResearch.WordTrace tailWord_4566229 prefixEnd_4566229 2344670255499120341737801 := by
  unfold tailWord_4566229
  simp only [CollatzResearch.WordTrace]
  refine ⟨166544053774339657671293741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111029369182893105114195827 166544053774339657671293741)
  ·
    refine ⟨62454020165377371626735153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 166544053774339657671293741 62454020165377371626735153)
    ·
      refine ⟨46840515124033028720051365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62454020165377371626735153 46840515124033028720051365)
      ·
        refine ⟨8782596585756192885009631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 46840515124033028720051365 8782596585756192885009631)
        ·
          refine ⟨13173894878634289327514447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8782596585756192885009631 13173894878634289327514447)
          ·
            refine ⟨19760842317951433991271671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13173894878634289327514447 19760842317951433991271671)
            ·
              refine ⟨29641263476927150986907507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19760842317951433991271671 29641263476927150986907507)
              ·
                refine ⟨44461895215390726480361261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29641263476927150986907507 44461895215390726480361261)
                ·
                  refine ⟨16673210705771522430135473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 44461895215390726480361261 16673210705771522430135473)
                  ·
                    refine ⟨12504908029328641822601605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16673210705771522430135473 12504908029328641822601605)
                    ·
                      refine ⟨2344670255499120341737801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12504908029328641822601605 2344670255499120341737801)
                      ·
                        rfl

theorem cell23_4566229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 1, 1, 3, 2, 4].length) (baseStart_4566229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4566229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4566229 prefixEnd_4566229 := by exact prefixLift 4566229
  have htrace : WordTrace (prefixWord ++ tailWord_4566229) baseStart_4566229 baseEnd_4566229 := by
    simpa [prefixWord, tailWord_4566229, baseEnd_4566229] using wordTrace_append hprefix tailTrace_4566229
  have hstable : (prefixWord ++ tailWord_4566229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4566229).length < 2 ^ (prefixWord ++ tailWord_4566229).sum := by decide
  have hdescent : baseEnd_4566229 < baseStart_4566229 := by decide
  rcases family_descends (prefixWord ++ tailWord_4566229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4566230 : List Nat := [5, 2, 1, 2, 2, 1, 3, 1, 1, 5]
def baseStart_4566230 : Nat := 118140960795 + 4566230 * 2 ^ 59
def prefixEnd_4566230 : Nat := 4983230072969 + 3 ^ 40 * 4566230 * 2
def baseEnd_4566230 : Nat := 781556922993258279275099

theorem tailTrace_4566230 : CollatzResearch.WordTrace tailWord_4566230 prefixEnd_4566230 781556922993258279275099 := by
  unfold tailWord_4566230
  simp only [CollatzResearch.WordTrace]
  refine ⟨10409005640458502177630009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 111029393498224023228053429 10409005640458502177630009)
  ·
    refine ⟨7806754230343876633222507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10409005640458502177630009 7806754230343876633222507)
    ·
      refine ⟨11710131345515814949833761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7806754230343876633222507 11710131345515814949833761)
      ·
        refine ⟨8782598509136861212375321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11710131345515814949833761 8782598509136861212375321)
        ·
          refine ⟨6586948881852645909281491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8782598509136861212375321 6586948881852645909281491)
          ·
            refine ⟨9880423322778968863922237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6586948881852645909281491 9880423322778968863922237)
            ·
              refine ⟨3705158746042113323970839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9880423322778968863922237 3705158746042113323970839)
              ·
                refine ⟨5557738119063169985956259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3705158746042113323970839 5557738119063169985956259)
                ·
                  refine ⟨8336607178594754978934389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5557738119063169985956259 8336607178594754978934389)
                  ·
                    refine ⟨781556922993258279275099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8336607178594754978934389 781556922993258279275099)
                    ·
                      rfl

theorem cell23_4566230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 1, 3, 1, 1, 5].length) (baseStart_4566230 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4566230 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4566230 prefixEnd_4566230 := by exact prefixLift 4566230
  have htrace : WordTrace (prefixWord ++ tailWord_4566230) baseStart_4566230 baseEnd_4566230 := by
    simpa [prefixWord, tailWord_4566230, baseEnd_4566230] using wordTrace_append hprefix tailTrace_4566230
  have hstable : (prefixWord ++ tailWord_4566230).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4566230).length < 2 ^ (prefixWord ++ tailWord_4566230).sum := by decide
  have hdescent : baseEnd_4566230 < baseStart_4566230 := by decide
  rcases family_descends (prefixWord ++ tailWord_4566230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4566233 : List Nat := [1, 2, 1, 2, 3, 1, 1, 7, 1, 2, 2]
def baseStart_4566233 : Nat := 118140960795 + 4566233 * 2 ^ 59
def prefixEnd_4566233 : Nat := 4983230072969 + 3 ^ 40 * 4566233 * 2
def baseEnd_4566233 : Nat := 2344672309421738326087783

theorem tailTrace_4566233 : CollatzResearch.WordTrace tailWord_4566233 prefixEnd_4566233 2344672309421738326087783 := by
  unfold tailWord_4566233
  simp only [CollatzResearch.WordTrace]
  refine ⟨166544199666325166354439353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111029466444216777569626235 166544199666325166354439353)
  ·
    refine ⟨124908149749743874765829515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 166544199666325166354439353 124908149749743874765829515)
    ·
      refine ⟨187362224624615812148744273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 124908149749743874765829515 187362224624615812148744273)
      ·
        refine ⟨140521668468461859111558205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 187362224624615812148744273 140521668468461859111558205)
        ·
          refine ⟨52695625675673197166834327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 140521668468461859111558205 52695625675673197166834327)
          ·
            refine ⟨79043438513509795750251491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52695625675673197166834327 79043438513509795750251491)
            ·
              refine ⟨118565157770264693625377237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 79043438513509795750251491 118565157770264693625377237)
              ·
                refine ⟨2778870885240578756844779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 118565157770264693625377237 2778870885240578756844779)
                ·
                  refine ⟨4168306327860868135267169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2778870885240578756844779 4168306327860868135267169)
                  ·
                    refine ⟨3126229745895651101450377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4168306327860868135267169 3126229745895651101450377)
                    ·
                      refine ⟨2344672309421738326087783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3126229745895651101450377 2344672309421738326087783)
                      ·
                        rfl

theorem cell23_4566233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 7, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 7, 1, 2, 2].length) (baseStart_4566233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4566233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4566233 prefixEnd_4566233 := by exact prefixLift 4566233
  have htrace : WordTrace (prefixWord ++ tailWord_4566233) baseStart_4566233 baseEnd_4566233 := by
    simpa [prefixWord, tailWord_4566233, baseEnd_4566233] using wordTrace_append hprefix tailTrace_4566233
  have hstable : (prefixWord ++ tailWord_4566233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4566233).length < 2 ^ (prefixWord ++ tailWord_4566233).sum := by decide
  have hdescent : baseEnd_4566233 < baseStart_4566233 := by decide
  rcases family_descends (prefixWord ++ tailWord_4566233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4566250 : List Nat := [3, 1, 3, 1, 1, 4, 1, 4, 1, 2, 2]
def baseStart_4566250 : Nat := 118140960795 + 4566250 * 2 ^ 59
def prefixEnd_4566250 : Nat := 4983230072969 + 3 ^ 40 * 4566250 * 2
def baseEnd_4566250 : Nat := 2344681038592864759575205

theorem tailTrace_4566250 : CollatzResearch.WordTrace tailWord_4566250 prefixEnd_4566250 2344681038592864759575205 := by
  unfold tailWord_4566250
  simp only [CollatzResearch.WordTrace]
  refine ⟨41636204926815894564452051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 111029879804842385505205469 41636204926815894564452051)
  ·
    refine ⟨62454307390223841846678077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41636204926815894564452051 62454307390223841846678077)
    ·
      refine ⟨23420365271333940692504279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 62454307390223841846678077 23420365271333940692504279)
      ·
        refine ⟨35130547907000911038756419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23420365271333940692504279 35130547907000911038756419)
        ·
          refine ⟨52695821860501366558134629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35130547907000911038756419 52695821860501366558134629)
          ·
            refine ⟨9880466598844006229650243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 52695821860501366558134629 9880466598844006229650243)
            ·
              refine ⟨14820699898266009344475365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9880466598844006229650243 14820699898266009344475365)
              ·
                refine ⟨2778881230924876752089131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14820699898266009344475365 2778881230924876752089131)
                ·
                  refine ⟨4168321846387315128133697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2778881230924876752089131 4168321846387315128133697)
                  ·
                    refine ⟨3126241384790486346100273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4168321846387315128133697 3126241384790486346100273)
                    ·
                      refine ⟨2344681038592864759575205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3126241384790486346100273 2344681038592864759575205)
                      ·
                        rfl

theorem cell23_4566250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 4, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 4, 1, 4, 1, 2, 2].length) (baseStart_4566250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4566250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4566250 prefixEnd_4566250 := by exact prefixLift 4566250
  have htrace : WordTrace (prefixWord ++ tailWord_4566250) baseStart_4566250 baseEnd_4566250 := by
    simpa [prefixWord, tailWord_4566250, baseEnd_4566250] using wordTrace_append hprefix tailTrace_4566250
  have hstable : (prefixWord ++ tailWord_4566250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4566250).length < 2 ^ (prefixWord ++ tailWord_4566250).sum := by decide
  have hdescent : baseEnd_4566250 < baseStart_4566250 := by decide
  rcases family_descends (prefixWord ++ tailWord_4566250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4566252 : List Nat := [2, 2, 1, 1, 2, 4, 1, 1, 2, 7]
def baseStart_4566252 : Nat := 118140960795 + 4566252 * 2 ^ 59
def prefixEnd_4566252 : Nat := 4983230072969 + 3 ^ 40 * 4566252 * 2
def baseEnd_4566252 : Nat := 781560688518057917250065

theorem tailTrace_4566252 : CollatzResearch.WordTrace tailWord_4566252 prefixEnd_4566252 781560688518057917250065 := by
  unfold tailWord_4566252
  simp only [CollatzResearch.WordTrace]
  refine ⟨83272446326628166299690505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111029928435504221732920673 83272446326628166299690505)
  ·
    refine ⟨62454334744971124724767879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83272446326628166299690505 62454334744971124724767879)
    ·
      refine ⟨93681502117456687087151819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62454334744971124724767879 93681502117456687087151819)
      ·
        refine ⟨140522253176185030630727729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93681502117456687087151819 140522253176185030630727729)
        ·
          refine ⟨105391689882138772973045797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 140522253176185030630727729 105391689882138772973045797)
          ·
            refine ⟨19760941852901019932446087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 105391689882138772973045797 19760941852901019932446087)
            ·
              refine ⟨29641412779351529898669131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19760941852901019932446087 29641412779351529898669131)
              ·
                refine ⟨44462119169027294848003697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29641412779351529898669131 44462119169027294848003697)
                ·
                  refine ⟨33346589376770471136002773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 44462119169027294848003697 33346589376770471136002773)
                  ·
                    refine ⟨781560688518057917250065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 33346589376770471136002773 781560688518057917250065)
                    ·
                      rfl

theorem cell23_4566252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 7].length) (baseStart_4566252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4566252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4566252 prefixEnd_4566252 := by exact prefixLift 4566252
  have htrace : WordTrace (prefixWord ++ tailWord_4566252) baseStart_4566252 baseEnd_4566252 := by
    simpa [prefixWord, tailWord_4566252, baseEnd_4566252] using wordTrace_append hprefix tailTrace_4566252
  have hstable : (prefixWord ++ tailWord_4566252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4566252).length < 2 ^ (prefixWord ++ tailWord_4566252).sum := by decide
  have hdescent : baseEnd_4566252 < baseStart_4566252 := by decide
  rcases family_descends (prefixWord ++ tailWord_4566252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4566260 : List Nat := [2, 6, 1, 2, 1, 1, 2, 1, 1, 6]
def baseStart_4566260 : Nat := 118140960795 + 4566260 * 2 ^ 59
def prefixEnd_4566260 : Nat := 4983230072969 + 3 ^ 40 * 4566260 * 2
def baseEnd_4566260 : Nat := 781562057799803240150053

theorem tailTrace_4566260 : CollatzResearch.WordTrace tailWord_4566260 prefixEnd_4566260 781562057799803240150053 := by
  unfold tailWord_4566260
  simp only [CollatzResearch.WordTrace]
  refine ⟨83272592218613674982836117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111030122958151566643781489 83272592218613674982836117)
  ·
    refine ⟨3903402760247516014820443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 83272592218613674982836117 3903402760247516014820443)
    ·
      refine ⟨5855104140371274022230665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3903402760247516014820443 5855104140371274022230665)
      ·
        refine ⟨4391328105278455516672999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5855104140371274022230665 4391328105278455516672999)
        ·
          refine ⟨6586992157917683275009499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4391328105278455516672999 6586992157917683275009499)
          ·
            refine ⟨9880488236876524912514249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6586992157917683275009499 9880488236876524912514249)
            ·
              refine ⟨7410366177657393684385687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9880488236876524912514249 7410366177657393684385687)
              ·
                refine ⟨11115549266486090526578531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7410366177657393684385687 11115549266486090526578531)
                ·
                  refine ⟨16673323899729135789867797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11115549266486090526578531 16673323899729135789867797)
                  ·
                    refine ⟨781562057799803240150053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16673323899729135789867797 781562057799803240150053)
                    ·
                      rfl

theorem cell23_4566260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 1, 2, 1, 1, 6].length) (baseStart_4566260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4566260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4566260 prefixEnd_4566260 := by exact prefixLift 4566260
  have htrace : WordTrace (prefixWord ++ tailWord_4566260) baseStart_4566260 baseEnd_4566260 := by
    simpa [prefixWord, tailWord_4566260, baseEnd_4566260] using wordTrace_append hprefix tailTrace_4566260
  have hstable : (prefixWord ++ tailWord_4566260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4566260).length < 2 ^ (prefixWord ++ tailWord_4566260).sum := by decide
  have hdescent : baseEnd_4566260 < baseStart_4566260 := by decide
  rcases family_descends (prefixWord ++ tailWord_4566260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4566266 : List Nat := [3, 1, 1, 1, 1, 4, 1, 5, 2, 1, 3]
def baseStart_4566266 : Nat := 118140960795 + 4566266 * 2 ^ 59
def prefixEnd_4566266 : Nat := 4983230072969 + 3 ^ 40 * 4566266 * 2
def baseEnd_4566266 : Nat := 2344689254283336696975131

theorem tailTrace_4566266 : CollatzResearch.WordTrace tailWord_4566266 prefixEnd_4566266 2344689254283336696975131 := by
  unfold tailWord_4566266
  simp only [CollatzResearch.WordTrace]
  refine ⟨41636350818801403247597663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 111030268850137075326927101 41636350818801403247597663)
  ·
    refine ⟨62454526228202104871396495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41636350818801403247597663 62454526228202104871396495)
    ·
      refine ⟨93681789342303157307094743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62454526228202104871396495 93681789342303157307094743)
      ·
        refine ⟨140522684013454735960642115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93681789342303157307094743 140522684013454735960642115)
        ·
          refine ⟨210784026020182103940963173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 140522684013454735960642115 210784026020182103940963173)
          ·
            refine ⟨39522004878784144488930595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 210784026020182103940963173 39522004878784144488930595)
            ·
              refine ⟨59283007318176216733395893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39522004878784144488930595 59283007318176216733395893)
              ·
                refine ⟨5557781936079020318755865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 59283007318176216733395893 5557781936079020318755865)
                ·
                  refine ⟨4168336452059265239066899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5557781936079020318755865 4168336452059265239066899)
                  ·
                    refine ⟨6252504678088897858600349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4168336452059265239066899 6252504678088897858600349)
                    ·
                      refine ⟨2344689254283336696975131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6252504678088897858600349 2344689254283336696975131)
                      ·
                        rfl

theorem cell23_4566266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 1, 5, 2, 1, 3].length) (baseStart_4566266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4566266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4566266 prefixEnd_4566266 := by exact prefixLift 4566266
  have htrace : WordTrace (prefixWord ++ tailWord_4566266) baseStart_4566266 baseEnd_4566266 := by
    simpa [prefixWord, tailWord_4566266, baseEnd_4566266] using wordTrace_append hprefix tailTrace_4566266
  have hstable : (prefixWord ++ tailWord_4566266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4566266).length < 2 ^ (prefixWord ++ tailWord_4566266).sum := by decide
  have hdescent : baseEnd_4566266 < baseStart_4566266 := by decide
  rcases family_descends (prefixWord ++ tailWord_4566266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4566272 : List Nat := [2, 1, 1, 2, 1, 1, 3, 1, 4, 3, 4]
def baseStart_4566272 : Nat := 118140960795 + 4566272 * 2 ^ 59
def prefixEnd_4566272 : Nat := 4983230072969 + 3 ^ 40 * 4566272 * 2
def baseEnd_4566272 : Nat := 2344692335167263673500103

theorem tailTrace_4566272 : CollatzResearch.WordTrace tailWord_4566272 prefixEnd_4566272 2344692335167263673500103 := by
  unfold tailWord_4566272
  simp only [CollatzResearch.WordTrace]
  refine ⟨83272811056591938007554535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111030414742122584010072713 83272811056591938007554535)
  ·
    refine ⟨124909216584887907011331803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83272811056591938007554535 124909216584887907011331803)
    ·
      refine ⟨187363824877331860516997705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 124909216584887907011331803 187363824877331860516997705)
      ·
        refine ⟨140522868657998895387748279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 187363824877331860516997705 140522868657998895387748279)
        ·
          refine ⟨210784302986998343081622419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 140522868657998895387748279 210784302986998343081622419)
          ·
            refine ⟨316176454480497514622433629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 210784302986998343081622419 316176454480497514622433629)
            ·
              refine ⟨118566170430186567983412611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 316176454480497514622433629 118566170430186567983412611)
              ·
                refine ⟨177849255645279851975118917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 118566170430186567983412611 177849255645279851975118917)
                ·
                  refine ⟨33346735433489972245334797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 177849255645279851975118917 33346735433489972245334797)
                  ·
                    refine ⟨12505025787558739592000549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 33346735433489972245334797 12505025787558739592000549)
                    ·
                      refine ⟨2344692335167263673500103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12505025787558739592000549 2344692335167263673500103)
                      ·
                        rfl

theorem cell23_4566272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 1, 4, 3, 4].length) (baseStart_4566272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4566272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4566272 prefixEnd_4566272 := by exact prefixLift 4566272
  have htrace : WordTrace (prefixWord ++ tailWord_4566272) baseStart_4566272 baseEnd_4566272 := by
    simpa [prefixWord, tailWord_4566272, baseEnd_4566272] using wordTrace_append hprefix tailTrace_4566272
  have hstable : (prefixWord ++ tailWord_4566272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4566272).length < 2 ^ (prefixWord ++ tailWord_4566272).sum := by decide
  have hdescent : baseEnd_4566272 < baseStart_4566272 := by decide
  rcases family_descends (prefixWord ++ tailWord_4566272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4566282 : List Nat := [3, 1, 2, 2, 1, 1, 1, 1, 3, 8]
def baseStart_4566282 : Nat := 118140960795 + 4566282 * 2 ^ 59
def prefixEnd_4566282 : Nat := 4983230072969 + 3 ^ 40 * 4566282 * 2
def baseEnd_4566282 : Nat := 781565823324602878125019

theorem tailTrace_4566282 : CollatzResearch.WordTrace tailWord_4566282 prefixEnd_4566282 781565823324602878125019 := by
  unfold tailWord_4566282
  simp only [CollatzResearch.WordTrace]
  refine ⟨41636496710786911930743275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 111030657895431765148648733 41636496710786911930743275)
  ·
    refine ⟨62454745066180367896114913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41636496710786911930743275 62454745066180367896114913)
    ·
      refine ⟨46841058799635275922086185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62454745066180367896114913 46841058799635275922086185)
      ·
        refine ⟨35130794099726456941564639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46841058799635275922086185 35130794099726456941564639)
        ·
          refine ⟨52696191149589685412346959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35130794099726456941564639 52696191149589685412346959)
          ·
            refine ⟨79044286724384528118520439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52696191149589685412346959 79044286724384528118520439)
            ·
              refine ⟨118566430086576792177780659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 79044286724384528118520439 118566430086576792177780659)
              ·
                refine ⟨177849645129865188266670989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 118566430086576792177780659 177849645129865188266670989)
                ·
                  refine ⟨66693616923699445600001621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 177849645129865188266670989 66693616923699445600001621)
                  ·
                    refine ⟨781565823324602878125019, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 66693616923699445600001621 781565823324602878125019)
                    ·
                      rfl

theorem cell23_4566282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 1, 3, 8].length) (baseStart_4566282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4566282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4566282 prefixEnd_4566282 := by exact prefixLift 4566282
  have htrace : WordTrace (prefixWord ++ tailWord_4566282) baseStart_4566282 baseEnd_4566282 := by
    simpa [prefixWord, tailWord_4566282, baseEnd_4566282] using wordTrace_append hprefix tailTrace_4566282
  have hstable : (prefixWord ++ tailWord_4566282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4566282).length < 2 ^ (prefixWord ++ tailWord_4566282).sum := by decide
  have hdescent : baseEnd_4566282 < baseStart_4566282 := by decide
  rcases family_descends (prefixWord ++ tailWord_4566282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4566317 : List Nat := [1, 5, 3, 1, 1, 2, 3, 1, 2, 1, 3]
def baseStart_4566317 : Nat := 118140960795 + 4566317 * 2 ^ 59
def prefixEnd_4566317 : Nat := 4983230072969 + 3 ^ 40 * 4566317 * 2
def baseEnd_4566317 : Nat := 2344715441796715997437397

theorem tailTrace_4566317 : CollatzResearch.WordTrace tailWord_4566317 prefixEnd_4566317 2344715441796715997437397 := by
  unfold tailWord_4566317
  simp only [CollatzResearch.WordTrace]
  refine ⟨166547263398020848700497205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111031508932013899133664803 166547263398020848700497205)
  ·
    refine ⟨15613805943564454565671613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 166547263398020848700497205 15613805943564454565671613)
    ·
      refine ⟨5855177228836670462126855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15613805943564454565671613 5855177228836670462126855)
      ·
        refine ⟨8782765843255005693190283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5855177228836670462126855 8782765843255005693190283)
        ·
          refine ⟨13174148764882508539785425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8782765843255005693190283 13174148764882508539785425)
          ·
            refine ⟨9880611573661881404839069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13174148764882508539785425 9880611573661881404839069)
            ·
              refine ⟨3705229340123205526814651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9880611573661881404839069 3705229340123205526814651)
              ·
                refine ⟨5557844010184808290221977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3705229340123205526814651 5557844010184808290221977)
                ·
                  refine ⟨4168383007638606217666483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5557844010184808290221977 4168383007638606217666483)
                  ·
                    refine ⟨6252574511457909326499725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4168383007638606217666483 6252574511457909326499725)
                    ·
                      refine ⟨2344715441796715997437397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6252574511457909326499725 2344715441796715997437397)
                      ·
                        rfl

theorem cell23_4566317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 2, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 2, 3, 1, 2, 1, 3].length) (baseStart_4566317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4566317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4566317 prefixEnd_4566317 := by exact prefixLift 4566317
  have htrace : WordTrace (prefixWord ++ tailWord_4566317) baseStart_4566317 baseEnd_4566317 := by
    simpa [prefixWord, tailWord_4566317, baseEnd_4566317] using wordTrace_append hprefix tailTrace_4566317
  have hstable : (prefixWord ++ tailWord_4566317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4566317).length < 2 ^ (prefixWord ++ tailWord_4566317).sum := by decide
  have hdescent : baseEnd_4566317 < baseStart_4566317 := by decide
  rcases family_descends (prefixWord ++ tailWord_4566317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4566323 : List Nat := [1, 1, 1, 2, 5, 4, 1, 1, 1, 4, 2]
def baseStart_4566323 : Nat := 118140960795 + 4566323 * 2 ^ 59
def prefixEnd_4566323 : Nat := 4983230072969 + 3 ^ 40 * 4566323 * 2
def baseEnd_4566323 : Nat := 2344718522680642973962369

theorem tailTrace_4566323 : CollatzResearch.WordTrace tailWord_4566323 prefixEnd_4566323 2344718522680642973962369 := by
  unfold tailWord_4566323
  simp only [CollatzResearch.WordTrace]
  refine ⟨166547482235999111725215623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111031654823999407816810415 166547482235999111725215623)
  ·
    refine ⟨249821223353998667587823435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 166547482235999111725215623 249821223353998667587823435)
    ·
      refine ⟨374731835030998001381735153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 249821223353998667587823435 374731835030998001381735153)
      ·
        refine ⟨281048876273248501036301365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 374731835030998001381735153 281048876273248501036301365)
        ·
          refine ⟨26348332150617046972153253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 281048876273248501036301365 26348332150617046972153253)
          ·
            refine ⟨4940312278240696307278735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 26348332150617046972153253 4940312278240696307278735)
            ·
              refine ⟨7410468417361044460918103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4940312278240696307278735 7410468417361044460918103)
              ·
                refine ⟨11115702626041566691377155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7410468417361044460918103 11115702626041566691377155)
                ·
                  refine ⟨16673553939062350037065733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11115702626041566691377155 16673553939062350037065733)
                  ·
                    refine ⟨3126291363574190631949825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16673553939062350037065733 3126291363574190631949825)
                    ·
                      refine ⟨2344718522680642973962369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3126291363574190631949825 2344718522680642973962369)
                      ·
                        rfl

theorem cell23_4566323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 4, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 4, 1, 1, 1, 4, 2].length) (baseStart_4566323 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4566323 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4566323 prefixEnd_4566323 := by exact prefixLift 4566323
  have htrace : WordTrace (prefixWord ++ tailWord_4566323) baseStart_4566323 baseEnd_4566323 := by
    simpa [prefixWord, tailWord_4566323, baseEnd_4566323] using wordTrace_append hprefix tailTrace_4566323
  have hstable : (prefixWord ++ tailWord_4566323).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4566323).length < 2 ^ (prefixWord ++ tailWord_4566323).sum := by decide
  have hdescent : baseEnd_4566323 < baseStart_4566323 := by decide
  rcases family_descends (prefixWord ++ tailWord_4566323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4566340 : List Nat := [2, 3, 4, 1, 1, 1, 1, 2, 4, 2, 2]
def baseStart_4566340 : Nat := 118140960795 + 4566340 * 2 ^ 59
def prefixEnd_4566340 : Nat := 4983230072969 + 3 ^ 40 * 4566340 * 2
def baseEnd_4566340 : Nat := 2344727251851769407449791

theorem tailTrace_4566340 : CollatzResearch.WordTrace tailWord_4566340 prefixEnd_4566340 2344727251851769407449791 := by
  unfold tailWord_4566340
  simp only [CollatzResearch.WordTrace]
  refine ⟨83274051138468761814292237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111032068184625015752389649 83274051138468761814292237)
  ·
    refine ⟨31227769176925785680359589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 83274051138468761814292237 31227769176925785680359589)
    ·
      refine ⟨5855206720673584815067423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 31227769176925785680359589 5855206720673584815067423)
      ·
        refine ⟨8782810081010377222601135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5855206720673584815067423 8782810081010377222601135)
        ·
          refine ⟨13174215121515565833901703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8782810081010377222601135 13174215121515565833901703)
          ·
            refine ⟨19761322682273348750852555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13174215121515565833901703 19761322682273348750852555)
            ·
              refine ⟨29641984023410023126278833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19761322682273348750852555 29641984023410023126278833)
              ·
                refine ⟨22231488017557517344709125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29641984023410023126278833 22231488017557517344709125)
                ·
                  refine ⟨4168404003292034502132961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22231488017557517344709125 4168404003292034502132961)
                  ·
                    refine ⟨3126303002469025876599721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4168404003292034502132961 3126303002469025876599721)
                    ·
                      refine ⟨2344727251851769407449791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3126303002469025876599721 2344727251851769407449791)
                      ·
                        rfl

theorem cell23_4566340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 1, 2, 4, 2, 2].length) (baseStart_4566340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4566340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4566340 prefixEnd_4566340 := by exact prefixLift 4566340
  have htrace : WordTrace (prefixWord ++ tailWord_4566340) baseStart_4566340 baseEnd_4566340 := by
    simpa [prefixWord, tailWord_4566340, baseEnd_4566340] using wordTrace_append hprefix tailTrace_4566340
  have hstable : (prefixWord ++ tailWord_4566340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4566340).length < 2 ^ (prefixWord ++ tailWord_4566340).sum := by decide
  have hdescent : baseEnd_4566340 < baseStart_4566340 := by decide
  rcases family_descends (prefixWord ++ tailWord_4566340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4566359 : List Nat := [1, 1, 3, 2, 3, 2, 1, 1, 4, 5]
def baseStart_4566359 : Nat := 118140960795 + 4566359 * 2 ^ 59
def prefixEnd_4566359 : Nat := 4983230072969 + 3 ^ 40 * 4566359 * 2
def baseEnd_4566359 : Nat := 781579002661401611037401

theorem tailTrace_4566359 : CollatzResearch.WordTrace tailWord_4566359 prefixEnd_4566359 781579002661401611037401 := by
  unfold tailWord_4566359
  simp only [CollatzResearch.WordTrace]
  refine ⟨166548795263868689873526131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111032530175912459915684087 166548795263868689873526131)
  ·
    refine ⟨249823192895803034810289197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 166548795263868689873526131 249823192895803034810289197)
    ·
      refine ⟨93683697335926138053858449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 249823192895803034810289197 93683697335926138053858449)
      ·
        refine ⟨70262773001944603540393837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 93683697335926138053858449 70262773001944603540393837)
        ·
          refine ⟨26348539875729226327647689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 70262773001944603540393837 26348539875729226327647689)
          ·
            refine ⟨19761404906796919745735767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26348539875729226327647689 19761404906796919745735767)
            ·
              refine ⟨29642107360195379618603651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19761404906796919745735767 29642107360195379618603651)
              ·
                refine ⟨44463161040293069427905477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29642107360195379618603651 44463161040293069427905477)
                ·
                  refine ⟨8336842695054950517732277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 44463161040293069427905477 8336842695054950517732277)
                  ·
                    refine ⟨781579002661401611037401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8336842695054950517732277 781579002661401611037401)
                    ·
                      rfl

theorem cell23_4566359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 1, 1, 4, 5].length) (baseStart_4566359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4566359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4566359 prefixEnd_4566359 := by exact prefixLift 4566359
  have htrace : WordTrace (prefixWord ++ tailWord_4566359) baseStart_4566359 baseEnd_4566359 := by
    simpa [prefixWord, tailWord_4566359, baseEnd_4566359] using wordTrace_append hprefix tailTrace_4566359
  have hstable : (prefixWord ++ tailWord_4566359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4566359).length < 2 ^ (prefixWord ++ tailWord_4566359).sum := by decide
  have hdescent : baseEnd_4566359 < baseStart_4566359 := by decide
  rcases family_descends (prefixWord ++ tailWord_4566359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4566396 : List Nat := [2, 2, 2, 1, 1, 1, 6, 1, 2, 1, 4]
def baseStart_4566396 : Nat := 118140960795 + 4566396 * 2 ^ 59
def prefixEnd_4566396 : Nat := 4983230072969 + 3 ^ 40 * 4566396 * 2
def baseEnd_4566396 : Nat := 2344756006768421188349533

theorem tailTrace_4566396 : CollatzResearch.WordTrace tailWord_4566396 prefixEnd_4566396 2344756006768421188349533 := by
  unfold tailWord_4566396
  simp only [CollatzResearch.WordTrace]
  refine ⟨83275072382367322596311521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111033429843156430128415361 83275072382367322596311521)
  ·
    refine ⟨62456304286775491947233641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83275072382367322596311521 62456304286775491947233641)
    ·
      refine ⟨46842228215081618960425231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62456304286775491947233641 46842228215081618960425231)
      ·
        refine ⟨70263342322622428440637847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46842228215081618960425231 70263342322622428440637847)
        ·
          refine ⟨105395013483933642660956771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70263342322622428440637847 105395013483933642660956771)
          ·
            refine ⟨158092520225900463991435157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 105395013483933642660956771 158092520225900463991435157)
            ·
              refine ⟨7410586885589084249598523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 158092520225900463991435157 7410586885589084249598523)
              ·
                refine ⟨11115880328383626374397785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7410586885589084249598523 11115880328383626374397785)
                ·
                  refine ⟨8336910246287719780798339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11115880328383626374397785 8336910246287719780798339)
                  ·
                    refine ⟨12505365369431579671197509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8336910246287719780798339 12505365369431579671197509)
                    ·
                      refine ⟨2344756006768421188349533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12505365369431579671197509 2344756006768421188349533)
                      ·
                        rfl

theorem cell23_4566396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 6, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 6, 1, 2, 1, 4].length) (baseStart_4566396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4566396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4566396 prefixEnd_4566396 := by exact prefixLift 4566396
  have htrace : WordTrace (prefixWord ++ tailWord_4566396) baseStart_4566396 baseEnd_4566396 := by
    simpa [prefixWord, tailWord_4566396, baseEnd_4566396] using wordTrace_append hprefix tailTrace_4566396
  have hstable : (prefixWord ++ tailWord_4566396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4566396).length < 2 ^ (prefixWord ++ tailWord_4566396).sum := by decide
  have hdescent : baseEnd_4566396 < baseStart_4566396 := by decide
  rcases family_descends (prefixWord ++ tailWord_4566396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4566440 : List Nat := [2, 1, 6, 1, 2, 1, 1, 2, 3, 4]
def baseStart_4566440 : Nat := 118140960795 + 4566440 * 2 ^ 59
def prefixEnd_4566440 : Nat := 4983230072969 + 3 ^ 40 * 4566440 * 2
def baseEnd_4566440 : Nat := 781592866639073005399777

theorem tailTrace_4566440 : CollatzResearch.WordTrace tailWord_4566440 prefixEnd_4566440 781592866639073005399777 := by
  unfold tailWord_4566440
  simp only [CollatzResearch.WordTrace]
  refine ⟨83275874788287620353612387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111034499717716827138149849 83275874788287620353612387)
  ·
    refine ⟨124913812182431430530418581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83275874788287620353612387 124913812182431430530418581)
    ·
      refine ⟨5855334946051473306113371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 124913812182431430530418581 5855334946051473306113371)
      ·
        refine ⟨8783002419077209959170057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5855334946051473306113371 8783002419077209959170057)
        ·
          refine ⟨6587251814307907469377543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8783002419077209959170057 6587251814307907469377543)
          ·
            refine ⟨9880877721461861204066315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6587251814307907469377543 9880877721461861204066315)
            ·
              refine ⟨14821316582192791806099473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9880877721461861204066315 14821316582192791806099473)
              ·
                refine ⟨11115987436644593854574605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14821316582192791806099473 11115987436644593854574605)
                ·
                  refine ⟨4168495288741722695465477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11115987436644593854574605 4168495288741722695465477)
                  ·
                    refine ⟨781592866639073005399777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4168495288741722695465477 781592866639073005399777)
                    ·
                      rfl

theorem cell23_4566440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 1, 1, 2, 3, 4].length) (baseStart_4566440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4566440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4566440 prefixEnd_4566440 := by exact prefixLift 4566440
  have htrace : WordTrace (prefixWord ++ tailWord_4566440) baseStart_4566440 baseEnd_4566440 := by
    simpa [prefixWord, tailWord_4566440, baseEnd_4566440] using wordTrace_append hprefix tailTrace_4566440
  have hstable : (prefixWord ++ tailWord_4566440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4566440).length < 2 ^ (prefixWord ++ tailWord_4566440).sum := by decide
  have hdescent : baseEnd_4566440 < baseStart_4566440 := by decide
  rcases family_descends (prefixWord ++ tailWord_4566440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4566479 : List Nat := [1, 1, 2, 1, 1, 4, 2, 2, 3, 6]
def baseStart_4566479 : Nat := 118140960795 + 4566479 * 2 ^ 59
def prefixEnd_4566479 : Nat := 4983230072969 + 3 ^ 40 * 4566479 * 2
def baseEnd_4566479 : Nat := 781599541887581454537217

theorem tailTrace_4566479 : CollatzResearch.WordTrace tailWord_4566479 prefixEnd_4566479 781599541887581454537217 := by
  unfold tailWord_4566479
  simp only [CollatzResearch.WordTrace]
  refine ⟨166553172023433950367894491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111035448015622633578596327 166553172023433950367894491)
  ·
    refine ⟨249829758035150925551841737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 166553172023433950367894491 249829758035150925551841737)
    ·
      refine ⟨187372318526363194163881303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 249829758035150925551841737 187372318526363194163881303)
      ·
        refine ⟨281058477789544791245821955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 187372318526363194163881303 281058477789544791245821955)
        ·
          refine ⟨421587716684317186868732933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 281058477789544791245821955 421587716684317186868732933)
          ·
            refine ⟨79047696878309472537887425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 421587716684317186868732933 79047696878309472537887425)
            ·
              refine ⟨59285772658732104403415569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 79047696878309472537887425 59285772658732104403415569)
              ·
                refine ⟨44464329494049078302561677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 59285772658732104403415569 44464329494049078302561677)
                ·
                  refine ⟨16674123560268404363460629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 44464329494049078302561677 16674123560268404363460629)
                  ·
                    refine ⟨781599541887581454537217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16674123560268404363460629 781599541887581454537217)
                    ·
                      rfl

theorem cell23_4566479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 2, 2, 3, 6].length) (baseStart_4566479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4566479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4566479 prefixEnd_4566479 := by exact prefixLift 4566479
  have htrace : WordTrace (prefixWord ++ tailWord_4566479) baseStart_4566479 baseEnd_4566479 := by
    simpa [prefixWord, tailWord_4566479, baseEnd_4566479] using wordTrace_append hprefix tailTrace_4566479
  have hstable : (prefixWord ++ tailWord_4566479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4566479).length < 2 ^ (prefixWord ++ tailWord_4566479).sum := by decide
  have hdescent : baseEnd_4566479 < baseStart_4566479 := by decide
  rcases family_descends (prefixWord ++ tailWord_4566479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4566503 : List Nat := [1, 1, 5, 2, 1, 2, 1, 4, 1, 1, 4]
def baseStart_4566503 : Nat := 118140960795 + 4566503 * 2 ^ 59
def prefixEnd_4566503 : Nat := 4983230072969 + 3 ^ 40 * 4566503 * 2
def baseEnd_4566503 : Nat := 2344810949198452269711541

theorem tailTrace_4566503 : CollatzResearch.WordTrace tailWord_4566503 prefixEnd_4566503 2344810949198452269711541 := by
  unfold tailWord_4566503
  simp only [CollatzResearch.WordTrace]
  refine ⟨166554047375347002466768163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111036031583564668311178775 166554047375347002466768163)
  ·
    refine ⟨249831071063020503700152245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 166554047375347002466768163 249831071063020503700152245)
    ·
      refine ⟨23421662912158172221889273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 249831071063020503700152245 23421662912158172221889273)
      ·
        refine ⟨17566247184118629166416955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23421662912158172221889273 17566247184118629166416955)
        ·
          refine ⟨26349370776177943749625433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17566247184118629166416955 26349370776177943749625433)
          ·
            refine ⟨19762028082133457812219075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26349370776177943749625433 19762028082133457812219075)
            ·
              refine ⟨29643042123200186718328613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19762028082133457812219075 29643042123200186718328613)
              ·
                refine ⟨5558070398100035009686615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 29643042123200186718328613 5558070398100035009686615)
                ·
                  refine ⟨8337105597150052514529923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5558070398100035009686615 8337105597150052514529923)
                  ·
                    refine ⟨12505658395725078771794885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8337105597150052514529923 12505658395725078771794885)
                    ·
                      refine ⟨2344810949198452269711541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12505658395725078771794885 2344810949198452269711541)
                      ·
                        rfl

theorem cell23_4566503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 1, 4, 1, 1, 4].length) (baseStart_4566503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4566503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4566503 prefixEnd_4566503 := by exact prefixLift 4566503
  have htrace : WordTrace (prefixWord ++ tailWord_4566503) baseStart_4566503 baseEnd_4566503 := by
    simpa [prefixWord, tailWord_4566503, baseEnd_4566503] using wordTrace_append hprefix tailTrace_4566503
  have hstable : (prefixWord ++ tailWord_4566503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4566503).length < 2 ^ (prefixWord ++ tailWord_4566503).sum := by decide
  have hdescent : baseEnd_4566503 < baseStart_4566503 := by decide
  rcases family_descends (prefixWord ++ tailWord_4566503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4566514 : List Nat := [3, 2, 1, 4, 1, 3, 1, 3, 1, 1, 3]
def baseStart_4566514 : Nat := 118140960795 + 4566514 * 2 ^ 59
def prefixEnd_4566514 : Nat := 4983230072969 + 3 ^ 40 * 4566514 * 2
def baseEnd_4566514 : Nat := 2344816597485651726673991

theorem tailTrace_4566514 : CollatzResearch.WordTrace tailWord_4566514 prefixEnd_4566514 2344816597485651726673991 := by
  unfold tailWord_4566514
  simp only [CollatzResearch.WordTrace]
  refine ⟨41638612144576787836354649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 111036299052204767563612397 41638612144576787836354649)
  ·
    refine ⟨31228959108432590877265987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41638612144576787836354649 31228959108432590877265987)
    ·
      refine ⟨46843438662648886315898981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31228959108432590877265987 46843438662648886315898981)
      ·
        refine ⟨8783144749246666184231059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 46843438662648886315898981 8783144749246666184231059)
        ·
          refine ⟨13174717123869999276346589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8783144749246666184231059 13174717123869999276346589)
          ·
            refine ⟨4940518921451249728629971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13174717123869999276346589 4940518921451249728629971)
            ·
              refine ⟨7410778382176874592944957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4940518921451249728629971 7410778382176874592944957)
              ·
                refine ⟨2779041893316327972354359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7410778382176874592944957 2779041893316327972354359)
                ·
                  refine ⟨4168562839974491958531539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2779041893316327972354359 4168562839974491958531539)
                  ·
                    refine ⟨6252844259961737937797309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4168562839974491958531539 6252844259961737937797309)
                    ·
                      refine ⟨2344816597485651726673991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6252844259961737937797309 2344816597485651726673991)
                      ·
                        rfl

theorem cell23_4566514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 3, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 3, 1, 3, 1, 1, 3].length) (baseStart_4566514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4566514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4566514 prefixEnd_4566514 := by exact prefixLift 4566514
  have htrace : WordTrace (prefixWord ++ tailWord_4566514) baseStart_4566514 baseEnd_4566514 := by
    simpa [prefixWord, tailWord_4566514, baseEnd_4566514] using wordTrace_append hprefix tailTrace_4566514
  have hstable : (prefixWord ++ tailWord_4566514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4566514).length < 2 ^ (prefixWord ++ tailWord_4566514).sum := by decide
  have hdescent : baseEnd_4566514 < baseStart_4566514 := by decide
  rcases family_descends (prefixWord ++ tailWord_4566514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4566530 : List Nat := [3, 4, 1, 2, 1, 1, 2, 1, 4, 4]
def baseStart_4566530 : Nat := 118140960795 + 4566530 * 2 ^ 59
def prefixEnd_4566530 : Nat := 4983230072969 + 3 ^ 40 * 4566530 * 2
def baseEnd_4566530 : Nat := 781608271058707888024639

theorem tailTrace_4566530 : CollatzResearch.WordTrace tailWord_4566530 prefixEnd_4566530 781608271058707888024639 := by
  unfold tailWord_4566530
  simp only [CollatzResearch.WordTrace]
  refine ⟨41638758036562296519500261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 111036688097499457385334029 41638758036562296519500261)
  ·
    refine ⟨7807267131855430597406299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 41638758036562296519500261 7807267131855430597406299)
    ·
      refine ⟨11710900697783145896109449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7807267131855430597406299 11710900697783145896109449)
      ·
        refine ⟨8783175523337359422082087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11710900697783145896109449 8783175523337359422082087)
        ·
          refine ⟨13174763285006039133123131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8783175523337359422082087 13174763285006039133123131)
          ·
            refine ⟨19762144927509058699684697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13174763285006039133123131 19762144927509058699684697)
            ·
              refine ⟨14821608695631794024763523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19762144927509058699684697 14821608695631794024763523)
              ·
                refine ⟨22232413043447691037145285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14821608695631794024763523 22232413043447691037145285)
                ·
                  refine ⟨4168577445646442069464741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22232413043447691037145285 4168577445646442069464741)
                  ·
                    refine ⟨781608271058707888024639, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4168577445646442069464741 781608271058707888024639)
                    ·
                      rfl

theorem cell23_4566530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 2, 1, 4, 4].length) (baseStart_4566530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4566530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4566530 prefixEnd_4566530 := by exact prefixLift 4566530
  have htrace : WordTrace (prefixWord ++ tailWord_4566530) baseStart_4566530 baseEnd_4566530 := by
    simpa [prefixWord, tailWord_4566530, baseEnd_4566530] using wordTrace_append hprefix tailTrace_4566530
  have hstable : (prefixWord ++ tailWord_4566530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4566530).length < 2 ^ (prefixWord ++ tailWord_4566530).sum := by decide
  have hdescent : baseEnd_4566530 < baseStart_4566530 := by decide
  rcases family_descends (prefixWord ++ tailWord_4566530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4566586 : List Nat := [3, 1, 1, 1, 3, 2, 2, 2, 2, 6]
def baseStart_4566586 : Nat := 118140960795 + 4566586 * 2 ^ 59
def prefixEnd_4566586 : Nat := 4983230072969 + 3 ^ 40 * 4566586 * 2
def baseEnd_4566586 : Nat := 781617856030925148324553

theorem tailTrace_4566586 : CollatzResearch.WordTrace tailWord_4566586 prefixEnd_4566586 781617856030925148324553 := by
  unfold tailWord_4566586
  simp only [CollatzResearch.WordTrace]
  refine ⟨41639268658511576910509903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 111038049756030871761359741 41639268658511576910509903)
  ·
    refine ⟨62458902987767365365764855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41639268658511576910509903 62458902987767365365764855)
    ·
      refine ⟨93688354481651048048647283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62458902987767365365764855 93688354481651048048647283)
      ·
        refine ⟨140532531722476572072970925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93688354481651048048647283 140532531722476572072970925)
        ·
          refine ⟨52699699395928714527364097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 140532531722476572072970925 52699699395928714527364097)
          ·
            refine ⟨39524774546946535895523073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52699699395928714527364097 39524774546946535895523073)
            ·
              refine ⟨29643580910209901921642305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39524774546946535895523073 29643580910209901921642305)
              ·
                refine ⟨22232685682657426441231729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29643580910209901921642305 22232685682657426441231729)
                ·
                  refine ⟨16674514261993069830923797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22232685682657426441231729 16674514261993069830923797)
                  ·
                    refine ⟨781617856030925148324553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16674514261993069830923797 781617856030925148324553)
                    ·
                      rfl

theorem cell23_4566586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 2, 2, 2, 6].length) (baseStart_4566586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4566586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4566586 prefixEnd_4566586 := by exact prefixLift 4566586
  have htrace : WordTrace (prefixWord ++ tailWord_4566586) baseStart_4566586 baseEnd_4566586 := by
    simpa [prefixWord, tailWord_4566586, baseEnd_4566586] using wordTrace_append hprefix tailTrace_4566586
  have hstable : (prefixWord ++ tailWord_4566586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4566586).length < 2 ^ (prefixWord ++ tailWord_4566586).sum := by decide
  have hdescent : baseEnd_4566586 < baseStart_4566586 := by decide
  rcases family_descends (prefixWord ++ tailWord_4566586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4566588 : List Nat := [2, 2, 2, 2, 5, 1, 2, 2, 1, 2, 2]
def baseStart_4566588 : Nat := 118140960795 + 4566588 * 2 ^ 59
def prefixEnd_4566588 : Nat := 4983230072969 + 3 ^ 40 * 4566588 * 2
def baseEnd_4566588 : Nat := 2344854595054084437148651

theorem tailTrace_4566588 : CollatzResearch.WordTrace tailWord_4566588 prefixEnd_4566588 2344854595054084437148651 := by
  unfold tailWord_4566588
  simp only [CollatzResearch.WordTrace]
  refine ⟨83278573790019530991806209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111038098386692707989074945 83278573790019530991806209)
  ·
    refine ⟨62458930342514648243854657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83278573790019530991806209 62458930342514648243854657)
    ·
      refine ⟨46844197756885986182890993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62458930342514648243854657 46844197756885986182890993)
      ·
        refine ⟨35133148317664489637168245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46844197756885986182890993 35133148317664489637168245)
        ·
          refine ⟨3293732654781045903484523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 35133148317664489637168245 3293732654781045903484523)
          ·
            refine ⟨4940598982171568855226785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3293732654781045903484523 4940598982171568855226785)
            ·
              refine ⟨3705449236628676641420089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4940598982171568855226785 3705449236628676641420089)
              ·
                refine ⟨2779086927471507481065067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3705449236628676641420089 2779086927471507481065067)
                ·
                  refine ⟨4168630391207261221597601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2779086927471507481065067 4168630391207261221597601)
                  ·
                    refine ⟨3126472793405445916198201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4168630391207261221597601 3126472793405445916198201)
                    ·
                      refine ⟨2344854595054084437148651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3126472793405445916198201 2344854595054084437148651)
                      ·
                        rfl

theorem cell23_4566588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 5, 1, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 5, 1, 2, 2, 1, 2, 2].length) (baseStart_4566588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4566588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4566588 prefixEnd_4566588 := by exact prefixLift 4566588
  have htrace : WordTrace (prefixWord ++ tailWord_4566588) baseStart_4566588 baseEnd_4566588 := by
    simpa [prefixWord, tailWord_4566588, baseEnd_4566588] using wordTrace_append hprefix tailTrace_4566588
  have hstable : (prefixWord ++ tailWord_4566588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4566588).length < 2 ^ (prefixWord ++ tailWord_4566588).sum := by decide
  have hdescent : baseEnd_4566588 < baseStart_4566588 := by decide
  rcases family_descends (prefixWord ++ tailWord_4566588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4566610 : List Nat := [3, 2, 2, 1, 2, 2, 1, 3, 1, 4, 2]
def baseStart_4566610 : Nat := 118140960795 + 4566610 * 2 ^ 59
def prefixEnd_4566610 : Nat := 4983230072969 + 3 ^ 40 * 4566610 * 2
def baseEnd_4566610 : Nat := 2344865891628483351073549

theorem tailTrace_4566610 : CollatzResearch.WordTrace tailWord_4566610 prefixEnd_4566610 2344865891628483351073549 := by
  unfold tailWord_4566610
  simp only [CollatzResearch.WordTrace]
  refine ⟨41639487496489839935228321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 111038633323972906493942189 41639487496489839935228321)
  ·
    refine ⟨31229615622367379951421241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41639487496489839935228321 31229615622367379951421241)
    ·
      refine ⟨23422211716775534963565931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31229615622367379951421241 23422211716775534963565931)
      ·
        refine ⟨35133317575163302445348897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23422211716775534963565931 35133317575163302445348897)
        ·
          refine ⟨26349988181372476834011673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35133317575163302445348897 26349988181372476834011673)
          ·
            refine ⟨19762491136029357625508755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26349988181372476834011673 19762491136029357625508755)
            ·
              refine ⟨29643736704044036438263133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19762491136029357625508755 29643736704044036438263133)
              ·
                refine ⟨11116401264016513664348675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29643736704044036438263133 11116401264016513664348675)
                ·
                  refine ⟨16674601896024770496523013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11116401264016513664348675 16674601896024770496523013)
                  ·
                    refine ⟨3126487855504644468098065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16674601896024770496523013 3126487855504644468098065)
                    ·
                      refine ⟨2344865891628483351073549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3126487855504644468098065 2344865891628483351073549)
                      ·
                        rfl

theorem cell23_4566610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 1, 3, 1, 4, 2].length) (baseStart_4566610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4566610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4566610 prefixEnd_4566610 := by exact prefixLift 4566610
  have htrace : WordTrace (prefixWord ++ tailWord_4566610) baseStart_4566610 baseEnd_4566610 := by
    simpa [prefixWord, tailWord_4566610, baseEnd_4566610] using wordTrace_append hprefix tailTrace_4566610
  have hstable : (prefixWord ++ tailWord_4566610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4566610).length < 2 ^ (prefixWord ++ tailWord_4566610).sum := by decide
  have hdescent : baseEnd_4566610 < baseStart_4566610 := by decide
  rcases family_descends (prefixWord ++ tailWord_4566610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4566633 : List Nat := [1, 2, 1, 1, 1, 4, 3, 5, 5]
def baseStart_4566633 : Nat := 118140960795 + 4566633 * 2 ^ 59
def prefixEnd_4566633 : Nat := 4983230072969 + 3 ^ 40 * 4566633 * 2
def baseEnd_4566633 : Nat := 260541966853726306787327

theorem tailTrace_4566633 : CollatzResearch.WordTrace tailWord_4566633 prefixEnd_4566633 260541966853726306787327 := by
  unfold tailWord_4566633
  simp only [CollatzResearch.WordTrace]
  refine ⟨166558788864876034669000553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111039192576584023112667035 166558788864876034669000553)
  ·
    refine ⟨124919091648657026001750415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 166558788864876034669000553 124919091648657026001750415)
    ·
      refine ⟨187378637472985539002625623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 124919091648657026001750415 187378637472985539002625623)
      ·
        refine ⟨281067956209478308503938435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 187378637472985539002625623 281067956209478308503938435)
        ·
          refine ⟨421601934314217462755907653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 281067956209478308503938435 421601934314217462755907653)
          ·
            refine ⟨79050362683915774266732685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 421601934314217462755907653 79050362683915774266732685)
            ·
              refine ⟨29643886006468415350024757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 79050362683915774266732685 29643886006468415350024757)
              ·
                refine ⟨2779114313106413939064821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 29643886006468415350024757 2779114313106413939064821)
                ·
                  refine ⟨260541966853726306787327, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2779114313106413939064821 260541966853726306787327)
                  ·
                    rfl

theorem cell23_4566633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 3, 5, 5].length) (baseStart_4566633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4566633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4566633 prefixEnd_4566633 := by exact prefixLift 4566633
  have htrace : WordTrace (prefixWord ++ tailWord_4566633) baseStart_4566633 baseEnd_4566633 := by
    simpa [prefixWord, tailWord_4566633, baseEnd_4566633] using wordTrace_append hprefix tailTrace_4566633
  have hstable : (prefixWord ++ tailWord_4566633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4566633).length < 2 ^ (prefixWord ++ tailWord_4566633).sum := by decide
  have hdescent : baseEnd_4566633 < baseStart_4566633 := by decide
  rcases family_descends (prefixWord ++ tailWord_4566633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4566656 : List Nat := [2, 1, 1, 2, 1, 4, 2, 1, 1, 1, 7]
def baseStart_4566656 : Nat := 118140960795 + 4566656 * 2 ^ 59
def prefixEnd_4566656 : Nat := 4983230072969 + 3 ^ 40 * 4566656 * 2
def baseEnd_4566656 : Nat := 2344889511738590171098337

theorem tailTrace_4566656 : CollatzResearch.WordTrace tailWord_4566656 prefixEnd_4566656 2344889511738590171098337 := by
  unfold tailWord_4566656
  simp only [CollatzResearch.WordTrace]
  refine ⟨83279813871896354798543911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111039751829195139731391881 83279813871896354798543911)
  ·
    refine ⟨124919720807844532197815867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83279813871896354798543911 124919720807844532197815867)
    ·
      refine ⟨187379581211766798296723801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 124919720807844532197815867 187379581211766798296723801)
      ·
        refine ⟨140534685908825098722542851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 187379581211766798296723801 140534685908825098722542851)
        ·
          refine ⟨210802028863237648083814277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 140534685908825098722542851 210802028863237648083814277)
          ·
            refine ⟨39525380411857059015715177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 210802028863237648083814277 39525380411857059015715177)
            ·
              refine ⟨29644035308892794261786383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39525380411857059015715177 29644035308892794261786383)
              ·
                refine ⟨44466052963339191392679575, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29644035308892794261786383 44466052963339191392679575)
                ·
                  refine ⟨66699079445008787089019363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 44466052963339191392679575 66699079445008787089019363)
                  ·
                    refine ⟨100048619167513180633529045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 66699079445008787089019363 100048619167513180633529045)
                    ·
                      refine ⟨2344889511738590171098337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 100048619167513180633529045 2344889511738590171098337)
                      ·
                        rfl

theorem cell23_4566656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 2, 1, 1, 1, 7].length) (baseStart_4566656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4566656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4566656 prefixEnd_4566656 := by exact prefixLift 4566656
  have htrace : WordTrace (prefixWord ++ tailWord_4566656) baseStart_4566656 baseEnd_4566656 := by
    simpa [prefixWord, tailWord_4566656, baseEnd_4566656] using wordTrace_append hprefix tailTrace_4566656
  have hstable : (prefixWord ++ tailWord_4566656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4566656).length < 2 ^ (prefixWord ++ tailWord_4566656).sum := by decide
  have hdescent : baseEnd_4566656 < baseStart_4566656 := by decide
  rcases family_descends (prefixWord ++ tailWord_4566656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4566684 : List Nat := [2, 2, 3, 2, 4, 1, 1, 3, 5]
def baseStart_4566684 : Nat := 118140960795 + 4566684 * 2 ^ 59
def prefixEnd_4566684 : Nat := 4983230072969 + 3 ^ 40 * 4566684 * 2
def baseEnd_4566684 : Nat := 260544876577435117949801

theorem tailTrace_4566684 : CollatzResearch.WordTrace tailWord_4566684 prefixEnd_4566684 260544876577435117949801 := by
  unfold tailWord_4566684
  simp only [CollatzResearch.WordTrace]
  refine ⟨83280324493845635189553553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111040432658460846919404737 83280324493845635189553553)
  ·
    refine ⟨62460243370384226392165165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83280324493845635189553553 62460243370384226392165165)
    ·
      refine ⟨23422591263894084897061937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 62460243370384226392165165 23422591263894084897061937)
      ·
        refine ⟨17566943447920563672796453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23422591263894084897061937 17566943447920563672796453)
        ·
          refine ⟨3293801896485105688649335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17566943447920563672796453 3293801896485105688649335)
          ·
            refine ⟨4940702844727658532974003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3293801896485105688649335 4940702844727658532974003)
            ·
              refine ⟨7411054267091487799461005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4940702844727658532974003 7411054267091487799461005)
              ·
                refine ⟨2779145350159307924797877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7411054267091487799461005 2779145350159307924797877)
                ·
                  refine ⟨260544876577435117949801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2779145350159307924797877 260544876577435117949801)
                  ·
                    rfl

theorem cell23_4566684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 4, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 4, 1, 1, 3, 5].length) (baseStart_4566684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4566684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4566684 prefixEnd_4566684 := by exact prefixLift 4566684
  have htrace : WordTrace (prefixWord ++ tailWord_4566684) baseStart_4566684 baseEnd_4566684 := by
    simpa [prefixWord, tailWord_4566684, baseEnd_4566684] using wordTrace_append hprefix tailTrace_4566684
  have hstable : (prefixWord ++ tailWord_4566684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4566684).length < 2 ^ (prefixWord ++ tailWord_4566684).sum := by decide
  have hdescent : baseEnd_4566684 < baseStart_4566684 := by decide
  rcases family_descends (prefixWord ++ tailWord_4566684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4566693 : List Nat := [1, 3, 1, 2, 1, 2, 2, 2, 5, 4]
def baseStart_4566693 : Nat := 118140960795 + 4566693 * 2 ^ 59
def prefixEnd_4566693 : Nat := 4983230072969 + 3 ^ 40 * 4566693 * 2
def baseEnd_4566693 : Nat := 781636170174268842111889

theorem tailTrace_4566693 : CollatzResearch.WordTrace tailWord_4566693 prefixEnd_4566693 781636170174268842111889 := by
  unfold tailWord_4566693
  simp only [CollatzResearch.WordTrace]
  refine ⟨166560977244658664916184733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111040651496439109944123155 166560977244658664916184733)
  ·
    refine ⟨62460366466746999343569275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 166560977244658664916184733 62460366466746999343569275)
    ·
      refine ⟨93690549700120499015353913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62460366466746999343569275 93690549700120499015353913)
      ·
        refine ⟨70267912275090374261515435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 93690549700120499015353913 70267912275090374261515435)
        ·
          refine ⟨105401868412635561392273153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70267912275090374261515435 105401868412635561392273153)
          ·
            refine ⟨79051401309476671044204865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 105401868412635561392273153 79051401309476671044204865)
            ·
              refine ⟨59288550982107503283153649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 79051401309476671044204865 59288550982107503283153649)
              ·
                refine ⟨44466413236580627462365237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 59288550982107503283153649 44466413236580627462365237)
                ·
                  refine ⟨4168726240929433824596741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 44466413236580627462365237 4168726240929433824596741)
                  ·
                    refine ⟨781636170174268842111889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4168726240929433824596741 781636170174268842111889)
                    ·
                      rfl

theorem cell23_4566693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 2, 2, 5, 4].length) (baseStart_4566693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4566693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4566693 prefixEnd_4566693 := by exact prefixLift 4566693
  have htrace : WordTrace (prefixWord ++ tailWord_4566693) baseStart_4566693 baseEnd_4566693 := by
    simpa [prefixWord, tailWord_4566693, baseEnd_4566693] using wordTrace_append hprefix tailTrace_4566693
  have hstable : (prefixWord ++ tailWord_4566693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4566693).length < 2 ^ (prefixWord ++ tailWord_4566693).sum := by decide
  have hdescent : baseEnd_4566693 < baseStart_4566693 := by decide
  rcases family_descends (prefixWord ++ tailWord_4566693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4566783 : List Nat := [1, 1, 2, 2, 1, 3, 3, 3, 1, 6]
def baseStart_4566783 : Nat := 118140960795 + 4566783 * 2 ^ 59
def prefixEnd_4566783 : Nat := 4983230072969 + 3 ^ 40 * 4566783 * 2
def baseEnd_4566783 : Nat := 781651574593903724736751

theorem tailTrace_4566783 : CollatzResearch.WordTrace tailWord_4566783 prefixEnd_4566783 781651574593903724736751 := by
  unfold tailWord_4566783
  simp only [CollatzResearch.WordTrace]
  refine ⟨166564259814332610286961003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111042839876221740191307335 166564259814332610286961003)
  ·
    refine ⟨249846389721498915430441505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 166564259814332610286961003 249846389721498915430441505)
    ·
      refine ⟨187384792291124186572831129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 249846389721498915430441505 187384792291124186572831129)
      ·
        refine ⟨140538594218343139929623347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 187384792291124186572831129 140538594218343139929623347)
        ·
          refine ⟨210807891327514709894435021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 140538594218343139929623347 210807891327514709894435021)
          ·
            refine ⟨79052959247818016210413133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 210807891327514709894435021 79052959247818016210413133)
            ·
              refine ⟨29644859717931756078904925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 79052959247818016210413133 29644859717931756078904925)
              ·
                refine ⟨11116822394224408529589347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29644859717931756078904925 11116822394224408529589347)
                ·
                  refine ⟨16675233591336612794384021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11116822394224408529589347 16675233591336612794384021)
                  ·
                    refine ⟨781651574593903724736751, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16675233591336612794384021 781651574593903724736751)
                    ·
                      rfl

theorem cell23_4566783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 3, 3, 1, 6].length) (baseStart_4566783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4566783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4566783 prefixEnd_4566783 := by exact prefixLift 4566783
  have htrace : WordTrace (prefixWord ++ tailWord_4566783) baseStart_4566783 baseEnd_4566783 := by
    simpa [prefixWord, tailWord_4566783, baseEnd_4566783] using wordTrace_append hprefix tailTrace_4566783
  have hstable : (prefixWord ++ tailWord_4566783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4566783).length < 2 ^ (prefixWord ++ tailWord_4566783).sum := by decide
  have hdescent : baseEnd_4566783 < baseStart_4566783 := by decide
  rcases family_descends (prefixWord ++ tailWord_4566783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4566794 : List Nat := [3, 1, 2, 2, 1, 5, 1, 1, 2, 3, 2]
def baseStart_4566794 : Nat := 118140960795 + 4566794 * 2 ^ 59
def prefixEnd_4566794 : Nat := 4983230072969 + 3 ^ 40 * 4566794 * 2
def baseEnd_4566794 : Nat := 2344960372068910631172703

theorem tailTrace_4566794 : CollatzResearch.WordTrace tailWord_4566794 prefixEnd_4566794 2344960372068910631172703 := by
  unfold tailWord_4566794
  simp only [CollatzResearch.WordTrace]
  refine ⟨41641165254323189791402859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 111043107344861839443740957 41641165254323189791402859)
  ·
    refine ⟨62461747881484784687104289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41641165254323189791402859 62461747881484784687104289)
    ·
      refine ⟨46846310911113588515328217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62461747881484784687104289 46846310911113588515328217)
      ·
        refine ⟨35134733183335191386496163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46846310911113588515328217 35134733183335191386496163)
        ·
          refine ⟨52702099775002787079744245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35134733183335191386496163 52702099775002787079744245)
          ·
            refine ⟨4940821853906511288726023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 52702099775002787079744245 4940821853906511288726023)
            ·
              refine ⟨7411232780859766933089035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4940821853906511288726023 7411232780859766933089035)
              ·
                refine ⟨11116849171289650399633553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7411232780859766933089035 11116849171289650399633553)
                ·
                  refine ⟨8337636878467237799725165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11116849171289650399633553 8337636878467237799725165)
                  ·
                    refine ⟨3126613829425214174896937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8337636878467237799725165 3126613829425214174896937)
                    ·
                      refine ⟨2344960372068910631172703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3126613829425214174896937 2344960372068910631172703)
                      ·
                        rfl

theorem cell23_4566794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 5, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 5, 1, 1, 2, 3, 2].length) (baseStart_4566794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4566794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4566794 prefixEnd_4566794 := by exact prefixLift 4566794
  have htrace : WordTrace (prefixWord ++ tailWord_4566794) baseStart_4566794 baseEnd_4566794 := by
    simpa [prefixWord, tailWord_4566794, baseEnd_4566794] using wordTrace_append hprefix tailTrace_4566794
  have hstable : (prefixWord ++ tailWord_4566794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4566794).length < 2 ^ (prefixWord ++ tailWord_4566794).sum := by decide
  have hdescent : baseEnd_4566794 < baseStart_4566794 := by decide
  rcases family_descends (prefixWord ++ tailWord_4566794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4566803 : List Nat := [1, 1, 1, 2, 1, 3, 2, 3, 3, 2, 4]
def baseStart_4566803 : Nat := 118140960795 + 4566803 * 2 ^ 59
def prefixEnd_4566803 : Nat := 4983230072969 + 3 ^ 40 * 4566803 * 2
def baseEnd_4566803 : Nat := 2344964993394801095960161

theorem tailTrace_4566803 : CollatzResearch.WordTrace tailWord_4566803 prefixEnd_4566803 2344964993394801095960161 := by
  unfold tailWord_4566803
  simp only [CollatzResearch.WordTrace]
  refine ⟨166564989274260153702689063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111043326182840102468459375 166564989274260153702689063)
  ·
    refine ⟨249847483911390230554033595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 166564989274260153702689063 249847483911390230554033595)
    ·
      refine ⟨374771225867085345831050393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 249847483911390230554033595 374771225867085345831050393)
      ·
        refine ⟨281078419400314009373287795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 374771225867085345831050393 281078419400314009373287795)
        ·
          refine ⟨421617629100471014059931693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 281078419400314009373287795 421617629100471014059931693)
          ·
            refine ⟨158106610912676630272474385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 421617629100471014059931693 158106610912676630272474385)
            ·
              refine ⟨118579958184507472704355789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 158106610912676630272474385 118579958184507472704355789)
              ·
                refine ⟨44467484319190302264133421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 118579958184507472704355789 44467484319190302264133421)
                ·
                  refine ⟨16675306619696363349050033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 44467484319190302264133421 16675306619696363349050033)
                  ·
                    refine ⟨12506479964772272511787525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16675306619696363349050033 12506479964772272511787525)
                    ·
                      refine ⟨2344964993394801095960161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12506479964772272511787525 2344964993394801095960161)
                      ·
                        rfl

theorem cell23_4566803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 3, 3, 2, 4].length) (baseStart_4566803 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4566803 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4566803 prefixEnd_4566803 := by exact prefixLift 4566803
  have htrace : WordTrace (prefixWord ++ tailWord_4566803) baseStart_4566803 baseEnd_4566803 := by
    simpa [prefixWord, tailWord_4566803, baseEnd_4566803] using wordTrace_append hprefix tailTrace_4566803
  have hstable : (prefixWord ++ tailWord_4566803).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4566803).length < 2 ^ (prefixWord ++ tailWord_4566803).sum := by decide
  have hdescent : baseEnd_4566803 < baseStart_4566803 := by decide
  rcases family_descends (prefixWord ++ tailWord_4566803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4566807 : List Nat := [1, 1, 3, 4, 2, 2, 1, 3, 1, 1, 4]
def baseStart_4566807 : Nat := 118140960795 + 4566807 * 2 ^ 59
def prefixEnd_4566807 : Nat := 4983230072969 + 3 ^ 40 * 4566807 * 2
def baseEnd_4566807 : Nat := 2344967047317419080310143

theorem tailTrace_4566807 : CollatzResearch.WordTrace tailWord_4566807 prefixEnd_4566807 2344967047317419080310143 := by
  unfold tailWord_4566807
  simp only [CollatzResearch.WordTrace]
  refine ⟨166565135166245662385834675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111043423444163774923889783 166565135166245662385834675)
  ·
    refine ⟨249847702749368493578752013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 166565135166245662385834675 249847702749368493578752013)
    ·
      refine ⟨93692888531013185092032005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 249847702749368493578752013 93692888531013185092032005)
      ·
        refine ⟨17567416599564972204756001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 93692888531013185092032005 17567416599564972204756001)
        ·
          refine ⟨13175562449673729153567001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17567416599564972204756001 13175562449673729153567001)
          ·
            refine ⟨9881671837255296865175251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13175562449673729153567001 9881671837255296865175251)
            ·
              refine ⟨14822507755882945297762877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9881671837255296865175251 14822507755882945297762877)
              ·
                refine ⟨5558440408456104486661079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14822507755882945297762877 5558440408456104486661079)
                ·
                  refine ⟨8337660612684156729991619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5558440408456104486661079 8337660612684156729991619)
                  ·
                    refine ⟨12506490919026235094987429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8337660612684156729991619 12506490919026235094987429)
                    ·
                      refine ⟨2344967047317419080310143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12506490919026235094987429 2344967047317419080310143)
                      ·
                        rfl

theorem cell23_4566807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 2, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 2, 1, 3, 1, 1, 4].length) (baseStart_4566807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4566807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4566807 prefixEnd_4566807 := by exact prefixLift 4566807
  have htrace : WordTrace (prefixWord ++ tailWord_4566807) baseStart_4566807 baseEnd_4566807 := by
    simpa [prefixWord, tailWord_4566807, baseEnd_4566807] using wordTrace_append hprefix tailTrace_4566807
  have hstable : (prefixWord ++ tailWord_4566807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4566807).length < 2 ^ (prefixWord ++ tailWord_4566807).sum := by decide
  have hdescent : baseEnd_4566807 < baseStart_4566807 := by decide
  rcases family_descends (prefixWord ++ tailWord_4566807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4566817 : List Nat := [1, 2, 3, 2, 1, 3, 3, 2, 2, 4]
def baseStart_4566817 : Nat := 118140960795 + 4566817 * 2 ^ 59
def prefixEnd_4566817 : Nat := 4983230072969 + 3 ^ 40 * 4566817 * 2
def baseEnd_4566817 : Nat := 781657394041321347061699

theorem tailTrace_4566817 : CollatzResearch.WordTrace tailWord_4566817 prefixEnd_4566817 781657394041321347061699 := by
  unfold tailWord_4566817
  simp only [CollatzResearch.WordTrace]
  refine ⟨166565499896209434093698705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111043666597472956062465803 166565499896209434093698705)
  ·
    refine ⟨124924124922157075570274029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 166565499896209434093698705 124924124922157075570274029)
    ·
      refine ⟨46846546845808903338852761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 124924124922157075570274029 46846546845808903338852761)
      ·
        refine ⟨35134910134356677504139571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46846546845808903338852761 35134910134356677504139571)
        ·
          refine ⟨52702365201535016256209357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35134910134356677504139571 52702365201535016256209357)
          ·
            refine ⟨19763386950575631096078509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 52702365201535016256209357 19763386950575631096078509)
            ·
              refine ⟨7411270106465861661029441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19763386950575631096078509 7411270106465861661029441)
              ·
                refine ⟨5558452579849396245772081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7411270106465861661029441 5558452579849396245772081)
                ·
                  refine ⟨4168839434887047184329061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5558452579849396245772081 4168839434887047184329061)
                  ·
                    refine ⟨781657394041321347061699, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4168839434887047184329061 781657394041321347061699)
                    ·
                      rfl

theorem cell23_4566817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 3, 2, 2, 4].length) (baseStart_4566817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4566817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4566817 prefixEnd_4566817 := by exact prefixLift 4566817
  have htrace : WordTrace (prefixWord ++ tailWord_4566817) baseStart_4566817 baseEnd_4566817 := by
    simpa [prefixWord, tailWord_4566817, baseEnd_4566817] using wordTrace_append hprefix tailTrace_4566817
  have hstable : (prefixWord ++ tailWord_4566817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4566817).length < 2 ^ (prefixWord ++ tailWord_4566817).sum := by decide
  have hdescent : baseEnd_4566817 < baseStart_4566817 := by decide
  rcases family_descends (prefixWord ++ tailWord_4566817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4566824 : List Nat := [2, 1, 5, 1, 1, 2, 1, 3, 3, 2, 2]
def baseStart_4566824 : Nat := 118140960795 + 4566824 * 2 ^ 59
def prefixEnd_4566824 : Nat := 4983230072969 + 3 ^ 40 * 4566824 * 2
def baseEnd_4566824 : Nat := 2344975776488545513797565

theorem tailTrace_4566824 : CollatzResearch.WordTrace tailWord_4566824 prefixEnd_4566824 2344975776488545513797565 := by
  unfold tailWord_4566824
  simp only [CollatzResearch.WordTrace]
  refine ⟨83282877603592037144601763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111043836804789382859469017 83282877603592037144601763)
  ·
    refine ⟨124924316405388055716902645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83282877603592037144601763 124924316405388055716902645)
    ·
      refine ⟨11711654663005130223459623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 124924316405388055716902645 11711654663005130223459623)
      ·
        refine ⟨17567481994507695335189435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11711654663005130223459623 17567481994507695335189435)
        ·
          refine ⟨26351222991761543002784153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17567481994507695335189435 26351222991761543002784153)
          ·
            refine ⟨19763417243821157252088115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26351222991761543002784153 19763417243821157252088115)
            ·
              refine ⟨29645125865731735878132173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19763417243821157252088115 29645125865731735878132173)
              ·
                refine ⟨11116922199649400954299565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29645125865731735878132173 11116922199649400954299565)
                ·
                  refine ⟨4168845824868525357862337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11116922199649400954299565 4168845824868525357862337)
                  ·
                    refine ⟨3126634368651394018396753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4168845824868525357862337 3126634368651394018396753)
                    ·
                      refine ⟨2344975776488545513797565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3126634368651394018396753 2344975776488545513797565)
                      ·
                        rfl

theorem cell23_4566824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 1, 3, 3, 2, 2].length) (baseStart_4566824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4566824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4566824 prefixEnd_4566824 := by exact prefixLift 4566824
  have htrace : WordTrace (prefixWord ++ tailWord_4566824) baseStart_4566824 baseEnd_4566824 := by
    simpa [prefixWord, tailWord_4566824, baseEnd_4566824] using wordTrace_append hprefix tailTrace_4566824
  have hstable : (prefixWord ++ tailWord_4566824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4566824).length < 2 ^ (prefixWord ++ tailWord_4566824).sum := by decide
  have hdescent : baseEnd_4566824 < baseStart_4566824 := by decide
  rcases family_descends (prefixWord ++ tailWord_4566824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4566834 : List Nat := [3, 2, 1, 1, 3, 3, 3, 1, 2, 4]
def baseStart_4566834 : Nat := 118140960795 + 4566834 * 2 ^ 59
def prefixEnd_4566834 : Nat := 4983230072969 + 3 ^ 40 * 4566834 * 2
def baseEnd_4566834 : Nat := 781660303765030158224173

theorem tailTrace_4566834 : CollatzResearch.WordTrace tailWord_4566834 prefixEnd_4566834 781660303765030158224173 := by
  unfold tailWord_4566834
  simp only [CollatzResearch.WordTrace]
  refine ⟨41641529984286961499266889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 111044079958098563998045037 41641529984286961499266889)
  ·
    refine ⟨31231147488215221124450167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41641529984286961499266889 31231147488215221124450167)
    ·
      refine ⟨46846721232322831686675251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31231147488215221124450167 46846721232322831686675251)
      ·
        refine ⟨70270081848484247530012877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46846721232322831686675251 70270081848484247530012877)
        ·
          refine ⟨26351280693181592823754829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 70270081848484247530012877 26351280693181592823754829)
          ·
            refine ⟨9881730259943097308908061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26351280693181592823754829 9881730259943097308908061)
            ·
              refine ⟨3705648847478661490840523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9881730259943097308908061 3705648847478661490840523)
              ·
                refine ⟨5558473271217992236260785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3705648847478661490840523 5558473271217992236260785)
                ·
                  refine ⟨4168854953413494177195589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5558473271217992236260785 4168854953413494177195589)
                  ·
                    refine ⟨781660303765030158224173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4168854953413494177195589 781660303765030158224173)
                    ·
                      rfl

theorem cell23_4566834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 3, 3, 1, 2, 4].length) (baseStart_4566834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4566834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4566834 prefixEnd_4566834 := by exact prefixLift 4566834
  have htrace : WordTrace (prefixWord ++ tailWord_4566834) baseStart_4566834 baseEnd_4566834 := by
    simpa [prefixWord, tailWord_4566834, baseEnd_4566834] using wordTrace_append hprefix tailTrace_4566834
  have hstable : (prefixWord ++ tailWord_4566834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4566834).length < 2 ^ (prefixWord ++ tailWord_4566834).sum := by decide
  have hdescent : baseEnd_4566834 < baseStart_4566834 := by decide
  rcases family_descends (prefixWord ++ tailWord_4566834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4566847 : List Nat := [1, 1, 2, 2, 6, 2, 2, 7]
def baseStart_4566847 : Nat := 118140960795 + 4566847 * 2 ^ 59
def prefixEnd_4566847 : Nat := 4983230072969 + 3 ^ 40 * 4566847 * 2
def baseEnd_4566847 : Nat := 86851392094207367548517

theorem tailTrace_4566847 : CollatzResearch.WordTrace tailWord_4566847 prefixEnd_4566847 86851392094207367548517 := by
  unfold tailWord_4566847
  simp only [CollatzResearch.WordTrace]
  refine ⟨166566594086100749217290795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111044396057400499478193863 166566594086100749217290795)
  ·
    refine ⟨249849891129151123825936193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 166566594086100749217290795 249849891129151123825936193)
    ·
      refine ⟨187387418346863342869452145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 249849891129151123825936193 187387418346863342869452145)
      ·
        refine ⟨140540563760147507152089109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 187387418346863342869452145 140540563760147507152089109)
        ·
          refine ⟨6587838926256914397754177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 140540563760147507152089109 6587838926256914397754177)
          ·
            refine ⟨4940879194692685798315633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6587838926256914397754177 4940879194692685798315633)
            ·
              refine ⟨3705659396019514348736725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4940879194692685798315633 3705659396019514348736725)
              ·
                refine ⟨86851392094207367548517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3705659396019514348736725 86851392094207367548517)
                ·
                  rfl

theorem cell23_4566847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 2, 2, 7].length) (baseStart_4566847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4566847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4566847 prefixEnd_4566847 := by exact prefixLift 4566847
  have htrace : WordTrace (prefixWord ++ tailWord_4566847) baseStart_4566847 baseEnd_4566847 := by
    simpa [prefixWord, tailWord_4566847, baseEnd_4566847] using wordTrace_append hprefix tailTrace_4566847
  have hstable : (prefixWord ++ tailWord_4566847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4566847).length < 2 ^ (prefixWord ++ tailWord_4566847).sum := by decide
  have hdescent : baseEnd_4566847 < baseStart_4566847 := by decide
  rcases family_descends (prefixWord ++ tailWord_4566847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4566853 : List Nat := [1, 3, 1, 1, 1, 2, 3, 1, 1, 4, 5]
def baseStart_4566853 : Nat := 118140960795 + 4566853 * 2 ^ 59
def prefixEnd_4566853 : Nat := 4983230072969 + 3 ^ 40 * 4566853 * 2
def baseEnd_4566853 : Nat := 2344990667427525900334931

theorem tailTrace_4566853 : CollatzResearch.WordTrace tailWord_4566853 prefixEnd_4566853 2344990667427525900334931 := by
  unfold tailWord_4566853
  simp only [CollatzResearch.WordTrace]
  refine ⟨166566812924079012242009213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111044541949386008161339475 166566812924079012242009213)
  ·
    refine ⟨62462554846529629590753455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 166566812924079012242009213 62462554846529629590753455)
    ·
      refine ⟨93693832269794444386130183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62462554846529629590753455 93693832269794444386130183)
      ·
        refine ⟨140540748404691666579195275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93693832269794444386130183 140540748404691666579195275)
        ·
          refine ⟨210811122607037499868792913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 140540748404691666579195275 210811122607037499868792913)
          ·
            refine ⟨158108341955278124901594685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 210811122607037499868792913 158108341955278124901594685)
            ·
              refine ⟨59290628233229296838098007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 158108341955278124901594685 59290628233229296838098007)
              ·
                refine ⟨88935942349843945257147011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 59290628233229296838098007 88935942349843945257147011)
                ·
                  refine ⟨133403913524765917885720517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 88935942349843945257147011 133403913524765917885720517)
                  ·
                    refine ⟨25013233785893609603572597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 133403913524765917885720517 25013233785893609603572597)
                    ·
                      refine ⟨2344990667427525900334931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25013233785893609603572597 2344990667427525900334931)
                      ·
                        rfl

theorem cell23_4566853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 3, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 3, 1, 1, 4, 5].length) (baseStart_4566853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4566853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4566853 prefixEnd_4566853 := by exact prefixLift 4566853
  have htrace : WordTrace (prefixWord ++ tailWord_4566853) baseStart_4566853 baseEnd_4566853 := by
    simpa [prefixWord, tailWord_4566853, baseEnd_4566853] using wordTrace_append hprefix tailTrace_4566853
  have hstable : (prefixWord ++ tailWord_4566853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4566853).length < 2 ^ (prefixWord ++ tailWord_4566853).sum := by decide
  have hdescent : baseEnd_4566853 < baseStart_4566853 := by decide
  rcases family_descends (prefixWord ++ tailWord_4566853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4566897 : List Nat := [1, 2, 2, 2, 1, 3, 2, 3, 1, 4, 2]
def baseStart_4566897 : Nat := 118140960795 + 4566897 * 2 ^ 59
def prefixEnd_4566897 : Nat := 4983230072969 + 3 ^ 40 * 4566897 * 2
def baseEnd_4566897 : Nat := 2345013260576323728184729

theorem tailTrace_4566897 : CollatzResearch.WordTrace tailWord_4566897 prefixEnd_4566897 2345013260576323728184729 := by
  unfold tailWord_4566897
  simp only [CollatzResearch.WordTrace]
  refine ⟨166568417735919607756610945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111045611823946405171073963 166568417735919607756610945)
  ·
    refine ⟨124926313301939705817458209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 166568417735919607756610945 124926313301939705817458209)
    ·
      refine ⟨93694734976454779363093657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 124926313301939705817458209 93694734976454779363093657)
      ·
        refine ⟨70271051232341084522320243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 93694734976454779363093657 70271051232341084522320243)
        ·
          refine ⟨105406576848511626783480365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70271051232341084522320243 105406576848511626783480365)
          ·
            refine ⟨39527466318191860043805137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 105406576848511626783480365 39527466318191860043805137)
            ·
              refine ⟨29645599738643895032853853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39527466318191860043805137 29645599738643895032853853)
              ·
                refine ⟨11117099901991460637320195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29645599738643895032853853 11117099901991460637320195)
                ·
                  refine ⟨16675649852987190955980293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11117099901991460637320195 16675649852987190955980293)
                  ·
                    refine ⟨3126684347435098304246305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16675649852987190955980293 3126684347435098304246305)
                    ·
                      refine ⟨2345013260576323728184729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3126684347435098304246305 2345013260576323728184729)
                      ·
                        rfl

theorem cell23_4566897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 2, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 2, 3, 1, 4, 2].length) (baseStart_4566897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4566897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4566897 prefixEnd_4566897 := by exact prefixLift 4566897
  have htrace : WordTrace (prefixWord ++ tailWord_4566897) baseStart_4566897 baseEnd_4566897 := by
    simpa [prefixWord, tailWord_4566897, baseEnd_4566897] using wordTrace_append hprefix tailTrace_4566897
  have hstable : (prefixWord ++ tailWord_4566897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4566897).length < 2 ^ (prefixWord ++ tailWord_4566897).sum := by decide
  have hdescent : baseEnd_4566897 < baseStart_4566897 := by decide
  rcases family_descends (prefixWord ++ tailWord_4566897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4566987 : List Nat := [1, 1, 1, 1, 3, 4, 1, 1, 4, 4, 2]
def baseStart_4566987 : Nat := 118140960795 + 4566987 * 2 ^ 59
def prefixEnd_4566987 : Nat := 4983230072969 + 3 ^ 40 * 4566987 * 2
def baseEnd_4566987 : Nat := 2345059473835228376059315

theorem tailTrace_4566987 : CollatzResearch.WordTrace tailWord_4566987 prefixEnd_4566987 2345059473835228376059315 := by
  unfold tailWord_4566987
  simp only [CollatzResearch.WordTrace]
  refine ⟨166571700305593553127387215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111047800203729035418258143 166571700305593553127387215)
  ·
    refine ⟨249857550458390329691080823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 166571700305593553127387215 249857550458390329691080823)
    ·
      refine ⟨374786325687585494536621235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 249857550458390329691080823 374786325687585494536621235)
      ·
        refine ⟨562179488531378241804931853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 374786325687585494536621235 562179488531378241804931853)
        ·
          refine ⟨210817308199266840676849445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 562179488531378241804931853 210817308199266840676849445)
          ·
            refine ⟨39528245287362532626909271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 210817308199266840676849445 39528245287362532626909271)
            ·
              refine ⟨59292367931043798940363907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39528245287362532626909271 59292367931043798940363907)
              ·
                refine ⟨88938551896565698410545861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 59292367931043798940363907 88938551896565698410545861)
                ·
                  refine ⟨16675978480606068451977349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 88938551896565698410545861 16675978480606068451977349)
                  ·
                    refine ⟨3126745965113637834745753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16675978480606068451977349 3126745965113637834745753)
                    ·
                      refine ⟨2345059473835228376059315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3126745965113637834745753 2345059473835228376059315)
                      ·
                        rfl

theorem cell23_4566987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 1, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 1, 1, 4, 4, 2].length) (baseStart_4566987 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4566987 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4566987 prefixEnd_4566987 := by exact prefixLift 4566987
  have htrace : WordTrace (prefixWord ++ tailWord_4566987) baseStart_4566987 baseEnd_4566987 := by
    simpa [prefixWord, tailWord_4566987, baseEnd_4566987] using wordTrace_append hprefix tailTrace_4566987
  have hstable : (prefixWord ++ tailWord_4566987).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4566987).length < 2 ^ (prefixWord ++ tailWord_4566987).sum := by decide
  have hdescent : baseEnd_4566987 < baseStart_4566987 := by decide
  rcases family_descends (prefixWord ++ tailWord_4566987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4567000 : List Nat := [2, 1, 2, 2, 2, 2, 1, 2, 2, 1, 6]
def baseStart_4567000 : Nat := 118140960795 + 4567000 * 2 ^ 59
def prefixEnd_4567000 : Nat := 4983230072969 + 3 ^ 40 * 4567000 * 2
def baseEnd_4567000 : Nat := 2345066149083736825196755

theorem tailTrace_4567000 : CollatzResearch.WordTrace tailWord_4567000 prefixEnd_4567000 2345066149083736825196755 := by
  unfold tailWord_4567000
  simp only [CollatzResearch.WordTrace]
  refine ⟨83286087227273228173805227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111048116303030970898406969 83286087227273228173805227)
  ·
    refine ⟨124929130840909842260707841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83286087227273228173805227 124929130840909842260707841)
    ·
      refine ⟨93696848130682381695530881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 124929130840909842260707841 93696848130682381695530881)
      ·
        refine ⟨70272636098011786271648161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 93696848130682381695530881 70272636098011786271648161)
        ·
          refine ⟨52704477073508839703736121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 70272636098011786271648161 52704477073508839703736121)
          ·
            refine ⟨39528357805131629777802091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52704477073508839703736121 39528357805131629777802091)
            ·
              refine ⟨59292536707697444666703137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39528357805131629777802091 59292536707697444666703137)
              ·
                refine ⟨44469402530773083500027353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 59292536707697444666703137 44469402530773083500027353)
                ·
                  refine ⟨33352051898079812625020515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 44469402530773083500027353 33352051898079812625020515)
                  ·
                    refine ⟨50028077847119718937530773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 33352051898079812625020515 50028077847119718937530773)
                    ·
                      refine ⟨2345066149083736825196755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 50028077847119718937530773 2345066149083736825196755)
                      ·
                        rfl

theorem cell23_4567000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 1, 2, 2, 1, 6].length) (baseStart_4567000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4567000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4567000 prefixEnd_4567000 := by exact prefixLift 4567000
  have htrace : WordTrace (prefixWord ++ tailWord_4567000) baseStart_4567000 baseEnd_4567000 := by
    simpa [prefixWord, tailWord_4567000, baseEnd_4567000] using wordTrace_append hprefix tailTrace_4567000
  have hstable : (prefixWord ++ tailWord_4567000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4567000).length < 2 ^ (prefixWord ++ tailWord_4567000).sum := by decide
  have hdescent : baseEnd_4567000 < baseStart_4567000 := by decide
  rcases family_descends (prefixWord ++ tailWord_4567000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4567007 : List Nat := [1, 1, 2, 3, 4, 1, 1, 2, 1, 4, 3]
def baseStart_4567007 : Nat := 118140960795 + 4567007 * 2 ^ 59
def prefixEnd_4567007 : Nat := 4983230072969 + 3 ^ 40 * 4567007 * 2
def baseEnd_4567007 : Nat := 2345069743448318297809223

theorem tailTrace_4567007 : CollatzResearch.WordTrace tailWord_4567007 prefixEnd_4567007 2345069743448318297809223 := by
  unfold tailWord_4567007
  simp only [CollatzResearch.WordTrace]
  refine ⟨166572429765521096543115275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111048286510347397695410183 166572429765521096543115275)
  ·
    refine ⟨249858644648281644814672913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 166572429765521096543115275 249858644648281644814672913)
    ·
      refine ⟨187393983486211233611004685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 249858644648281644814672913 187393983486211233611004685)
      ·
        refine ⟨70272743807329212604126757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 187393983486211233611004685 70272743807329212604126757)
        ·
          refine ⟨13176139463874227363273767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 70272743807329212604126757 13176139463874227363273767)
          ·
            refine ⟨19764209195811341044910651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13176139463874227363273767 19764209195811341044910651)
            ·
              refine ⟨29646313793717011567365977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19764209195811341044910651 29646313793717011567365977)
              ·
                refine ⟨22234735345287758675524483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29646313793717011567365977 22234735345287758675524483)
                ·
                  refine ⟨33352103017931638013286725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22234735345287758675524483 33352103017931638013286725)
                  ·
                    refine ⟨6253519315862182127491261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 33352103017931638013286725 6253519315862182127491261)
                    ·
                      refine ⟨2345069743448318297809223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6253519315862182127491261 2345069743448318297809223)
                      ·
                        rfl

theorem cell23_4567007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 1, 2, 1, 4, 3].length) (baseStart_4567007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4567007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4567007 prefixEnd_4567007 := by exact prefixLift 4567007
  have htrace : WordTrace (prefixWord ++ tailWord_4567007) baseStart_4567007 baseEnd_4567007 := by
    simpa [prefixWord, tailWord_4567007, baseEnd_4567007] using wordTrace_append hprefix tailTrace_4567007
  have hstable : (prefixWord ++ tailWord_4567007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4567007).length < 2 ^ (prefixWord ++ tailWord_4567007).sum := by decide
  have hdescent : baseEnd_4567007 < baseStart_4567007 := by decide
  rcases family_descends (prefixWord ++ tailWord_4567007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4567061 : List Nat := [1, 3, 2, 1, 5, 2, 2, 1, 6]
def baseStart_4567061 : Nat := 118140960795 + 4567061 * 2 ^ 59
def prefixEnd_4567061 : Nat := 4983230072969 + 3 ^ 40 * 4567061 * 2
def baseEnd_4567061 : Nat := 260566385711517898503775

theorem tailTrace_4567061 : CollatzResearch.WordTrace tailWord_4567061 prefixEnd_4567061 260566385711517898503775 := by
  unfold tailWord_4567061
  simp only [CollatzResearch.WordTrace]
  refine ⟨166574399307325463765581037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111049599538216975843720691 166574399307325463765581037)
  ·
    refine ⟨62465399740247048912092889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 166574399307325463765581037 62465399740247048912092889)
    ·
      refine ⟨46849049805185286684069667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62465399740247048912092889 46849049805185286684069667)
      ·
        refine ⟨70273574707777930026104501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46849049805185286684069667 70273574707777930026104501)
        ·
          refine ⟨6588147628854180939947297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 70273574707777930026104501 6588147628854180939947297)
          ·
            refine ⟨4941110721640635704960473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6588147628854180939947297 4941110721640635704960473)
            ·
              refine ⟨3705833041230476778720355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4941110721640635704960473 3705833041230476778720355)
              ·
                refine ⟨5558749561845715168080533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3705833041230476778720355 5558749561845715168080533)
                ·
                  refine ⟨260566385711517898503775, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5558749561845715168080533 260566385711517898503775)
                  ·
                    rfl

theorem cell23_4567061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 2, 2, 1, 6].length) (baseStart_4567061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4567061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4567061 prefixEnd_4567061 := by exact prefixLift 4567061
  have htrace : WordTrace (prefixWord ++ tailWord_4567061) baseStart_4567061 baseEnd_4567061 := by
    simpa [prefixWord, tailWord_4567061, baseEnd_4567061] using wordTrace_append hprefix tailTrace_4567061
  have hstable : (prefixWord ++ tailWord_4567061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4567061).length < 2 ^ (prefixWord ++ tailWord_4567061).sum := by decide
  have hdescent : baseEnd_4567061 < baseStart_4567061 := by decide
  rcases family_descends (prefixWord ++ tailWord_4567061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4567064 : List Nat := [2, 1, 2, 3, 2, 1, 1, 2, 4, 3, 2]
def baseStart_4567064 : Nat := 118140960795 + 4567064 * 2 ^ 59
def prefixEnd_4567064 : Nat := 4983230072969 + 3 ^ 40 * 4567064 * 2
def baseEnd_4567064 : Nat := 2345099011845624574796461

theorem tailTrace_4567064 : CollatzResearch.WordTrace tailWord_4567064 prefixEnd_4567064 2345099011845624574796461 := by
  unfold tailWord_4567064
  simp only [CollatzResearch.WordTrace]
  refine ⟨83287254363157297638970123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111049672484209730185293497 83287254363157297638970123)
  ·
    refine ⟨124930881544735946458455185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83287254363157297638970123 124930881544735946458455185)
    ·
      refine ⟨93698161158551959843841389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 124930881544735946458455185 93698161158551959843841389)
      ·
        refine ⟨35136810434456984941440521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 93698161158551959843841389 35136810434456984941440521)
        ·
          refine ⟨26352607825842738706080391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35136810434456984941440521 26352607825842738706080391)
          ·
            refine ⟨39528911738764108059120587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26352607825842738706080391 39528911738764108059120587)
            ·
              refine ⟨59293367608146162088680881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39528911738764108059120587 59293367608146162088680881)
              ·
                refine ⟨44470025706109621566510661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 59293367608146162088680881 44470025706109621566510661)
                ·
                  refine ⟨8338129819895554043720749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 44470025706109621566510661 8338129819895554043720749)
                  ·
                    refine ⟨3126798682460832766395281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8338129819895554043720749 3126798682460832766395281)
                    ·
                      refine ⟨2345099011845624574796461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3126798682460832766395281 2345099011845624574796461)
                      ·
                        rfl

theorem cell23_4567064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 1, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 1, 2, 4, 3, 2].length) (baseStart_4567064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4567064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4567064 prefixEnd_4567064 := by exact prefixLift 4567064
  have htrace : WordTrace (prefixWord ++ tailWord_4567064) baseStart_4567064 baseEnd_4567064 := by
    simpa [prefixWord, tailWord_4567064, baseEnd_4567064] using wordTrace_append hprefix tailTrace_4567064
  have hstable : (prefixWord ++ tailWord_4567064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4567064).length < 2 ^ (prefixWord ++ tailWord_4567064).sum := by decide
  have hdescent : baseEnd_4567064 < baseStart_4567064 := by decide
  rcases family_descends (prefixWord ++ tailWord_4567064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4567087 : List Nat := [1, 1, 2, 1, 2, 1, 1, 6, 4, 4]
def baseStart_4567087 : Nat := 118140960795 + 4567087 * 2 ^ 59
def prefixEnd_4567087 : Nat := 4983230072969 + 3 ^ 40 * 4567087 * 2
def baseEnd_4567087 : Nat := 781703607300225994936285

theorem tailTrace_4567087 : CollatzResearch.WordTrace tailWord_4567087 prefixEnd_4567087 781703607300225994936285 := by
  unfold tailWord_4567087
  simp only [CollatzResearch.WordTrace]
  refine ⟨166575347605231270206027515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111050231736820846804018343 166575347605231270206027515)
  ·
    refine ⟨249863021407846905309041273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 166575347605231270206027515 249863021407846905309041273)
    ·
      refine ⟨187397266055885178981780955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 249863021407846905309041273 187397266055885178981780955)
      ·
        refine ⟨281095899083827768472671433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 187397266055885178981780955 281095899083827768472671433)
        ·
          refine ⟨210821924312870826354503575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 281095899083827768472671433 210821924312870826354503575)
          ·
            refine ⟨316232886469306239531755363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 210821924312870826354503575 316232886469306239531755363)
            ·
              refine ⟨474349329703959359297633045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 316232886469306239531755363 474349329703959359297633045)
              ·
                refine ⟨22235124829873094967076549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 474349329703959359297633045 22235124829873094967076549)
                ·
                  refine ⟨4169085905601205306326853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22235124829873094967076549 4169085905601205306326853)
                  ·
                    refine ⟨781703607300225994936285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4169085905601205306326853 781703607300225994936285)
                    ·
                      rfl

theorem cell23_4567087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 6, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 6, 4, 4].length) (baseStart_4567087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4567087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4567087 prefixEnd_4567087 := by exact prefixLift 4567087
  have htrace : WordTrace (prefixWord ++ tailWord_4567087) baseStart_4567087 baseEnd_4567087 := by
    simpa [prefixWord, tailWord_4567087, baseEnd_4567087] using wordTrace_append hprefix tailTrace_4567087
  have hstable : (prefixWord ++ tailWord_4567087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4567087).length < 2 ^ (prefixWord ++ tailWord_4567087).sum := by decide
  have hdescent : baseEnd_4567087 < baseStart_4567087 := by decide
  rcases family_descends (prefixWord ++ tailWord_4567087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4567104 : List Nat := [2, 1, 1, 2, 2, 4, 1, 4, 2, 4]
def baseStart_4567104 : Nat := 118140960795 + 4567104 * 2 ^ 59
def prefixEnd_4567104 : Nat := 4983230072969 + 3 ^ 40 * 4567104 * 2
def baseEnd_4567104 : Nat := 781706517023934806098759

theorem tailTrace_4567104 : CollatzResearch.WordTrace tailWord_4567104 prefixEnd_4567104 781706517023934806098759 := by
  unfold tailWord_4567104
  simp only [CollatzResearch.WordTrace]
  refine ⟨83287983823084841054698183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111050645097446454739597577 83287983823084841054698183)
  ·
    refine ⟨124931975734627261582047275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83287983823084841054698183 124931975734627261582047275)
    ·
      refine ⟨187397963601940892373070913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 124931975734627261582047275 187397963601940892373070913)
      ·
        refine ⟨140548472701455669279803185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 187397963601940892373070913 140548472701455669279803185)
        ·
          refine ⟨105411354526091751959852389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 140548472701455669279803185 105411354526091751959852389)
          ·
            refine ⟨19764628973642203492472323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 105411354526091751959852389 19764628973642203492472323)
            ·
              refine ⟨29646943460463305238708485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19764628973642203492472323 29646943460463305238708485)
              ·
                refine ⟨5558801898836869732257841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 29646943460463305238708485 5558801898836869732257841)
                ·
                  refine ⟨4169101424127652299193381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5558801898836869732257841 4169101424127652299193381)
                  ·
                    refine ⟨781706517023934806098759, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4169101424127652299193381 781706517023934806098759)
                    ·
                      rfl

theorem cell23_4567104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 1, 4, 2, 4].length) (baseStart_4567104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4567104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4567104 prefixEnd_4567104 := by exact prefixLift 4567104
  have htrace : WordTrace (prefixWord ++ tailWord_4567104) baseStart_4567104 baseEnd_4567104 := by
    simpa [prefixWord, tailWord_4567104, baseEnd_4567104] using wordTrace_append hprefix tailTrace_4567104
  have hstable : (prefixWord ++ tailWord_4567104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4567104).length < 2 ^ (prefixWord ++ tailWord_4567104).sum := by decide
  have hdescent : baseEnd_4567104 < baseStart_4567104 := by decide
  rcases family_descends (prefixWord ++ tailWord_4567104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4567105 : List Nat := [1, 2, 5, 1, 2, 1, 4, 2, 1, 1, 3]
def baseStart_4567105 : Nat := 118140960795 + 4567105 * 2 ^ 59
def prefixEnd_4567105 : Nat := 4983230072969 + 3 ^ 40 * 4567105 * 2
def baseEnd_4567105 : Nat := 2345120064552458914383773

theorem tailTrace_4567105 : CollatzResearch.WordTrace tailWord_4567105 prefixEnd_4567105 2345120064552458914383773 := by
  unfold tailWord_4567105
  simp only [CollatzResearch.WordTrace]
  refine ⟨166576004119166059280182769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111050669412777372853455179 166576004119166059280182769)
  ·
    refine ⟨124932003089374544460137077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 166576004119166059280182769 124932003089374544460137077)
    ·
      refine ⟨11712375289628863543137851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 124932003089374544460137077 11712375289628863543137851)
      ·
        refine ⟨17568562934443295314706777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11712375289628863543137851 17568562934443295314706777)
        ·
          refine ⟨13176422200832471486030083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17568562934443295314706777 13176422200832471486030083)
          ·
            refine ⟨19764633301248707229045125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13176422200832471486030083 19764633301248707229045125)
            ·
              refine ⟨3705868743984132605445961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19764633301248707229045125 3705868743984132605445961)
              ·
                refine ⟨2779401557988099454084471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3705868743984132605445961 2779401557988099454084471)
                ·
                  refine ⟨4169102336982149181126707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2779401557988099454084471 4169102336982149181126707)
                  ·
                    refine ⟨6253653505473223771690061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4169102336982149181126707 6253653505473223771690061)
                    ·
                      refine ⟨2345120064552458914383773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6253653505473223771690061 2345120064552458914383773)
                      ·
                        rfl

theorem cell23_4567105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 4, 2, 1, 1, 3].length) (baseStart_4567105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4567105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4567105 prefixEnd_4567105 := by exact prefixLift 4567105
  have htrace : WordTrace (prefixWord ++ tailWord_4567105) baseStart_4567105 baseEnd_4567105 := by
    simpa [prefixWord, tailWord_4567105, baseEnd_4567105] using wordTrace_append hprefix tailTrace_4567105
  have hstable : (prefixWord ++ tailWord_4567105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4567105).length < 2 ^ (prefixWord ++ tailWord_4567105).sum := by decide
  have hdescent : baseEnd_4567105 < baseStart_4567105 := by decide
  rcases family_descends (prefixWord ++ tailWord_4567105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4567111 : List Nat := [1, 1, 4, 1, 3, 1, 2, 3, 3, 2, 2]
def baseStart_4567111 : Nat := 118140960795 + 4567111 * 2 ^ 59
def prefixEnd_4567111 : Nat := 4983230072969 + 3 ^ 40 * 4567111 * 2
def baseEnd_4567111 : Nat := 2345123145436385890908745

theorem tailTrace_4567111 : CollatzResearch.WordTrace tailWord_4567111 prefixEnd_4567111 2345123145436385890908745 := by
  unfold tailWord_4567111
  simp only [CollatzResearch.WordTrace]
  refine ⟨166576222957144322304901187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111050815304762881536600791 166576222957144322304901187)
  ·
    refine ⟨249864334435716483457351781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 166576222957144322304901187 249864334435716483457351781)
    ·
      refine ⟨46849562706696840648253459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 249864334435716483457351781 46849562706696840648253459)
      ·
        refine ⟨70274344060045260972380189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46849562706696840648253459 70274344060045260972380189)
        ·
          refine ⟨26352879022516972864642571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 70274344060045260972380189 26352879022516972864642571)
          ·
            refine ⟨39529318533775459296963857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26352879022516972864642571 39529318533775459296963857)
            ·
              refine ⟨29646988900331594472722893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39529318533775459296963857 29646988900331594472722893)
              ·
                refine ⟨11117620837624347927271085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29646988900331594472722893 11117620837624347927271085)
                ·
                  refine ⟨4169107814109130472726657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11117620837624347927271085 4169107814109130472726657)
                  ·
                    refine ⟨3126830860581847854544993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4169107814109130472726657 3126830860581847854544993)
                    ·
                      refine ⟨2345123145436385890908745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3126830860581847854544993 2345123145436385890908745)
                      ·
                        rfl

theorem cell23_4567111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 2, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 2, 3, 3, 2, 2].length) (baseStart_4567111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4567111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4567111 prefixEnd_4567111 := by exact prefixLift 4567111
  have htrace : WordTrace (prefixWord ++ tailWord_4567111) baseStart_4567111 baseEnd_4567111 := by
    simpa [prefixWord, tailWord_4567111, baseEnd_4567111] using wordTrace_append hprefix tailTrace_4567111
  have hstable : (prefixWord ++ tailWord_4567111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4567111).length < 2 ^ (prefixWord ++ tailWord_4567111).sum := by decide
  have hdescent : baseEnd_4567111 < baseStart_4567111 := by decide
  rcases family_descends (prefixWord ++ tailWord_4567111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4567148 : List Nat := [2, 2, 1, 1, 3, 5, 2, 1, 1, 2, 3]
def baseStart_4567148 : Nat := 118140960795 + 4567148 * 2 ^ 59
def prefixEnd_4567148 : Nat := 4983230072969 + 3 ^ 40 * 4567148 * 2
def baseEnd_4567148 : Nat := 2345142144220602246146075

theorem tailTrace_4567148 : CollatzResearch.WordTrace tailWord_4567148 prefixEnd_4567148 2345142144220602246146075 := by
  unfold tailWord_4567148
  simp only [CollatzResearch.WordTrace]
  refine ⟨83288786229005138811999049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111051714972006851749332065 83288786229005138811999049)
  ·
    refine ⟨62466589671753854108999287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83288786229005138811999049 62466589671753854108999287)
    ·
      refine ⟨93699884507630781163498931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62466589671753854108999287 93699884507630781163498931)
      ·
        refine ⟨140549826761446171745248397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93699884507630781163498931 140549826761446171745248397)
        ·
          refine ⟨52706185035542314404468149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 140549826761446171745248397 52706185035542314404468149)
          ·
            refine ⟨4941204847082091975418889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 52706185035542314404468149 4941204847082091975418889)
            ·
              refine ⟨3705903635311568981564167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4941204847082091975418889 3705903635311568981564167)
              ·
                refine ⟨5558855452967353472346251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3705903635311568981564167 5558855452967353472346251)
                ·
                  refine ⟨8338283179451030208519377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5558855452967353472346251 8338283179451030208519377)
                  ·
                    refine ⟨6253712384588272656389533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8338283179451030208519377 6253712384588272656389533)
                    ·
                      refine ⟨2345142144220602246146075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6253712384588272656389533 2345142144220602246146075)
                      ·
                        rfl

theorem cell23_4567148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 2, 3].length) (baseStart_4567148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4567148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4567148 prefixEnd_4567148 := by exact prefixLift 4567148
  have htrace : WordTrace (prefixWord ++ tailWord_4567148) baseStart_4567148 baseEnd_4567148 := by
    simpa [prefixWord, tailWord_4567148, baseEnd_4567148] using wordTrace_append hprefix tailTrace_4567148
  have hstable : (prefixWord ++ tailWord_4567148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4567148).length < 2 ^ (prefixWord ++ tailWord_4567148).sum := by decide
  have hdescent : baseEnd_4567148 < baseStart_4567148 := by decide
  rcases family_descends (prefixWord ++ tailWord_4567148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4567161 : List Nat := [1, 2, 1, 3, 4, 2, 1, 1, 4, 1, 3]
def baseStart_4567161 : Nat := 118140960795 + 4567161 * 2 ^ 59
def prefixEnd_4567161 : Nat := 4983230072969 + 3 ^ 40 * 4567161 * 2
def baseEnd_4567161 : Nat := 2345148819469110695283515

theorem tailTrace_4567161 : CollatzResearch.WordTrace tailWord_4567161 prefixEnd_4567161 2345148819469110695283515 := by
  unfold tailWord_4567161
  simp only [CollatzResearch.WordTrace]
  refine ⟨166578046606963180844221337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111052031071308787229480891 166578046606963180844221337)
  ·
    refine ⟨124933534955222385633166003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 166578046606963180844221337 124933534955222385633166003)
    ·
      refine ⟨187400302432833578449749005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 124933534955222385633166003 187400302432833578449749005)
      ·
        refine ⟨70275113412312591918655877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 187400302432833578449749005 70275113412312591918655877)
        ·
          refine ⟨13176583764808610984747977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 70275113412312591918655877 13176583764808610984747977)
          ·
            refine ⟨9882437823606458238560983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13176583764808610984747977 9882437823606458238560983)
            ·
              refine ⟨14823656735409687357841475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9882437823606458238560983 14823656735409687357841475)
              ·
                refine ⟨22235485103114531036762213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14823656735409687357841475 22235485103114531036762213)
                ·
                  refine ⟨4169153456833974569392915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22235485103114531036762213 4169153456833974569392915)
                  ·
                    refine ⟨6253730185250961854089373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4169153456833974569392915 6253730185250961854089373)
                    ·
                      refine ⟨2345148819469110695283515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6253730185250961854089373 2345148819469110695283515)
                      ·
                        rfl

theorem cell23_4567161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 2, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 2, 1, 1, 4, 1, 3].length) (baseStart_4567161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4567161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4567161 prefixEnd_4567161 := by exact prefixLift 4567161
  have htrace : WordTrace (prefixWord ++ tailWord_4567161) baseStart_4567161 baseEnd_4567161 := by
    simpa [prefixWord, tailWord_4567161, baseEnd_4567161] using wordTrace_append hprefix tailTrace_4567161
  have hstable : (prefixWord ++ tailWord_4567161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4567161).length < 2 ^ (prefixWord ++ tailWord_4567161).sum := by decide
  have hdescent : baseEnd_4567161 < baseStart_4567161 := by decide
  rcases family_descends (prefixWord ++ tailWord_4567161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4567177 : List Nat := [1, 2, 1, 1, 4, 2, 1, 3, 2, 6]
def baseStart_4567177 : Nat := 118140960795 + 4567177 * 2 ^ 59
def prefixEnd_4567177 : Nat := 4983230072969 + 3 ^ 40 * 4567177 * 2
def baseEnd_4567177 : Nat := 781719011719860877561147

theorem tailTrace_4567177 : CollatzResearch.WordTrace tailWord_4567177 prefixEnd_4567177 781719011719860877561147 := by
  unfold tailWord_4567177
  simp only [CollatzResearch.WordTrace]
  refine ⟨166578630174905215576803785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111052420116603477051202523 166578630174905215576803785)
  ·
    refine ⟨124933972631178911682602839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 166578630174905215576803785 124933972631178911682602839)
    ·
      refine ⟨187400958946768367523904259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 124933972631178911682602839 187400958946768367523904259)
      ·
        refine ⟨281101438420152551285856389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 187400958946768367523904259 281101438420152551285856389)
        ·
          refine ⟨52706519703778603366098073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 281101438420152551285856389 52706519703778603366098073)
          ·
            refine ⟨39529889777833952524573555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52706519703778603366098073 39529889777833952524573555)
            ·
              refine ⟨59294834666750928786860333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39529889777833952524573555 59294834666750928786860333)
              ·
                refine ⟨22235563000031598295072625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 59294834666750928786860333 22235563000031598295072625)
                ·
                  refine ⟨16676672250023698721304469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22235563000031598295072625 16676672250023698721304469)
                  ·
                    refine ⟨781719011719860877561147, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16676672250023698721304469 781719011719860877561147)
                    ·
                      rfl

theorem cell23_4567177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 1, 3, 2, 6].length) (baseStart_4567177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4567177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4567177 prefixEnd_4567177 := by exact prefixLift 4567177
  have htrace : WordTrace (prefixWord ++ tailWord_4567177) baseStart_4567177 baseEnd_4567177 := by
    simpa [prefixWord, tailWord_4567177, baseEnd_4567177] using wordTrace_append hprefix tailTrace_4567177
  have hstable : (prefixWord ++ tailWord_4567177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4567177).length < 2 ^ (prefixWord ++ tailWord_4567177).sum := by decide
  have hdescent : baseEnd_4567177 < baseStart_4567177 := by decide
  rcases family_descends (prefixWord ++ tailWord_4567177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4567187 : List Nat := [1, 1, 1, 2, 1, 2, 3, 4, 2, 1, 5]
def baseStart_4567187 : Nat := 118140960795 + 4567187 * 2 ^ 59
def prefixEnd_4567187 : Nat := 4983230072969 + 3 ^ 40 * 4567187 * 2
def baseEnd_4567187 : Nat := 2345162169966127593558395

theorem tailTrace_4567187 : CollatzResearch.WordTrace tailWord_4567187 prefixEnd_4567187 2345162169966127593558395 := by
  unfold tailWord_4567187
  simp only [CollatzResearch.WordTrace]
  refine ⟨166578994904868987284667815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111052663269912658189778543 166578994904868987284667815)
  ·
    refine ⟨249868492357303480927001723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 166578994904868987284667815 249868492357303480927001723)
    ·
      refine ⟨374802738535955221390502585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 249868492357303480927001723 374802738535955221390502585)
      ·
        refine ⟨281102053901966416042876939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 374802738535955221390502585 281102053901966416042876939)
        ·
          refine ⟨421653080852949624064315409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 281102053901966416042876939 421653080852949624064315409)
          ·
            refine ⟨316239810639712218048236557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 421653080852949624064315409 316239810639712218048236557)
            ·
              refine ⟨118589928989892081768088709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 316239810639712218048236557 118589928989892081768088709)
              ·
                refine ⟨22235611685604765331516633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 118589928989892081768088709 22235611685604765331516633)
                ·
                  refine ⟨16676708764203573998637475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22235611685604765331516633 16676708764203573998637475)
                  ·
                    refine ⟨25015063146305360997956213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16676708764203573998637475 25015063146305360997956213)
                    ·
                      refine ⟨2345162169966127593558395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25015063146305360997956213 2345162169966127593558395)
                      ·
                        rfl

theorem cell23_4567187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 4, 2, 1, 5].length) (baseStart_4567187 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4567187 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4567187 prefixEnd_4567187 := by exact prefixLift 4567187
  have htrace : WordTrace (prefixWord ++ tailWord_4567187) baseStart_4567187 baseEnd_4567187 := by
    simpa [prefixWord, tailWord_4567187, baseEnd_4567187] using wordTrace_append hprefix tailTrace_4567187
  have hstable : (prefixWord ++ tailWord_4567187).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4567187).length < 2 ^ (prefixWord ++ tailWord_4567187).sum := by decide
  have hdescent : baseEnd_4567187 < baseStart_4567187 := by decide
  rcases family_descends (prefixWord ++ tailWord_4567187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4567218 : List Nat := [3, 2, 1, 1, 1, 3, 2, 4, 2, 2, 2]
def baseStart_4567218 : Nat := 118140960795 + 4567218 * 2 ^ 59
def prefixEnd_4567218 : Nat := 4983230072969 + 3 ^ 40 * 4567218 * 2
def baseEnd_4567218 : Nat := 2345178087866416972270753

theorem tailTrace_4567218 : CollatzResearch.WordTrace tailWord_4567218 prefixEnd_4567218 2345178087866416972270753 := by
  unfold tailWord_4567218
  simp only [CollatzResearch.WordTrace]
  refine ⟨41645031391939169894761577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 111053417045171119719364205 41645031391939169894761577)
  ·
    refine ⟨31233773543954377421071183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41645031391939169894761577 31233773543954377421071183)
    ·
      refine ⟨46850660315931566131606775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31233773543954377421071183 46850660315931566131606775)
      ·
        refine ⟨70275990473897349197410163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46850660315931566131606775 70275990473897349197410163)
        ·
          refine ⟨105413985710846023796115245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70275990473897349197410163 105413985710846023796115245)
          ·
            refine ⟨39530244641567258923543217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 105413985710846023796115245 39530244641567258923543217)
            ·
              refine ⟨29647683481175444192657413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39530244641567258923543217 29647683481175444192657413)
              ·
                refine ⟨5558940652720395786123265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 29647683481175444192657413 5558940652720395786123265)
                ·
                  refine ⟨4169205489540296839592449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5558940652720395786123265 4169205489540296839592449)
                  ·
                    refine ⟨3126904117155222629694337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4169205489540296839592449 3126904117155222629694337)
                    ·
                      refine ⟨2345178087866416972270753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3126904117155222629694337 2345178087866416972270753)
                      ·
                        rfl

theorem cell23_4567218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 2, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 2, 4, 2, 2, 2].length) (baseStart_4567218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4567218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4567218 prefixEnd_4567218 := by exact prefixLift 4567218
  have htrace : WordTrace (prefixWord ++ tailWord_4567218) baseStart_4567218 baseEnd_4567218 := by
    simpa [prefixWord, tailWord_4567218, baseEnd_4567218] using wordTrace_append hprefix tailTrace_4567218
  have hstable : (prefixWord ++ tailWord_4567218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4567218).length < 2 ^ (prefixWord ++ tailWord_4567218).sum := by decide
  have hdescent : baseEnd_4567218 < baseStart_4567218 := by decide
  rcases family_descends (prefixWord ++ tailWord_4567218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4567237 : List Nat := [1, 3, 1, 1, 1, 1, 4, 1, 3, 7]
def baseStart_4567237 : Nat := 118140960795 + 4567237 * 2 ^ 59
def prefixEnd_4567237 : Nat := 4983230072969 + 3 ^ 40 * 4567237 * 2
def baseEnd_4567237 : Nat := 781729281332950799311055

theorem tailTrace_4567237 : CollatzResearch.WordTrace tailWord_4567237 prefixEnd_4567237 781729281332950799311055 := by
  unfold tailWord_4567237
  simp only [CollatzResearch.WordTrace]
  refine ⟨166580818554687845823987965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111053879036458563882658643 166580818554687845823987965)
  ·
    refine ⟨62467806958007942183995487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 166580818554687845823987965 62467806958007942183995487)
    ·
      refine ⟨93701710437011913275993231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62467806958007942183995487 93701710437011913275993231)
      ·
        refine ⟨140552565655517869913989847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93701710437011913275993231 140552565655517869913989847)
        ·
          refine ⟨210828848483276804870984771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 140552565655517869913989847 210828848483276804870984771)
          ·
            refine ⟨316243272724915207306477157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 210828848483276804870984771 316243272724915207306477157)
            ·
              refine ⟨59295613635921601369964467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 316243272724915207306477157 59295613635921601369964467)
              ·
                refine ⟨88943420453882402054946701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 59295613635921601369964467 88943420453882402054946701)
                ·
                  refine ⟨33353782670205900770605013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 88943420453882402054946701 33353782670205900770605013)
                  ·
                    refine ⟨781729281332950799311055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 33353782670205900770605013 781729281332950799311055)
                    ·
                      rfl

theorem cell23_4567237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 4, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 4, 1, 3, 7].length) (baseStart_4567237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4567237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4567237 prefixEnd_4567237 := by exact prefixLift 4567237
  have htrace : WordTrace (prefixWord ++ tailWord_4567237) baseStart_4567237 baseEnd_4567237 := by
    simpa [prefixWord, tailWord_4567237, baseEnd_4567237] using wordTrace_append hprefix tailTrace_4567237
  have hstable : (prefixWord ++ tailWord_4567237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4567237).length < 2 ^ (prefixWord ++ tailWord_4567237).sum := by decide
  have hdescent : baseEnd_4567237 < baseStart_4567237 := by decide
  rcases family_descends (prefixWord ++ tailWord_4567237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4567247 : List Nat := [1, 1, 2, 1, 1, 3, 3, 2, 1, 1, 7]
def baseStart_4567247 : Nat := 118140960795 + 4567247 * 2 ^ 59
def prefixEnd_4567247 : Nat := 4983230072969 + 3 ^ 40 * 4567247 * 2
def baseEnd_4567247 : Nat := 2345192978805397358808119

theorem tailTrace_4567247 : CollatzResearch.WordTrace tailWord_4567247 prefixEnd_4567247 2345192978805397358808119 := by
  unfold tailWord_4567247
  simp only [CollatzResearch.WordTrace]
  refine ⟨166581183284651617531851995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111054122189767745021234663 166581183284651617531851995)
  ·
    refine ⟨249871774926977426297777993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 166581183284651617531851995 249871774926977426297777993)
    ·
      refine ⟨187403831195233069723333495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 249871774926977426297777993 187403831195233069723333495)
      ·
        refine ⟨281105746792849604585000243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 187403831195233069723333495 281105746792849604585000243)
        ·
          refine ⟨421658620189274406877500365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 281105746792849604585000243 421658620189274406877500365)
          ·
            refine ⟨158121982570977902579062637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 421658620189274406877500365 158121982570977902579062637)
            ·
              refine ⟨59295743464116713467148489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 158121982570977902579062637 59295743464116713467148489)
              ·
                refine ⟨44471807598087535100361367, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 59295743464116713467148489 44471807598087535100361367)
                ·
                  refine ⟨66707711397131302650542051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 44471807598087535100361367 66707711397131302650542051)
                  ·
                    refine ⟨100061567095696953975813077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 66707711397131302650542051 100061567095696953975813077)
                    ·
                      refine ⟨2345192978805397358808119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 100061567095696953975813077 2345192978805397358808119)
                      ·
                        rfl

theorem cell23_4567247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 3, 2, 1, 1, 7].length) (baseStart_4567247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4567247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4567247 prefixEnd_4567247 := by exact prefixLift 4567247
  have htrace : WordTrace (prefixWord ++ tailWord_4567247) baseStart_4567247 baseEnd_4567247 := by
    simpa [prefixWord, tailWord_4567247, baseEnd_4567247] using wordTrace_append hprefix tailTrace_4567247
  have hstable : (prefixWord ++ tailWord_4567247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4567247).length < 2 ^ (prefixWord ++ tailWord_4567247).sum := by decide
  have hdescent : baseEnd_4567247 < baseStart_4567247 := by decide
  rcases family_descends (prefixWord ++ tailWord_4567247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4567271 : List Nat := [1, 1, 5, 3, 1, 1, 2, 2, 2, 5]
def baseStart_4567271 : Nat := 118140960795 + 4567271 * 2 ^ 59
def prefixEnd_4567271 : Nat := 4983230072969 + 3 ^ 40 * 4567271 * 2
def baseEnd_4567271 : Nat := 781735100780368421636003

theorem tailTrace_4567271 : CollatzResearch.WordTrace tailWord_4567271 prefixEnd_4567271 781735100780368421636003 := by
  unfold tailWord_4567271
  simp only [CollatzResearch.WordTrace]
  refine ⟨166582058636564669630725667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111054705757709779753817111 166582058636564669630725667)
  ·
    refine ⟨249873087954847004446088501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 166582058636564669630725667 249873087954847004446088501)
    ·
      refine ⟨23425601995766906666820797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 249873087954847004446088501 23425601995766906666820797)
      ·
        refine ⟨8784600748412590000057799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23425601995766906666820797 8784600748412590000057799)
        ·
          refine ⟨13176901122618885000086699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8784600748412590000057799 13176901122618885000086699)
          ·
            refine ⟨19765351683928327500130049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13176901122618885000086699 19765351683928327500130049)
            ·
              refine ⟨14824013762946245625097537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19765351683928327500130049 14824013762946245625097537)
              ·
                refine ⟨11118010322209684218823153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14824013762946245625097537 11118010322209684218823153)
                ·
                  refine ⟨8338507741657263164117365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11118010322209684218823153 8338507741657263164117365)
                  ·
                    refine ⟨781735100780368421636003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8338507741657263164117365 781735100780368421636003)
                    ·
                      rfl

theorem cell23_4567271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 2, 2, 2, 5].length) (baseStart_4567271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4567271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4567271 prefixEnd_4567271 := by exact prefixLift 4567271
  have htrace : WordTrace (prefixWord ++ tailWord_4567271) baseStart_4567271 baseEnd_4567271 := by
    simpa [prefixWord, tailWord_4567271, baseEnd_4567271] using wordTrace_append hprefix tailTrace_4567271
  have hstable : (prefixWord ++ tailWord_4567271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4567271).length < 2 ^ (prefixWord ++ tailWord_4567271).sum := by decide
  have hdescent : baseEnd_4567271 < baseStart_4567271 := by decide
  rcases family_descends (prefixWord ++ tailWord_4567271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4567344 : List Nat := [2, 1, 1, 1, 2, 2, 2, 4, 3, 5]
def baseStart_4567344 : Nat := 118140960795 + 4567344 * 2 ^ 59
def prefixEnd_4567344 : Nat := 4983230072969 + 3 ^ 40 * 4567344 * 2
def baseEnd_4567344 : Nat := 781747595476294493098391

theorem tailTrace_4567344 : CollatzResearch.WordTrace tailWord_4567344 prefixEnd_4567344 781747595476294493098391 := by
  unfold tailWord_4567344
  simp only [CollatzResearch.WordTrace]
  refine ⟨83292360582650101549066543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111056480776866802065422057 83292360582650101549066543)
  ·
    refine ⟨124938540873975152323599815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83292360582650101549066543 124938540873975152323599815)
    ·
      refine ⟨187407811310962728485399723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 124938540873975152323599815 187407811310962728485399723)
      ·
        refine ⟨281111716966444092728099585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 187407811310962728485399723 281111716966444092728099585)
        ·
          refine ⟨210833787724833069546074689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 281111716966444092728099585 210833787724833069546074689)
          ·
            refine ⟨158125340793624802159556017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 210833787724833069546074689 158125340793624802159556017)
            ·
              refine ⟨118594005595218601619667013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 158125340793624802159556017 118594005595218601619667013)
              ·
                refine ⟨22236376049103487803687565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 118594005595218601619667013 22236376049103487803687565)
                ·
                  refine ⟨8338641018413807926382837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22236376049103487803687565 8338641018413807926382837)
                  ·
                    refine ⟨781747595476294493098391, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8338641018413807926382837 781747595476294493098391)
                    ·
                      rfl

theorem cell23_4567344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 4, 3, 5].length) (baseStart_4567344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4567344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4567344 prefixEnd_4567344 := by exact prefixLift 4567344
  have htrace : WordTrace (prefixWord ++ tailWord_4567344) baseStart_4567344 baseEnd_4567344 := by
    simpa [prefixWord, tailWord_4567344, baseEnd_4567344] using wordTrace_append hprefix tailTrace_4567344
  have hstable : (prefixWord ++ tailWord_4567344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4567344).length < 2 ^ (prefixWord ++ tailWord_4567344).sum := by decide
  have hdescent : baseEnd_4567344 < baseStart_4567344 := by decide
  rcases family_descends (prefixWord ++ tailWord_4567344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4567391 : List Nat := [1, 1, 2, 3, 1, 2, 4, 1, 4, 4]
def baseStart_4567391 : Nat := 118140960795 + 4567391 * 2 ^ 59
def prefixEnd_4567391 : Nat := 4983230072969 + 3 ^ 40 * 4567391 * 2
def baseEnd_4567391 : Nat := 781755640006548265135819

theorem tailTrace_4567391 : CollatzResearch.WordTrace tailWord_4567391 prefixEnd_4567391 781755640006548265135819 := by
  unfold tailWord_4567391
  simp only [CollatzResearch.WordTrace]
  refine ⟨166586435396129930125094027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111057623597419953416729351 166586435396129930125094027)
  ·
    refine ⟨249879653094194895187641041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 166586435396129930125094027 249879653094194895187641041)
    ·
      refine ⟨187409739820646171390730781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 249879653094194895187641041 187409739820646171390730781)
      ·
        refine ⟨70278652432742314271524043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 187409739820646171390730781 70278652432742314271524043)
        ·
          refine ⟨105417978649113471407286065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70278652432742314271524043 105417978649113471407286065)
          ·
            refine ⟨79063483986835103555464549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 105417978649113471407286065 79063483986835103555464549)
            ·
              refine ⟨14824403247531581916649603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 79063483986835103555464549 14824403247531581916649603)
              ·
                refine ⟨22236604871297372874974405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14824403247531581916649603 22236604871297372874974405)
                ·
                  refine ⟨4169363413368257414057701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22236604871297372874974405 4169363413368257414057701)
                  ·
                    refine ⟨781755640006548265135819, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4169363413368257414057701 781755640006548265135819)
                    ·
                      rfl

theorem cell23_4567391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 4, 1, 4, 4].length) (baseStart_4567391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4567391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4567391 prefixEnd_4567391 := by exact prefixLift 4567391
  have htrace : WordTrace (prefixWord ++ tailWord_4567391) baseStart_4567391 baseEnd_4567391 := by
    simpa [prefixWord, tailWord_4567391, baseEnd_4567391] using wordTrace_append hprefix tailTrace_4567391
  have hstable : (prefixWord ++ tailWord_4567391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4567391).length < 2 ^ (prefixWord ++ tailWord_4567391).sum := by decide
  have hdescent : baseEnd_4567391 < baseStart_4567391 := by decide
  rcases family_descends (prefixWord ++ tailWord_4567391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4567392 : List Nat := [2, 1, 1, 3, 6, 1, 1, 1, 3, 1, 3]
def baseStart_4567392 : Nat := 118140960795 + 4567392 * 2 ^ 59
def prefixEnd_4567392 : Nat := 4983230072969 + 3 ^ 40 * 4567392 * 2
def baseEnd_4567392 : Nat := 2345267433500299291494953

theorem tailTrace_4567392 : CollatzResearch.WordTrace tailWord_4567392 prefixEnd_4567392 2345267433500299291494953 := by
  unfold tailWord_4567392
  simp only [CollatzResearch.WordTrace]
  refine ⟨83293235934563153647940215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111057647912750871530586953 83293235934563153647940215)
  ·
    refine ⟨124939853901844730471910323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83293235934563153647940215 124939853901844730471910323)
    ·
      refine ⟨187409780852767095707865485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 124939853901844730471910323 187409780852767095707865485)
      ·
        refine ⟨70278667819787660890449557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 187409780852767095707865485 70278667819787660890449557)
        ·
          refine ⟨3294312554052546604239823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 70278667819787660890449557 3294312554052546604239823)
          ·
            refine ⟨4941468831078819906359735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3294312554052546604239823 4941468831078819906359735)
            ·
              refine ⟨7412203246618229859539603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4941468831078819906359735 7412203246618229859539603)
              ·
                refine ⟨11118304869927344789309405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7412203246618229859539603 11118304869927344789309405)
                ·
                  refine ⟨4169364326222754295991027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11118304869927344789309405 4169364326222754295991027)
                  ·
                    refine ⟨6254046489334131443986541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4169364326222754295991027 6254046489334131443986541)
                    ·
                      refine ⟨2345267433500299291494953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6254046489334131443986541 2345267433500299291494953)
                      ·
                        rfl

theorem cell23_4567392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 6, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 6, 1, 1, 1, 3, 1, 3].length) (baseStart_4567392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4567392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4567392 prefixEnd_4567392 := by exact prefixLift 4567392
  have htrace : WordTrace (prefixWord ++ tailWord_4567392) baseStart_4567392 baseEnd_4567392 := by
    simpa [prefixWord, tailWord_4567392, baseEnd_4567392] using wordTrace_append hprefix tailTrace_4567392
  have hstable : (prefixWord ++ tailWord_4567392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4567392).length < 2 ^ (prefixWord ++ tailWord_4567392).sum := by decide
  have hdescent : baseEnd_4567392 < baseStart_4567392 := by decide
  rcases family_descends (prefixWord ++ tailWord_4567392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4567401 : List Nat := [1, 2, 1, 1, 1, 3, 4, 2, 3, 2, 3]
def baseStart_4567401 : Nat := 118140960795 + 4567401 * 2 ^ 59
def prefixEnd_4567401 : Nat := 4983230072969 + 3 ^ 40 * 4567401 * 2
def baseEnd_4567401 : Nat := 2345272054826189756282411

theorem tailTrace_4567401 : CollatzResearch.WordTrace tailWord_4567401 prefixEnd_4567401 2345272054826189756282411 := by
  unfold tailWord_4567401
  simp only [CollatzResearch.WordTrace]
  refine ⟨166586800126093701832958057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111057866750729134555305371 166586800126093701832958057)
  ·
    refine ⟨124940100094570276374718543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 166586800126093701832958057 124940100094570276374718543)
    ·
      refine ⟨187410150141855414562077815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 124940100094570276374718543 187410150141855414562077815)
      ·
        refine ⟨281115225212783121843116723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 187410150141855414562077815 281115225212783121843116723)
        ·
          refine ⟨421672837819174682764675085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 281115225212783121843116723 421672837819174682764675085)
          ·
            refine ⟨158127314182190506036753157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 421672837819174682764675085 158127314182190506036753157)
            ·
              refine ⟨29648871409160719881891217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 158127314182190506036753157 29648871409160719881891217)
              ·
                refine ⟨22236653556870539911418413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29648871409160719881891217 22236653556870539911418413)
                ·
                  refine ⟨8338745083826452466781905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22236653556870539911418413 8338745083826452466781905)
                  ·
                    refine ⟨6254058812869839350086429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8338745083826452466781905 6254058812869839350086429)
                    ·
                      refine ⟨2345272054826189756282411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6254058812869839350086429 2345272054826189756282411)
                      ·
                        rfl

theorem cell23_4567401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 4, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 4, 2, 3, 2, 3].length) (baseStart_4567401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4567401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4567401 prefixEnd_4567401 := by exact prefixLift 4567401
  have htrace : WordTrace (prefixWord ++ tailWord_4567401) baseStart_4567401 baseEnd_4567401 := by
    simpa [prefixWord, tailWord_4567401, baseEnd_4567401] using wordTrace_append hprefix tailTrace_4567401
  have hstable : (prefixWord ++ tailWord_4567401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4567401).length < 2 ^ (prefixWord ++ tailWord_4567401).sum := by decide
  have hdescent : baseEnd_4567401 < baseStart_4567401 := by decide
  rcases family_descends (prefixWord ++ tailWord_4567401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4567408 : List Nat := [2, 1, 1, 1, 4, 4, 1, 3, 2, 4]
def baseStart_4567408 : Nat := 118140960795 + 4567408 * 2 ^ 59
def prefixEnd_4567408 : Nat := 4983230072969 + 3 ^ 40 * 4567408 * 2
def baseEnd_4567408 : Nat := 781758549730257076298293

theorem tailTrace_4567408 : CollatzResearch.WordTrace tailWord_4567408 prefixEnd_4567408 781758549730257076298293 := by
  unfold tailWord_4567408
  simp only [CollatzResearch.WordTrace]
  refine ⟨83293527718534171014231439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111058036958045561352308585 83293527718534171014231439)
  ·
    refine ⟨124940291577801256521347159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83293527718534171014231439 124940291577801256521347159)
    ·
      refine ⟨187410437366701884782020739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 124940291577801256521347159 187410437366701884782020739)
      ·
        refine ⟨281115656050052827173031109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 187410437366701884782020739 281115656050052827173031109)
        ·
          refine ⟨52709185509384905094943333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 281115656050052827173031109 52709185509384905094943333)
          ·
            refine ⟨9882972283009669705301875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 52709185509384905094943333 9882972283009669705301875)
            ·
              refine ⟨14824458424514504557952813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9882972283009669705301875 14824458424514504557952813)
              ·
                refine ⟨5559171909192939209232305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14824458424514504557952813 5559171909192939209232305)
                ·
                  refine ⟨4169378931894704406924229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5559171909192939209232305 4169378931894704406924229)
                  ·
                    refine ⟨781758549730257076298293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4169378931894704406924229 781758549730257076298293)
                    ·
                      rfl

theorem cell23_4567408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 4, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 4, 1, 3, 2, 4].length) (baseStart_4567408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4567408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4567408 prefixEnd_4567408 := by exact prefixLift 4567408
  have htrace : WordTrace (prefixWord ++ tailWord_4567408) baseStart_4567408 baseEnd_4567408 := by
    simpa [prefixWord, tailWord_4567408, baseEnd_4567408] using wordTrace_append hprefix tailTrace_4567408
  have hstable : (prefixWord ++ tailWord_4567408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4567408).length < 2 ^ (prefixWord ++ tailWord_4567408).sum := by decide
  have hdescent : baseEnd_4567408 < baseStart_4567408 := by decide
  rcases family_descends (prefixWord ++ tailWord_4567408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4567432 : List Nat := [2, 1, 3, 3, 1, 1, 2, 5, 1, 2, 2]
def baseStart_4567432 : Nat := 118140960795 + 4567432 * 2 ^ 59
def prefixEnd_4567432 : Nat := 4983230072969 + 3 ^ 40 * 4567432 * 2
def baseEnd_4567432 : Nat := 2345287972726479134994769

theorem tailTrace_4567432 : CollatzResearch.WordTrace tailWord_4567432 prefixEnd_4567432 2345287972726479134994769 := by
  unfold tailWord_4567432
  simp only [CollatzResearch.WordTrace]
  refine ⟨83293965394490697063668275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111058620525987596084891033 83293965394490697063668275)
  ·
    refine ⟨124940948091736045595502413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83293965394490697063668275 124940948091736045595502413)
    ·
      refine ⟨46852855534401017098313405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 124940948091736045595502413 46852855534401017098313405)
      ·
        refine ⟨17569820825400381411867527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46852855534401017098313405 17569820825400381411867527)
        ·
          refine ⟨26354731238100572117801291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17569820825400381411867527 26354731238100572117801291)
          ·
            refine ⟨39532096857150858176701937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26354731238100572117801291 39532096857150858176701937)
            ·
              refine ⟨29649072642863143632526453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39532096857150858176701937 29649072642863143632526453)
              ·
                refine ⟨2779600560268419715549355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 29649072642863143632526453 2779600560268419715549355)
                ·
                  refine ⟨4169400840402629573324033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2779600560268419715549355 4169400840402629573324033)
                  ·
                    refine ⟨3127050630301972179993025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4169400840402629573324033 3127050630301972179993025)
                    ·
                      refine ⟨2345287972726479134994769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3127050630301972179993025 2345287972726479134994769)
                      ·
                        rfl

theorem cell23_4567432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 2, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 2, 5, 1, 2, 2].length) (baseStart_4567432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4567432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4567432 prefixEnd_4567432 := by exact prefixLift 4567432
  have htrace : WordTrace (prefixWord ++ tailWord_4567432) baseStart_4567432 baseEnd_4567432 := by
    simpa [prefixWord, tailWord_4567432, baseEnd_4567432] using wordTrace_append hprefix tailTrace_4567432
  have hstable : (prefixWord ++ tailWord_4567432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4567432).length < 2 ^ (prefixWord ++ tailWord_4567432).sum := by decide
  have hdescent : baseEnd_4567432 < baseStart_4567432 := by decide
  rcases family_descends (prefixWord ++ tailWord_4567432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4567435 : List Nat := [1, 1, 1, 1, 4, 5, 3, 1, 1, 2, 3]
def baseStart_4567435 : Nat := 118140960795 + 4567435 * 2 ^ 59
def prefixEnd_4567435 : Nat := 4983230072969 + 3 ^ 40 * 4567435 * 2
def baseEnd_4567435 : Nat := 2345289513168442623257255

theorem tailTrace_4567435 : CollatzResearch.WordTrace tailWord_4567435 prefixEnd_4567435 2345289513168442623257255 := by
  unfold tailWord_4567435
  simp only [CollatzResearch.WordTrace]
  refine ⟨166588040207970525639695759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111058693471980350426463839 166588040207970525639695759)
  ·
    refine ⟨249882060311955788459543639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 166588040207970525639695759 249882060311955788459543639)
    ·
      refine ⟨374823090467933682689315459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 249882060311955788459543639 374823090467933682689315459)
      ·
        refine ⟨562234635701900524033973189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 374823090467933682689315459 562234635701900524033973189)
        ·
          refine ⟨105418994194106348256369973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 562234635701900524033973189 105418994194106348256369973)
          ·
            refine ⟨9883030705697470149034685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 105418994194106348256369973 9883030705697470149034685)
            ·
              refine ⟨3706136514636551305888007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9883030705697470149034685 3706136514636551305888007)
              ·
                refine ⟨5559204771954826958832011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3706136514636551305888007 5559204771954826958832011)
                ·
                  refine ⟨8338807157932240438248017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5559204771954826958832011 8338807157932240438248017)
                  ·
                    refine ⟨6254105368449180328686013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8338807157932240438248017 6254105368449180328686013)
                    ·
                      refine ⟨2345289513168442623257255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6254105368449180328686013 2345289513168442623257255)
                      ·
                        rfl

theorem cell23_4567435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 5, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 5, 3, 1, 1, 2, 3].length) (baseStart_4567435 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4567435 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4567435 prefixEnd_4567435 := by exact prefixLift 4567435
  have htrace : WordTrace (prefixWord ++ tailWord_4567435) baseStart_4567435 baseEnd_4567435 := by
    simpa [prefixWord, tailWord_4567435, baseEnd_4567435] using wordTrace_append hprefix tailTrace_4567435
  have hstable : (prefixWord ++ tailWord_4567435).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4567435).length < 2 ^ (prefixWord ++ tailWord_4567435).sum := by decide
  have hdescent : baseEnd_4567435 < baseStart_4567435 := by decide
  rcases family_descends (prefixWord ++ tailWord_4567435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4567466 : List Nat := [3, 1, 6, 1, 1, 1, 1, 2, 3, 2, 2]
def baseStart_4567466 : Nat := 118140960795 + 4567466 * 2 ^ 59
def prefixEnd_4567466 : Nat := 4983230072969 + 3 ^ 40 * 4567466 * 2
def baseEnd_4567466 : Nat := 2345305431068732001969613

theorem tailTrace_4567466 : CollatzResearch.WordTrace tailWord_4567466 prefixEnd_4567466 2345305431068732001969613 := by
  unfold tailWord_4567466
  simp only [CollatzResearch.WordTrace]
  refine ⟨41647292717714554483518563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 111059447247238811956049501 41647292717714554483518563)
  ·
    refine ⟨62470939076571831725277845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41647292717714554483518563 62470939076571831725277845)
    ·
      refine ⟨2928325269214304612122399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 62470939076571831725277845 2928325269214304612122399)
      ·
        refine ⟨4392487903821456918183599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2928325269214304612122399 4392487903821456918183599)
        ·
          refine ⟨6588731855732185377275399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4392487903821456918183599 6588731855732185377275399)
          ·
            refine ⟨9883097783598278065913099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6588731855732185377275399 9883097783598278065913099)
            ·
              refine ⟨14824646675397417098869649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9883097783598278065913099 14824646675397417098869649)
              ·
                refine ⟨11118485006548062824152237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14824646675397417098869649 11118485006548062824152237)
                ·
                  refine ⟨4169431877455523559057089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11118485006548062824152237 4169431877455523559057089)
                  ·
                    refine ⟨3127073908091642669292817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4169431877455523559057089 3127073908091642669292817)
                    ·
                      refine ⟨2345305431068732001969613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3127073908091642669292817 2345305431068732001969613)
                      ·
                        rfl

theorem cell23_4567466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 1, 1, 2, 3, 2, 2].length) (baseStart_4567466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4567466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4567466 prefixEnd_4567466 := by exact prefixLift 4567466
  have htrace : WordTrace (prefixWord ++ tailWord_4567466) baseStart_4567466 baseEnd_4567466 := by
    simpa [prefixWord, tailWord_4567466, baseEnd_4567466] using wordTrace_append hprefix tailTrace_4567466
  have hstable : (prefixWord ++ tailWord_4567466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4567466).length < 2 ^ (prefixWord ++ tailWord_4567466).sum := by decide
  have hdescent : baseEnd_4567466 < baseStart_4567466 := by decide
  rcases family_descends (prefixWord ++ tailWord_4567466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4567548 : List Nat := [2, 2, 2, 1, 2, 1, 1, 2, 1, 7, 2]
def baseStart_4567548 : Nat := 118140960795 + 4567548 * 2 ^ 59
def prefixEnd_4567548 : Nat := 4983230072969 + 3 ^ 40 * 4567548 * 2
def baseEnd_4567548 : Nat := 2345347536482400681144235

theorem tailTrace_4567548 : CollatzResearch.WordTrace tailWord_4567548 prefixEnd_4567548 2345347536482400681144235 := by
  unfold tailWord_4567548
  simp only [CollatzResearch.WordTrace]
  refine ⟨83296080828280572969279649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111061441104374097292372865 83296080828280572969279649)
  ·
    refine ⟨62472060621210429726959737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83296080828280572969279649 62472060621210429726959737)
    ·
      refine ⟨46854045465907822295219803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62472060621210429726959737 46854045465907822295219803)
      ·
        refine ⟨70281068198861733442829705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46854045465907822295219803 70281068198861733442829705)
        ·
          refine ⟨52710801149146300082122279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 70281068198861733442829705 52710801149146300082122279)
          ·
            refine ⟨79066201723719450123183419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52710801149146300082122279 79066201723719450123183419)
            ·
              refine ⟨118599302585579175184775129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 79066201723719450123183419 118599302585579175184775129)
              ·
                refine ⟨88949476939184381388581347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 118599302585579175184775129 88949476939184381388581347)
                ·
                  refine ⟨133424215408776572082872021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 88949476939184381388581347 133424215408776572082872021)
                  ·
                    refine ⟨3127130048643200908192313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 133424215408776572082872021 3127130048643200908192313)
                    ·
                      refine ⟨2345347536482400681144235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3127130048643200908192313 2345347536482400681144235)
                      ·
                        rfl

theorem cell23_4567548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 2, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 2, 1, 7, 2].length) (baseStart_4567548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4567548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4567548 prefixEnd_4567548 := by exact prefixLift 4567548
  have htrace : WordTrace (prefixWord ++ tailWord_4567548) baseStart_4567548 baseEnd_4567548 := by
    simpa [prefixWord, tailWord_4567548, baseEnd_4567548] using wordTrace_append hprefix tailTrace_4567548
  have hstable : (prefixWord ++ tailWord_4567548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4567548).length < 2 ^ (prefixWord ++ tailWord_4567548).sum := by decide
  have hdescent : baseEnd_4567548 < baseStart_4567548 := by decide
  rcases family_descends (prefixWord ++ tailWord_4567548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4567551 : List Nat := [1, 1, 2, 2, 1, 2, 4, 2, 1, 2, 5]
def baseStart_4567551 : Nat := 118140960795 + 4567551 * 2 ^ 59
def prefixEnd_4567551 : Nat := 4983230072969 + 3 ^ 40 * 4567551 * 2
def baseEnd_4567551 : Nat := 2345349076924364169406721

theorem tailTrace_4567551 : CollatzResearch.WordTrace tailWord_4567551 prefixEnd_4567551 2345349076924364169406721 := by
  unfold tailWord_4567551
  simp only [CollatzResearch.WordTrace]
  refine ⟨166592271075550277450918507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111061514050366851633945671 166592271075550277450918507)
  ·
    refine ⟨249888406613325416176377761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 166592271075550277450918507 249888406613325416176377761)
    ·
      refine ⟨187416304959994062132283321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 249888406613325416176377761 187416304959994062132283321)
      ·
        refine ⟨140562228719995546599212491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 187416304959994062132283321 140562228719995546599212491)
        ·
          refine ⟨210843343079993319898818737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 140562228719995546599212491 210843343079993319898818737)
          ·
            refine ⟨158132507309994989924114053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 210843343079993319898818737 158132507309994989924114053)
            ·
              refine ⟨29649845120624060610771385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 158132507309994989924114053 29649845120624060610771385)
              ·
                refine ⟨22237383840468045458078539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29649845120624060610771385 22237383840468045458078539)
                ·
                  refine ⟨33356075760702068187117809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22237383840468045458078539 33356075760702068187117809)
                  ·
                    refine ⟨25017056820526551140338357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 33356075760702068187117809 25017056820526551140338357)
                    ·
                      refine ⟨2345349076924364169406721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25017056820526551140338357 2345349076924364169406721)
                      ·
                        rfl

theorem cell23_4567551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 4, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 4, 2, 1, 2, 5].length) (baseStart_4567551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4567551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4567551 prefixEnd_4567551 := by exact prefixLift 4567551
  have htrace : WordTrace (prefixWord ++ tailWord_4567551) baseStart_4567551 baseEnd_4567551 := by
    simpa [prefixWord, tailWord_4567551, baseEnd_4567551] using wordTrace_append hprefix tailTrace_4567551
  have hstable : (prefixWord ++ tailWord_4567551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4567551).length < 2 ^ (prefixWord ++ tailWord_4567551).sum := by decide
  have hdescent : baseEnd_4567551 < baseStart_4567551 := by decide
  rcases family_descends (prefixWord ++ tailWord_4567551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4567561 : List Nat := [1, 2, 1, 1, 3, 1, 2, 2, 3, 3, 4]
def baseStart_4567561 : Nat := 118140960795 + 4567561 * 2 ^ 59
def prefixEnd_4567561 : Nat := 4983230072969 + 3 ^ 40 * 4567561 * 2
def baseEnd_4567561 : Nat := 2345354211730909130281675

theorem tailTrace_4567561 : CollatzResearch.WordTrace tailWord_4567561 prefixEnd_4567561 2345354211730909130281675 := by
  unfold tailWord_4567561
  simp only [CollatzResearch.WordTrace]
  refine ⟨166592635805514049158782537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111061757203676032772521691 166592635805514049158782537)
  ·
    refine ⟨124944476854135536869086903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 166592635805514049158782537 124944476854135536869086903)
    ·
      refine ⟨187416715281203305303630355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 124944476854135536869086903 187416715281203305303630355)
      ·
        refine ⟨281125072921804957955445533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 187416715281203305303630355 281125072921804957955445533)
        ·
          refine ⟨105421902345676859233292075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 281125072921804957955445533 105421902345676859233292075)
          ·
            refine ⟨158132853518515288849938113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 105421902345676859233292075 158132853518515288849938113)
            ·
              refine ⟨118599640138886466637453585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 158132853518515288849938113 118599640138886466637453585)
              ·
                refine ⟨88949730104164849978090189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 118599640138886466637453585 88949730104164849978090189)
                ·
                  refine ⟨33356148789061818741783821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 88949730104164849978090189 33356148789061818741783821)
                  ·
                    refine ⟨12508555795898182028168933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 33356148789061818741783821 12508555795898182028168933)
                    ·
                      refine ⟨2345354211730909130281675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12508555795898182028168933 2345354211730909130281675)
                      ·
                        rfl

theorem cell23_4567561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 2, 3, 3, 4].length) (baseStart_4567561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4567561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4567561 prefixEnd_4567561 := by exact prefixLift 4567561
  have htrace : WordTrace (prefixWord ++ tailWord_4567561) baseStart_4567561 baseEnd_4567561 := by
    simpa [prefixWord, tailWord_4567561, baseEnd_4567561] using wordTrace_append hprefix tailTrace_4567561
  have hstable : (prefixWord ++ tailWord_4567561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4567561).length < 2 ^ (prefixWord ++ tailWord_4567561).sum := by decide
  have hdescent : baseEnd_4567561 < baseStart_4567561 := by decide
  rcases family_descends (prefixWord ++ tailWord_4567561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4567601 : List Nat := [1, 2, 2, 3, 1, 1, 2, 1, 10]
def baseStart_4567601 : Nat := 118140960795 + 4567601 * 2 ^ 59
def prefixEnd_4567601 : Nat := 4983230072969 + 3 ^ 40 * 4567601 * 2
def baseEnd_4567601 : Nat := 260597194550787663753499

theorem tailTrace_4567601 : CollatzResearch.WordTrace tailWord_4567601 prefixEnd_4567601 260597194550787663753499 := by
  unfold tailWord_4567601
  simp only [CollatzResearch.WordTrace]
  refine ⟨166594094725369135990238657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111062729816912757326825771 166594094725369135990238657)
  ·
    refine ⟨124945571044026851992678993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 166594094725369135990238657 124945571044026851992678993)
    ·
      refine ⟨93709178283020138994509245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 124945571044026851992678993 93709178283020138994509245)
      ·
        refine ⟨35140941856132552122940967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 93709178283020138994509245 35140941856132552122940967)
        ·
          refine ⟨52711412784198828184411451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35140941856132552122940967 52711412784198828184411451)
          ·
            refine ⟨79067119176298242276617177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52711412784198828184411451 79067119176298242276617177)
            ·
              refine ⟨59300339382223681707462883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 79067119176298242276617177 59300339382223681707462883)
              ·
                refine ⟨88950509073335522561194325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 59300339382223681707462883 88950509073335522561194325)
                ·
                  refine ⟨260597194550787663753499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 88950509073335522561194325 260597194550787663753499)
                  ·
                    rfl

theorem cell23_4567601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 2, 1, 10].length) (baseStart_4567601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4567601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4567601 prefixEnd_4567601 := by exact prefixLift 4567601
  have htrace : WordTrace (prefixWord ++ tailWord_4567601) baseStart_4567601 baseEnd_4567601 := by
    simpa [prefixWord, tailWord_4567601, baseEnd_4567601] using wordTrace_append hprefix tailTrace_4567601
  have hstable : (prefixWord ++ tailWord_4567601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4567601).length < 2 ^ (prefixWord ++ tailWord_4567601).sum := by decide
  have hdescent : baseEnd_4567601 < baseStart_4567601 := by decide
  rcases family_descends (prefixWord ++ tailWord_4567601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4567648 : List Nat := [2, 1, 1, 3, 2, 1, 4, 1, 3, 5]
def baseStart_4567648 : Nat := 118140960795 + 4567648 * 2 ^ 59
def prefixEnd_4567648 : Nat := 4983230072969 + 3 ^ 40 * 4567648 * 2
def baseEnd_4567648 : Nat := 781799628182616763297925

theorem tailTrace_4567648 : CollatzResearch.WordTrace tailWord_4567648 prefixEnd_4567648 781799628182616763297925 := by
  unfold tailWord_4567648
  simp only [CollatzResearch.WordTrace]
  refine ⟨83297904478099431508599799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111063872637465908678133065 83297904478099431508599799)
  ·
    refine ⟨124946856717149147262899699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83297904478099431508599799 124946856717149147262899699)
    ·
      refine ⟨187420285075723720894349549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 124946856717149147262899699 187420285075723720894349549)
      ·
        refine ⟨70282606903396395335381081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 187420285075723720894349549 70282606903396395335381081)
        ·
          refine ⟨52711955177547296501535811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 70282606903396395335381081 52711955177547296501535811)
          ·
            refine ⟨79067932766320944752303717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52711955177547296501535811 79067932766320944752303717)
            ·
              refine ⟨14825237393685177141056947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 79067932766320944752303717 14825237393685177141056947)
              ·
                refine ⟨22237856090527765711585421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14825237393685177141056947 22237856090527765711585421)
                ·
                  refine ⟨8339196033947912141844533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22237856090527765711585421 8339196033947912141844533)
                  ·
                    refine ⟨781799628182616763297925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8339196033947912141844533 781799628182616763297925)
                    ·
                      rfl

theorem cell23_4567648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 4, 1, 3, 5].length) (baseStart_4567648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4567648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4567648 prefixEnd_4567648 := by exact prefixLift 4567648
  have htrace : WordTrace (prefixWord ++ tailWord_4567648) baseStart_4567648 baseEnd_4567648 := by
    simpa [prefixWord, tailWord_4567648, baseEnd_4567648] using wordTrace_append hprefix tailTrace_4567648
  have hstable : (prefixWord ++ tailWord_4567648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4567648).length < 2 ^ (prefixWord ++ tailWord_4567648).sum := by decide
  have hdescent : baseEnd_4567648 < baseStart_4567648 := by decide
  rcases family_descends (prefixWord ++ tailWord_4567648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4567669 : List Nat := [1, 3, 4, 2, 3, 1, 1, 2, 6]
def baseStart_4567669 : Nat := 118140960795 + 4567669 * 2 ^ 59
def prefixEnd_4567669 : Nat := 4983230072969 + 3 ^ 40 * 4567669 * 2
def baseEnd_4567669 : Nat := 260601074182399411970131

theorem tailTrace_4567669 : CollatzResearch.WordTrace tailWord_4567669 prefixEnd_4567669 260601074182399411970131 := by
  unfold tailWord_4567669
  simp only [CollatzResearch.WordTrace]
  refine ⟨166596574889122783603714061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111064383259415189069142707 166596574889122783603714061)
  ·
    refine ⟨62473715583421043851392773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 166596574889122783603714061 62473715583421043851392773)
    ·
      refine ⟨11713821671891445722136145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 62473715583421043851392773 11713821671891445722136145)
      ·
        refine ⟨8785366253918584291602109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11713821671891445722136145 8785366253918584291602109)
        ·
          refine ⟨3294512345219469109350791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8785366253918584291602109 3294512345219469109350791)
          ·
            refine ⟨4941768517829203664026187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3294512345219469109350791 4941768517829203664026187)
            ·
              refine ⟨7412652776743805496039281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4941768517829203664026187 7412652776743805496039281)
              ·
                refine ⟨5559489582557854122029461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7412652776743805496039281 5559489582557854122029461)
                ·
                  refine ⟨260601074182399411970131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5559489582557854122029461 260601074182399411970131)
                  ·
                    rfl

theorem cell23_4567669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 3, 1, 1, 2, 6].length) (baseStart_4567669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4567669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4567669 prefixEnd_4567669 := by exact prefixLift 4567669
  have htrace : WordTrace (prefixWord ++ tailWord_4567669) baseStart_4567669 baseEnd_4567669 := by
    simpa [prefixWord, tailWord_4567669, baseEnd_4567669] using wordTrace_append hprefix tailTrace_4567669
  have hstable : (prefixWord ++ tailWord_4567669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4567669).length < 2 ^ (prefixWord ++ tailWord_4567669).sum := by decide
  have hdescent : baseEnd_4567669 < baseStart_4567669 := by decide
  rcases family_descends (prefixWord ++ tailWord_4567669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4567713 : List Nat := [1, 2, 3, 3, 4, 1, 1, 3, 1, 1, 3]
def baseStart_4567713 : Nat := 118140960795 + 4567713 * 2 ^ 59
def prefixEnd_4567713 : Nat := 4983230072969 + 3 ^ 40 * 4567713 * 2
def baseEnd_4567713 : Nat := 2345432260790392535580977

theorem tailTrace_4567713 : CollatzResearch.WordTrace tailWord_4567713 prefixEnd_4567713 2345432260790392535580977 := by
  unfold tailWord_4567713
  simp only [CollatzResearch.WordTrace]
  refine ⟨166598179700963379118315793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111065453133975586078877195 166598179700963379118315793)
  ·
    refine ⟨124948634775722534338736845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 166598179700963379118315793 124948634775722534338736845)
    ·
      refine ⟨46855738040895950377026317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 124948634775722534338736845 46855738040895950377026317)
      ·
        refine ⟨17570901765335981391384869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46855738040895950377026317 17570901765335981391384869)
        ·
          refine ⟨3294544081000496510884663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17570901765335981391384869 3294544081000496510884663)
          ·
            refine ⟨4941816121500744766326995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3294544081000496510884663 4941816121500744766326995)
            ·
              refine ⟨7412724182251117149490493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4941816121500744766326995 7412724182251117149490493)
              ·
                refine ⟨2779771568344168931058935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7412724182251117149490493 2779771568344168931058935)
                ·
                  refine ⟨4169657352516253396588403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2779771568344168931058935 4169657352516253396588403)
                  ·
                    refine ⟨6254486028774380094882605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4169657352516253396588403 6254486028774380094882605)
                    ·
                      refine ⟨2345432260790392535580977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6254486028774380094882605 2345432260790392535580977)
                      ·
                        rfl

theorem cell23_4567713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 4, 1, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 4, 1, 1, 3, 1, 1, 3].length) (baseStart_4567713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4567713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4567713 prefixEnd_4567713 := by exact prefixLift 4567713
  have htrace : WordTrace (prefixWord ++ tailWord_4567713) baseStart_4567713 baseEnd_4567713 := by
    simpa [prefixWord, tailWord_4567713, baseEnd_4567713] using wordTrace_append hprefix tailTrace_4567713
  have hstable : (prefixWord ++ tailWord_4567713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4567713).length < 2 ^ (prefixWord ++ tailWord_4567713).sum := by decide
  have hdescent : baseEnd_4567713 < baseStart_4567713 := by decide
  rcases family_descends (prefixWord ++ tailWord_4567713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4567725 : List Nat := [1, 5, 2, 1, 1, 4, 9]
def baseStart_4567725 : Nat := 118140960795 + 4567725 * 2 ^ 59
def prefixEnd_4567725 : Nat := 4983230072969 + 3 ^ 40 * 4567725 * 2
def baseEnd_4567725 : Nat := 28956029908126499859641

theorem tailTrace_4567725 : CollatzResearch.WordTrace tailWord_4567725 prefixEnd_4567725 28956029908126499859641 := by
  unfold tailWord_4567725
  simp only [CollatzResearch.WordTrace]
  refine ⟨166598617376919905167752629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111065744917946603445168419 166598617376919905167752629)
  ·
    refine ⟨15618620379086241109476809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 166598617376919905167752629 15618620379086241109476809)
    ·
      refine ⟨11713965284314680832107607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15618620379086241109476809 11713965284314680832107607)
      ·
        refine ⟨17570947926472021248161411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11713965284314680832107607 17570947926472021248161411)
        ·
          refine ⟨26356421889708031872242117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17570947926472021248161411 26356421889708031872242117)
          ·
            refine ⟨4941829104320255976045397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 26356421889708031872242117 4941829104320255976045397)
            ·
              refine ⟨28956029908126499859641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 4941829104320255976045397 28956029908126499859641)
              ·
                rfl

theorem cell23_4567725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 4, 9].length) (baseStart_4567725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4567725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4567725 prefixEnd_4567725 := by exact prefixLift 4567725
  have htrace : WordTrace (prefixWord ++ tailWord_4567725) baseStart_4567725 baseEnd_4567725 := by
    simpa [prefixWord, tailWord_4567725, baseEnd_4567725] using wordTrace_append hprefix tailTrace_4567725
  have hstable : (prefixWord ++ tailWord_4567725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4567725).length < 2 ^ (prefixWord ++ tailWord_4567725).sum := by decide
  have hdescent : baseEnd_4567725 < baseStart_4567725 := by decide
  rcases family_descends (prefixWord ++ tailWord_4567725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4567738 : List Nat := [3, 1, 1, 1, 2, 3, 2, 1, 2, 7]
def baseStart_4567738 : Nat := 118140960795 + 4567738 * 2 ^ 59
def prefixEnd_4567738 : Nat := 4983230072969 + 3 ^ 40 * 4567738 * 2
def baseEnd_4567738 : Nat := 781815032602251645922787

theorem tailTrace_4567738 : CollatzResearch.WordTrace tailWord_4567738 prefixEnd_4567738 781815032602251645922787 := by
  unfold tailWord_4567738
  simp only [CollatzResearch.WordTrace]
  refine ⟨41649772881468202096993967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 111066061017248538925317245 41649772881468202096993967)
  ·
    refine ⟨62474659322202303145490951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41649772881468202096993967 62474659322202303145490951)
    ·
      refine ⟨93711988983303454718236427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62474659322202303145490951 93711988983303454718236427)
      ·
        refine ⟨140567983474955182077354641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93711988983303454718236427 140567983474955182077354641)
        ·
          refine ⟨105425987606216386558015981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 140567983474955182077354641 105425987606216386558015981)
          ·
            refine ⟨39534745352331144959255993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 105425987606216386558015981 39534745352331144959255993)
            ·
              refine ⟨29651059014248358719441995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39534745352331144959255993 29651059014248358719441995)
              ·
                refine ⟨44476588521372538079162993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29651059014248358719441995 44476588521372538079162993)
                ·
                  refine ⟨33357441391029403559372245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 44476588521372538079162993 33357441391029403559372245)
                  ·
                    refine ⟨781815032602251645922787, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 33357441391029403559372245 781815032602251645922787)
                    ·
                      rfl

theorem cell23_4567738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 2, 1, 2, 7].length) (baseStart_4567738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4567738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4567738 prefixEnd_4567738 := by exact prefixLift 4567738
  have htrace : WordTrace (prefixWord ++ tailWord_4567738) baseStart_4567738 baseEnd_4567738 := by
    simpa [prefixWord, tailWord_4567738, baseEnd_4567738] using wordTrace_append hprefix tailTrace_4567738
  have hstable : (prefixWord ++ tailWord_4567738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4567738).length < 2 ^ (prefixWord ++ tailWord_4567738).sum := by decide
  have hdescent : baseEnd_4567738 < baseStart_4567738 := by decide
  rcases family_descends (prefixWord ++ tailWord_4567738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4567788 : List Nat := [2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 6]
def baseStart_4567788 : Nat := 118140960795 + 4567788 * 2 ^ 59
def prefixEnd_4567788 : Nat := 4983230072969 + 3 ^ 40 * 4567788 * 2
def baseEnd_4567788 : Nat := 2345470771839479742143131

theorem tailTrace_4567788 : CollatzResearch.WordTrace tailWord_4567788 prefixEnd_4567788 2345470771839479742143131 := by
  unfold tailWord_4567788
  simp only [CollatzResearch.WordTrace]
  refine ⟨83300457587845833463648009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111067276783794444618197345 83300457587845833463648009)
  ·
    refine ⟨62475343190884375097736007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83300457587845833463648009 62475343190884375097736007)
    ·
      refine ⟨93713014786326562646604011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62475343190884375097736007 93713014786326562646604011)
      ·
        refine ⟨140569522179489843969906017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93713014786326562646604011 140569522179489843969906017)
        ·
          refine ⟨105427141634617382977429513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 140569522179489843969906017 105427141634617382977429513)
          ·
            refine ⟨79070356225963037233072135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 105427141634617382977429513 79070356225963037233072135)
            ·
              refine ⟨118605534338944555849608203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 79070356225963037233072135 118605534338944555849608203)
              ·
                refine ⟨177908301508416833774412305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 118605534338944555849608203 177908301508416833774412305)
                ·
                  refine ⟨133431226131312625330809229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 177908301508416833774412305 133431226131312625330809229)
                  ·
                    refine ⟨50036709799242234499053461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 133431226131312625330809229 50036709799242234499053461)
                    ·
                      refine ⟨2345470771839479742143131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 50036709799242234499053461 2345470771839479742143131)
                      ·
                        rfl

theorem cell23_4567788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 6].length) (baseStart_4567788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4567788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4567788 prefixEnd_4567788 := by exact prefixLift 4567788
  have htrace : WordTrace (prefixWord ++ tailWord_4567788) baseStart_4567788 baseEnd_4567788 := by
    simpa [prefixWord, tailWord_4567788, baseEnd_4567788] using wordTrace_append hprefix tailTrace_4567788
  have hstable : (prefixWord ++ tailWord_4567788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4567788).length < 2 ^ (prefixWord ++ tailWord_4567788).sum := by decide
  have hdescent : baseEnd_4567788 < baseStart_4567788 := by decide
  rcases family_descends (prefixWord ++ tailWord_4567788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4567805 : List Nat := [1, 4, 1, 1, 1, 1, 5, 1, 2, 2, 4]
def baseStart_4567805 : Nat := 118140960795 + 4567805 * 2 ^ 59
def prefixEnd_4567805 : Nat := 4983230072969 + 3 ^ 40 * 4567805 * 2
def baseEnd_4567805 : Nat := 2345479501010606175630553

theorem tailTrace_4567805 : CollatzResearch.WordTrace tailWord_4567805 prefixEnd_4567805 2345479501010606175630553 := by
  unfold tailWord_4567805
  simp only [CollatzResearch.WordTrace]
  refine ⟨166601535216630078830664869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111067690144420052553776579 166601535216630078830664869)
  ·
    refine ⟨31237787853118139780749663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 166601535216630078830664869 31237787853118139780749663)
    ·
      refine ⟨46856681779677209671124495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31237787853118139780749663 46856681779677209671124495)
      ·
        refine ⟨70285022669515814506686743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46856681779677209671124495 70285022669515814506686743)
        ·
          refine ⟨105427534004273721760030115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70285022669515814506686743 105427534004273721760030115)
          ·
            refine ⟨158141301006410582640045173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 105427534004273721760030115 158141301006410582640045173)
            ·
              refine ⟨14825746969350992122504235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 158141301006410582640045173 14825746969350992122504235)
              ·
                refine ⟨22238620454026488183756353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14825746969350992122504235 22238620454026488183756353)
                ·
                  refine ⟨16678965340519866137817265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22238620454026488183756353 16678965340519866137817265)
                  ·
                    refine ⟨12509224005389899603362949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16678965340519866137817265 12509224005389899603362949)
                    ·
                      refine ⟨2345479501010606175630553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12509224005389899603362949 2345479501010606175630553)
                      ·
                        rfl

theorem cell23_4567805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 5, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 5, 1, 2, 2, 4].length) (baseStart_4567805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4567805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4567805 prefixEnd_4567805 := by exact prefixLift 4567805
  have htrace : WordTrace (prefixWord ++ tailWord_4567805) baseStart_4567805 baseEnd_4567805 := by
    simpa [prefixWord, tailWord_4567805, baseEnd_4567805] using wordTrace_append hprefix tailTrace_4567805
  have hstable : (prefixWord ++ tailWord_4567805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4567805).length < 2 ^ (prefixWord ++ tailWord_4567805).sum := by decide
  have hdescent : baseEnd_4567805 < baseStart_4567805 := by decide
  rcases family_descends (prefixWord ++ tailWord_4567805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4567815 : List Nat := [1, 1, 4, 4, 1, 1, 1, 1, 9]
def baseStart_4567815 : Nat := 118140960795 + 4567815 * 2 ^ 59
def prefixEnd_4567815 : Nat := 4983230072969 + 3 ^ 40 * 4567815 * 2
def baseEnd_4567815 : Nat := 260609403979683459611723

theorem tailTrace_4567815 : CollatzResearch.WordTrace tailWord_4567815 prefixEnd_4567815 260609403979683459611723 := by
  unfold tailWord_4567815
  simp only [CollatzResearch.WordTrace]
  refine ⟨166601899946593850538528899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111067933297729233692352599 166601899946593850538528899)
  ·
    refine ⟨249902849919890775807793349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 166601899946593850538528899 249902849919890775807793349)
    ·
      refine ⟨46856784359979520463961253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 249902849919890775807793349 46856784359979520463961253)
      ·
        refine ⟨8785647067496160086992735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 46856784359979520463961253 8785647067496160086992735)
        ·
          refine ⟨13178470601244240130489103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8785647067496160086992735 13178470601244240130489103)
          ·
            refine ⟨19767705901866360195733655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13178470601244240130489103 19767705901866360195733655)
            ·
              refine ⟨29651558852799540293600483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19767705901866360195733655 29651558852799540293600483)
              ·
                refine ⟨44477338279199310440400725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29651558852799540293600483 44477338279199310440400725)
                ·
                  refine ⟨260609403979683459611723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 44477338279199310440400725 260609403979683459611723)
                  ·
                    rfl

theorem cell23_4567815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 1, 1, 9].length) (baseStart_4567815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4567815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4567815 prefixEnd_4567815 := by exact prefixLift 4567815
  have htrace : WordTrace (prefixWord ++ tailWord_4567815) baseStart_4567815 baseEnd_4567815 := by
    simpa [prefixWord, tailWord_4567815, baseEnd_4567815] using wordTrace_append hprefix tailTrace_4567815
  have hstable : (prefixWord ++ tailWord_4567815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4567815).length < 2 ^ (prefixWord ++ tailWord_4567815).sum := by decide
  have hdescent : baseEnd_4567815 < baseStart_4567815 := by decide
  rcases family_descends (prefixWord ++ tailWord_4567815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4567842 : List Nat := [3, 3, 1, 1, 2, 2, 1, 2, 2, 3, 3]
def baseStart_4567842 : Nat := 118140960795 + 4567842 * 2 ^ 59
def prefixEnd_4567842 : Nat := 4983230072969 + 3 ^ 40 * 4567842 * 2
def baseEnd_4567842 : Nat := 2345498499794822530867883

theorem tailTrace_4567842 : CollatzResearch.WordTrace tailWord_4567842 prefixEnd_4567842 2345498499794822530867883 := by
  unfold tailWord_4567842
  simp only [CollatzResearch.WordTrace]
  refine ⟨41650721179374008537440445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 111068589811664022766507853 41650721179374008537440445)
  ·
    refine ⟨15619020442265253201540167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41650721179374008537440445 15619020442265253201540167)
    ·
      refine ⟨23428530663397879802310251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15619020442265253201540167 23428530663397879802310251)
      ·
        refine ⟨35142795995096819703465377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23428530663397879802310251 35142795995096819703465377)
        ·
          refine ⟨26357096996322614777599033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35142795995096819703465377 26357096996322614777599033)
          ·
            refine ⟨19767822747241961083199275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26357096996322614777599033 19767822747241961083199275)
            ·
              refine ⟨29651734120862941624798913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19767822747241961083199275 29651734120862941624798913)
              ·
                refine ⟨22238800590647206218599185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29651734120862941624798913 22238800590647206218599185)
                ·
                  refine ⟨16679100442985404663949389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22238800590647206218599185 16679100442985404663949389)
                  ·
                    refine ⟨6254662666119526748981021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16679100442985404663949389 6254662666119526748981021)
                    ·
                      refine ⟨2345498499794822530867883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6254662666119526748981021 2345498499794822530867883)
                      ·
                        rfl

theorem cell23_4567842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 1, 2, 2, 3, 3].length) (baseStart_4567842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4567842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4567842 prefixEnd_4567842 := by exact prefixLift 4567842
  have htrace : WordTrace (prefixWord ++ tailWord_4567842) baseStart_4567842 baseEnd_4567842 := by
    simpa [prefixWord, tailWord_4567842, baseEnd_4567842] using wordTrace_append hprefix tailTrace_4567842
  have hstable : (prefixWord ++ tailWord_4567842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4567842).length < 2 ^ (prefixWord ++ tailWord_4567842).sum := by decide
  have hdescent : baseEnd_4567842 < baseStart_4567842 := by decide
  rcases family_descends (prefixWord ++ tailWord_4567842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4567845 : List Nat := [1, 3, 1, 2, 3, 1, 2, 1, 4, 5]
def baseStart_4567845 : Nat := 118140960795 + 4567845 * 2 ^ 59
def prefixEnd_4567845 : Nat := 4983230072969 + 3 ^ 40 * 4567845 * 2
def baseEnd_4567845 : Nat := 781833346745595339710123

theorem tailTrace_4567845 : CollatzResearch.WordTrace tailWord_4567845 prefixEnd_4567845 781833346745595339710123 := by
  unfold tailWord_4567845
  simp only [CollatzResearch.WordTrace]
  refine ⟨166602994136485165662120989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111068662757656777108080659 166602994136485165662120989)
  ·
    refine ⟨62476122801181937123295371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 166602994136485165662120989 62476122801181937123295371)
    ·
      refine ⟨93714184201772905684943057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62476122801181937123295371 93714184201772905684943057)
      ·
        refine ⟨70285638151329679263707293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 93714184201772905684943057 70285638151329679263707293)
        ·
          refine ⟨26357114306748629723890235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 70285638151329679263707293 26357114306748629723890235)
          ·
            refine ⟨39535671460122944585835353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26357114306748629723890235 39535671460122944585835353)
            ·
              refine ⟨29651753595092208439376515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39535671460122944585835353 29651753595092208439376515)
              ·
                refine ⟨44477630392638312659064773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29651753595092208439376515 44477630392638312659064773)
                ·
                  refine ⟨8339555698619683623574645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 44477630392638312659064773 8339555698619683623574645)
                  ·
                    refine ⟨781833346745595339710123, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8339555698619683623574645 781833346745595339710123)
                    ·
                      rfl

theorem cell23_4567845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 2, 1, 4, 5].length) (baseStart_4567845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4567845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4567845 prefixEnd_4567845 := by exact prefixLift 4567845
  have htrace : WordTrace (prefixWord ++ tailWord_4567845) baseStart_4567845 baseEnd_4567845 := by
    simpa [prefixWord, tailWord_4567845, baseEnd_4567845] using wordTrace_append hprefix tailTrace_4567845
  have hstable : (prefixWord ++ tailWord_4567845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4567845).length < 2 ^ (prefixWord ++ tailWord_4567845).sum := by decide
  have hdescent : baseEnd_4567845 < baseStart_4567845 := by decide
  rcases family_descends (prefixWord ++ tailWord_4567845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4567860 : List Nat := [2, 5, 1, 1, 3, 1, 3, 1, 2, 2, 2]
def baseStart_4567860 : Nat := 118140960795 + 4567860 * 2 ^ 59
def prefixEnd_4567860 : Nat := 4983230072969 + 3 ^ 40 * 4567860 * 2
def baseEnd_4567860 : Nat := 2345507742446603460442801

theorem tailTrace_4567860 : CollatzResearch.WordTrace tailWord_4567860 prefixEnd_4567860 2345507742446603460442801 := by
  unfold tailWord_4567860
  simp only [CollatzResearch.WordTrace]
  refine ⟨83301770615715411611958517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111069027487620548815944689 83301770615715411611958517)
  ·
    refine ⟨7809540995223319838621111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 83301770615715411611958517 7809540995223319838621111)
    ·
      refine ⟨11714311492834979757931667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7809540995223319838621111 11714311492834979757931667)
      ·
        refine ⟨17571467239252469636897501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11714311492834979757931667 17571467239252469636897501)
        ·
          refine ⟨6589300214719676113836563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17571467239252469636897501 6589300214719676113836563)
          ·
            refine ⟨9883950322079514170754845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6589300214719676113836563 9883950322079514170754845)
            ·
              refine ⟨3706481370779817814033067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9883950322079514170754845 3706481370779817814033067)
              ·
                refine ⟨5559722056169726721049601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3706481370779817814033067 5559722056169726721049601)
                ·
                  refine ⟨4169791542127295040787201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5559722056169726721049601 4169791542127295040787201)
                  ·
                    refine ⟨3127343656595471280590401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4169791542127295040787201 3127343656595471280590401)
                    ·
                      refine ⟨2345507742446603460442801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3127343656595471280590401 2345507742446603460442801)
                      ·
                        rfl

theorem cell23_4567860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 1, 3, 1, 2, 2, 2].length) (baseStart_4567860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4567860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4567860 prefixEnd_4567860 := by exact prefixLift 4567860
  have htrace : WordTrace (prefixWord ++ tailWord_4567860) baseStart_4567860 baseEnd_4567860 := by
    simpa [prefixWord, tailWord_4567860, baseEnd_4567860] using wordTrace_append hprefix tailTrace_4567860
  have hstable : (prefixWord ++ tailWord_4567860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4567860).length < 2 ^ (prefixWord ++ tailWord_4567860).sum := by decide
  have hdescent : baseEnd_4567860 < baseStart_4567860 := by decide
  rcases family_descends (prefixWord ++ tailWord_4567860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4567882 : List Nat := [3, 1, 2, 1, 1, 1, 2, 2, 4, 4, 2]
def baseStart_4567882 : Nat := 118140960795 + 4567882 * 2 ^ 59
def prefixEnd_4567882 : Nat := 4983230072969 + 3 ^ 40 * 4567882 * 2
def baseEnd_4567882 : Nat := 2345519039021002374367699

theorem tailTrace_4567882 : CollatzResearch.WordTrace tailWord_4567882 prefixEnd_4567882 2345519039021002374367699 := by
  unfold tailWord_4567882
  simp only [CollatzResearch.WordTrace]
  refine ⟨41651085909337780245304475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 111069562424900747320811933 41651085909337780245304475)
  ·
    refine ⟨62476628864006670367956713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41651085909337780245304475 62476628864006670367956713)
    ·
      refine ⟨46857471648005002775967535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62476628864006670367956713 46857471648005002775967535)
      ·
        refine ⟨70286207472007504163951303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46857471648005002775967535 70286207472007504163951303)
        ·
          refine ⟨105429311208011256245926955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70286207472007504163951303 105429311208011256245926955)
          ·
            refine ⟨158143966812016884368890433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 105429311208011256245926955 158143966812016884368890433)
            ·
              refine ⟨118607975109012663276667825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 158143966812016884368890433 118607975109012663276667825)
              ·
                refine ⟨88955981331759497457500869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 118607975109012663276667825 88955981331759497457500869)
                ·
                  refine ⟨16679246499704905773281413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 88955981331759497457500869 16679246499704905773281413)
                  ·
                    refine ⟨3127358718694669832490265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16679246499704905773281413 3127358718694669832490265)
                    ·
                      refine ⟨2345519039021002374367699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3127358718694669832490265 2345519039021002374367699)
                      ·
                        rfl

theorem cell23_4567882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 2, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 2, 4, 4, 2].length) (baseStart_4567882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4567882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4567882 prefixEnd_4567882 := by exact prefixLift 4567882
  have htrace : WordTrace (prefixWord ++ tailWord_4567882) baseStart_4567882 baseEnd_4567882 := by
    simpa [prefixWord, tailWord_4567882, baseEnd_4567882] using wordTrace_append hprefix tailTrace_4567882
  have hstable : (prefixWord ++ tailWord_4567882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4567882).length < 2 ^ (prefixWord ++ tailWord_4567882).sum := by decide
  have hdescent : baseEnd_4567882 < baseStart_4567882 := by decide
  rcases family_descends (prefixWord ++ tailWord_4567882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4567909 : List Nat := [1, 3, 1, 3, 1, 1, 2, 6, 1, 4]
def baseStart_4567909 : Nat := 118140960795 + 4567909 * 2 ^ 59
def prefixEnd_4567909 : Nat := 4983230072969 + 3 ^ 40 * 4567909 * 2
def baseEnd_4567909 : Nat := 781844300999557922910025

theorem tailTrace_4567909 : CollatzResearch.WordTrace tailWord_4567909 prefixEnd_4567909 781844300999557922910025 := by
  unfold tailWord_4567909
  simp only [CollatzResearch.WordTrace]
  refine ⟨166605328408253304592450781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111070218938835536394967187 166605328408253304592450781)
  ·
    refine ⟨62476998153094989222169043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 166605328408253304592450781 62476998153094989222169043)
    ·
      refine ⟨93715497229642483833253565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62476998153094989222169043 93715497229642483833253565)
      ·
        refine ⟨35143311461115931437470087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 93715497229642483833253565 35143311461115931437470087)
        ·
          refine ⟨52714967191673897156205131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35143311461115931437470087 52714967191673897156205131)
          ·
            refine ⟨79072450787510845734307697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52714967191673897156205131 79072450787510845734307697)
            ·
              refine ⟨59304338090633134300730773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 79072450787510845734307697 59304338090633134300730773)
              ·
                refine ⟨2779890847998428170346755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 59304338090633134300730773 2779890847998428170346755)
                ·
                  refine ⟨4169836271997642255520133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2779890847998428170346755 4169836271997642255520133)
                  ·
                    refine ⟨781844300999557922910025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4169836271997642255520133 781844300999557922910025)
                    ·
                      rfl

theorem cell23_4567909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 2, 6, 1, 4].length) (baseStart_4567909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4567909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4567909 prefixEnd_4567909 := by exact prefixLift 4567909
  have htrace : WordTrace (prefixWord ++ tailWord_4567909) baseStart_4567909 baseEnd_4567909 := by
    simpa [prefixWord, tailWord_4567909, baseEnd_4567909] using wordTrace_append hprefix tailTrace_4567909
  have hstable : (prefixWord ++ tailWord_4567909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4567909).length < 2 ^ (prefixWord ++ tailWord_4567909).sum := by decide
  have hdescent : baseEnd_4567909 < baseStart_4567909 := by decide
  rcases family_descends (prefixWord ++ tailWord_4567909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4567959 : List Nat := [1, 1, 3, 3, 1, 2, 1, 4, 2, 3, 2]
def baseStart_4567959 : Nat := 118140960795 + 4567959 * 2 ^ 59
def prefixEnd_4567959 : Nat := 4983230072969 + 3 ^ 40 * 4567959 * 2
def baseEnd_4567959 : Nat := 2345558577031398573104845

theorem tailTrace_4567959 : CollatzResearch.WordTrace tailWord_4567959 prefixEnd_4567959 2345558577031398573104845 := by
  unfold tailWord_4567959
  simp only [CollatzResearch.WordTrace]
  refine ⟨166607152058072163131770931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111071434705381442087847287 166607152058072163131770931)
  ·
    refine ⟨249910728087108244697656397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 166607152058072163131770931 249910728087108244697656397)
    ·
      refine ⟨93716523032665591761621149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 249910728087108244697656397 93716523032665591761621149)
      ·
        refine ⟨35143696137249596910607931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 93716523032665591761621149 35143696137249596910607931)
        ·
          refine ⟨52715544205874395365911897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35143696137249596910607931 52715544205874395365911897)
          ·
            refine ⟨39536658154405796524433923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52715544205874395365911897 39536658154405796524433923)
            ·
              refine ⟨59304987231608694786650885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39536658154405796524433923 59304987231608694786650885)
              ·
                refine ⟨11119685105926630272497041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 59304987231608694786650885 11119685105926630272497041)
                ·
                  refine ⟨8339763829444972704372781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11119685105926630272497041 8339763829444972704372781)
                  ·
                    refine ⟨3127411436041864764139793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8339763829444972704372781 3127411436041864764139793)
                    ·
                      refine ⟨2345558577031398573104845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3127411436041864764139793 2345558577031398573104845)
                      ·
                        rfl

theorem cell23_4567959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 1, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 1, 4, 2, 3, 2].length) (baseStart_4567959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4567959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4567959 prefixEnd_4567959 := by exact prefixLift 4567959
  have htrace : WordTrace (prefixWord ++ tailWord_4567959) baseStart_4567959 baseEnd_4567959 := by
    simpa [prefixWord, tailWord_4567959, baseEnd_4567959] using wordTrace_append hprefix tailTrace_4567959
  have hstable : (prefixWord ++ tailWord_4567959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4567959).length < 2 ^ (prefixWord ++ tailWord_4567959).sum := by decide
  have hdescent : baseEnd_4567959 < baseStart_4567959 := by decide
  rcases family_descends (prefixWord ++ tailWord_4567959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4567972 : List Nat := [2, 3, 1, 2, 1, 2, 1, 1, 5, 1, 4]
def baseStart_4567972 : Nat := 118140960795 + 4567972 * 2 ^ 59
def prefixEnd_4567972 : Nat := 4983230072969 + 3 ^ 40 * 4567972 * 2
def baseEnd_4567972 : Nat := 2345565252279907022242285

theorem tailTrace_4567972 : CollatzResearch.WordTrace tailWord_4567972 prefixEnd_4567972 2345565252279907022242285 := by
  unfold tailWord_4567972
  simp only [CollatzResearch.WordTrace]
  refine ⟨83303813103512533175997085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111071750804683377567996113 83303813103512533175997085)
  ·
    refine ⟨31238929913817199940998907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 83303813103512533175997085 31238929913817199940998907)
    ·
      refine ⟨46858394870725799911498361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31238929913817199940998907 46858394870725799911498361)
      ·
        refine ⟨35143796153044349933623771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46858394870725799911498361 35143796153044349933623771)
        ·
          refine ⟨52715694229566524900435657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35143796153044349933623771 52715694229566524900435657)
          ·
            refine ⟨39536770672174893675326743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52715694229566524900435657 39536770672174893675326743)
            ·
              refine ⟨59305156008262340512990115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39536770672174893675326743 59305156008262340512990115)
              ·
                refine ⟨88957734012393510769485173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 59305156008262340512990115 88957734012393510769485173)
                ·
                  refine ⟨8339787563661891634639235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 88957734012393510769485173 8339787563661891634639235)
                  ·
                    refine ⟨12509681345492837451958853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8339787563661891634639235 12509681345492837451958853)
                    ·
                      refine ⟨2345565252279907022242285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12509681345492837451958853 2345565252279907022242285)
                      ·
                        rfl

theorem cell23_4567972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 1, 1, 5, 1, 4].length) (baseStart_4567972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4567972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4567972 prefixEnd_4567972 := by exact prefixLift 4567972
  have htrace : WordTrace (prefixWord ++ tailWord_4567972) baseStart_4567972 baseEnd_4567972 := by
    simpa [prefixWord, tailWord_4567972, baseEnd_4567972] using wordTrace_append hprefix tailTrace_4567972
  have hstable : (prefixWord ++ tailWord_4567972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4567972).length < 2 ^ (prefixWord ++ tailWord_4567972).sum := by decide
  have hdescent : baseEnd_4567972 < baseStart_4567972 := by decide
  rcases family_descends (prefixWord ++ tailWord_4567972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4567989 : List Nat := [1, 3, 3, 2, 1, 1, 2, 4, 1, 1, 4]
def baseStart_4567989 : Nat := 118140960795 + 4567989 * 2 ^ 59
def prefixEnd_4567989 : Nat := 4983230072969 + 3 ^ 40 * 4567989 * 2
def baseEnd_4567989 : Nat := 2345573981451033455729707

theorem tailTrace_4567989 : CollatzResearch.WordTrace tailWord_4567989 prefixEnd_4567989 2345573981451033455729707 := by
  unfold tailWord_4567989
  simp only [CollatzResearch.WordTrace]
  refine ⟨166608246247963478255363021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111072164165308985503575347 166608246247963478255363021)
  ·
    refine ⟨62478092342986304345761133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 166608246247963478255363021 62478092342986304345761133)
    ·
      refine ⟨23429284628619864129660425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 62478092342986304345761133 23429284628619864129660425)
      ·
        refine ⟨17571963471464898097245319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23429284628619864129660425 17571963471464898097245319)
        ·
          refine ⟨26357945207197347145867979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17571963471464898097245319 26357945207197347145867979)
          ·
            refine ⟨39536917810796020718801969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26357945207197347145867979 39536917810796020718801969)
            ·
              refine ⟨29652688358097015539101477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39536917810796020718801969 29652688358097015539101477)
              ·
                refine ⟨5559879067143190413581527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 29652688358097015539101477 5559879067143190413581527)
                ·
                  refine ⟨8339818600714785620372291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5559879067143190413581527 8339818600714785620372291)
                  ·
                    refine ⟨12509727901072178430558437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8339818600714785620372291 12509727901072178430558437)
                    ·
                      refine ⟨2345573981451033455729707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12509727901072178430558437 2345573981451033455729707)
                      ·
                        rfl

theorem cell23_4567989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 2, 4, 1, 1, 4].length) (baseStart_4567989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4567989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4567989 prefixEnd_4567989 := by exact prefixLift 4567989
  have htrace : WordTrace (prefixWord ++ tailWord_4567989) baseStart_4567989 baseEnd_4567989 := by
    simpa [prefixWord, tailWord_4567989, baseEnd_4567989] using wordTrace_append hprefix tailTrace_4567989
  have hstable : (prefixWord ++ tailWord_4567989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4567989).length < 2 ^ (prefixWord ++ tailWord_4567989).sum := by decide
  have hdescent : baseEnd_4567989 < baseStart_4567989 := by decide
  rcases family_descends (prefixWord ++ tailWord_4567989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4568005 : List Nat := [1, 3, 1, 1, 1, 1, 1, 2, 1, 4, 7]
def baseStart_4568005 : Nat := 118140960795 + 4568005 * 2 ^ 59
def prefixEnd_4568005 : Nat := 4983230072969 + 3 ^ 40 * 4568005 * 2
def baseEnd_4568005 : Nat := 2345582197141505393129633

theorem tailTrace_4568005 : CollatzResearch.WordTrace tailWord_4568005 prefixEnd_4568005 2345582197141505393129633 := by
  unfold tailWord_4568005
  simp only [CollatzResearch.WordTrace]
  refine ⟨166608829815905512987945469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111072553210603675325296979 166608829815905512987945469)
  ·
    refine ⟨62478311180964567370479551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 166608829815905512987945469 62478311180964567370479551)
    ·
      refine ⟨93717466771446851055719327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62478311180964567370479551 93717466771446851055719327)
      ·
        refine ⟨140576200157170276583578991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93717466771446851055719327 140576200157170276583578991)
        ·
          refine ⟨210864300235755414875368487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 140576200157170276583578991 210864300235755414875368487)
          ·
            refine ⟨316296450353633122313052731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 210864300235755414875368487 316296450353633122313052731)
            ·
              refine ⟨474444675530449683469579097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 316296450353633122313052731 474444675530449683469579097)
              ·
                refine ⟨355833506647837262602184323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 474444675530449683469579097 355833506647837262602184323)
                ·
                  refine ⟨533750259971755893903276485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 355833506647837262602184323 533750259971755893903276485)
                  ·
                    refine ⟨100078173744704230106864341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 533750259971755893903276485 100078173744704230106864341)
                    ·
                      refine ⟨2345582197141505393129633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 100078173744704230106864341 2345582197141505393129633)
                      ·
                        rfl

theorem cell23_4568005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 2, 1, 4, 7].length) (baseStart_4568005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4568005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4568005 prefixEnd_4568005 := by exact prefixLift 4568005
  have htrace : WordTrace (prefixWord ++ tailWord_4568005) baseStart_4568005 baseEnd_4568005 := by
    simpa [prefixWord, tailWord_4568005, baseEnd_4568005] using wordTrace_append hprefix tailTrace_4568005
  have hstable : (prefixWord ++ tailWord_4568005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4568005).length < 2 ^ (prefixWord ++ tailWord_4568005).sum := by decide
  have hdescent : baseEnd_4568005 < baseStart_4568005 := by decide
  rcases family_descends (prefixWord ++ tailWord_4568005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4568046 : List Nat := [4, 1, 2, 1, 4, 2, 2, 7]
def baseStart_4568046 : Nat := 118140960795 + 4568046 * 2 ^ 59
def prefixEnd_4568046 : Nat := 4983230072969 + 3 ^ 40 * 4568046 * 2
def baseEnd_4568046 : Nat := 86874194438827397508035

theorem tailTrace_4568046 : CollatzResearch.WordTrace tailWord_4568046 prefixEnd_4568046 86874194438827397508035 := by
  unfold tailWord_4568046
  simp only [CollatzResearch.WordTrace]
  refine ⟨20826290651094622123773499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 111073550139171317993458661 20826290651094622123773499)
  ·
    refine ⟨31239435976641933185660249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20826290651094622123773499 31239435976641933185660249)
    ·
      refine ⟨23429576982481449889245187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31239435976641933185660249 23429576982481449889245187)
      ·
        refine ⟨35144365473722174833867781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23429576982481449889245187 35144365473722174833867781)
        ·
          refine ⟨6589568526322907781350209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 35144365473722174833867781 6589568526322907781350209)
          ·
            refine ⟨4942176394742180836012657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6589568526322907781350209 4942176394742180836012657)
            ·
              refine ⟨3706632296056635627009493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4942176394742180836012657 3706632296056635627009493)
              ·
                refine ⟨86874194438827397508035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3706632296056635627009493 86874194438827397508035)
                ·
                  rfl

theorem cell23_4568046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 2, 2, 7].length) (baseStart_4568046 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4568046 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4568046 prefixEnd_4568046 := by exact prefixLift 4568046
  have htrace : WordTrace (prefixWord ++ tailWord_4568046) baseStart_4568046 baseEnd_4568046 := by
    simpa [prefixWord, tailWord_4568046, baseEnd_4568046] using wordTrace_append hprefix tailTrace_4568046
  have hstable : (prefixWord ++ tailWord_4568046).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4568046).length < 2 ^ (prefixWord ++ tailWord_4568046).sum := by decide
  have hdescent : baseEnd_4568046 < baseStart_4568046 := by decide
  rcases family_descends (prefixWord ++ tailWord_4568046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4568100 : List Nat := [2, 3, 1, 4, 1, 3, 1, 2, 1, 3, 2]
def baseStart_4568100 : Nat := 118140960795 + 4568100 * 2 ^ 59
def prefixEnd_4568100 : Nat := 4983230072969 + 3 ^ 40 * 4568100 * 2
def baseEnd_4568100 : Nat := 2345630977803682521441697

theorem tailTrace_4568100 : CollatzResearch.WordTrace tailWord_4568100 prefixEnd_4568100 2345630977803682521441697 := by
  unfold tailWord_4568100
  simp only [CollatzResearch.WordTrace]
  refine ⟨83306147375280672106326877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111074863167040896141769169 83306147375280672106326877)
  ·
    refine ⟨31239805265730252039872579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 83306147375280672106326877 31239805265730252039872579)
    ·
      refine ⟨46859707898595378059808869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31239805265730252039872579 46859707898595378059808869)
      ·
        refine ⟨8786195230986633386214163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 46859707898595378059808869 8786195230986633386214163)
        ·
          refine ⟨13179292846479950079321245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8786195230986633386214163 13179292846479950079321245)
          ·
            refine ⟨4942234817429981279745467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13179292846479950079321245 4942234817429981279745467)
            ·
              refine ⟨7413352226144971919618201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4942234817429981279745467 7413352226144971919618201)
              ·
                refine ⟨5560014169608728939713651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7413352226144971919618201 5560014169608728939713651)
                ·
                  refine ⟨8340021254413093409570477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5560014169608728939713651 8340021254413093409570477)
                  ·
                    refine ⟨3127507970404910028588929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8340021254413093409570477 3127507970404910028588929)
                    ·
                      refine ⟨2345630977803682521441697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3127507970404910028588929 2345630977803682521441697)
                      ·
                        rfl

theorem cell23_4568100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 3, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 3, 1, 2, 1, 3, 2].length) (baseStart_4568100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4568100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4568100 prefixEnd_4568100 := by exact prefixLift 4568100
  have htrace : WordTrace (prefixWord ++ tailWord_4568100) baseStart_4568100 baseEnd_4568100 := by
    simpa [prefixWord, tailWord_4568100, baseEnd_4568100] using wordTrace_append hprefix tailTrace_4568100
  have hstable : (prefixWord ++ tailWord_4568100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4568100).length < 2 ^ (prefixWord ++ tailWord_4568100).sum := by decide
  have hdescent : baseEnd_4568100 < baseStart_4568100 := by decide
  rcases family_descends (prefixWord ++ tailWord_4568100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4568116 : List Nat := [2, 5, 1, 2, 1, 1, 2, 1, 2, 1, 5]
def baseStart_4568116 : Nat := 118140960795 + 4568116 * 2 ^ 59
def prefixEnd_4568116 : Nat := 4983230072969 + 3 ^ 40 * 4568116 * 2
def baseEnd_4568116 : Nat := 2345639193494154458841623

theorem tailTrace_4568116 : CollatzResearch.WordTrace tailWord_4568116 prefixEnd_4568116 2345639193494154458841623 := by
  unfold tailWord_4568116
  simp only [CollatzResearch.WordTrace]
  refine ⟨83306439159251689472618101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111075252212335585963490801 83306439159251689472618101)
  ·
    refine ⟨7809978671179845888057947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 83306439159251689472618101 7809978671179845888057947)
    ·
      refine ⟨11714968006769768832086921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7809978671179845888057947 11714968006769768832086921)
      ·
        refine ⟨8786226005077326624065191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11714968006769768832086921 8786226005077326624065191)
        ·
          refine ⟨13179339007615989936097787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8786226005077326624065191 13179339007615989936097787)
          ·
            refine ⟨19769008511423984904146681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13179339007615989936097787 19769008511423984904146681)
            ·
              refine ⟨14826756383567988678110011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19769008511423984904146681 14826756383567988678110011)
              ·
                refine ⟨22240134575351983017165017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14826756383567988678110011 22240134575351983017165017)
                ·
                  refine ⟨16680100931513987262873763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22240134575351983017165017 16680100931513987262873763)
                  ·
                    refine ⟨25020151397270980894310645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16680100931513987262873763 25020151397270980894310645)
                    ·
                      refine ⟨2345639193494154458841623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25020151397270980894310645 2345639193494154458841623)
                      ·
                        rfl

theorem cell23_4568116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 2, 1, 2, 1, 5].length) (baseStart_4568116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4568116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4568116 prefixEnd_4568116 := by exact prefixLift 4568116
  have htrace : WordTrace (prefixWord ++ tailWord_4568116) baseStart_4568116 baseEnd_4568116 := by
    simpa [prefixWord, tailWord_4568116, baseEnd_4568116] using wordTrace_append hprefix tailTrace_4568116
  have hstable : (prefixWord ++ tailWord_4568116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4568116).length < 2 ^ (prefixWord ++ tailWord_4568116).sum := by decide
  have hdescent : baseEnd_4568116 < baseStart_4568116 := by decide
  rcases family_descends (prefixWord ++ tailWord_4568116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4568119 : List Nat := [1, 1, 3, 1, 2, 2, 1, 7, 5]
def baseStart_4568119 : Nat := 118140960795 + 4568119 * 2 ^ 59
def prefixEnd_4568119 : Nat := 4983230072969 + 3 ^ 40 * 4568119 * 2
def baseEnd_4568119 : Nat := 260626748215124216344901

theorem tailTrace_4568119 : CollatzResearch.WordTrace tailWord_4568119 prefixEnd_4568119 260626748215124216344901 := by
  unfold tailWord_4568119
  simp only [CollatzResearch.WordTrace]
  refine ⟨166612987737492510457595411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111075325158328340305063607 166612987737492510457595411)
  ·
    refine ⟨249919481606238765686393117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 166612987737492510457595411 249919481606238765686393117)
    ·
      refine ⟨93719805602339537132397419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 249919481606238765686393117 93719805602339537132397419)
      ·
        refine ⟨140579708403509305698596129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93719805602339537132397419 140579708403509305698596129)
        ·
          refine ⟨105434781302631979273947097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 140579708403509305698596129 105434781302631979273947097)
          ·
            refine ⟨79076085976973984455460323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 105434781302631979273947097 79076085976973984455460323)
            ·
              refine ⟨118614128965460976683190485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 79076085976973984455460323 118614128965460976683190485)
              ·
                refine ⟨2780018647627991641012277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 118614128965460976683190485 2780018647627991641012277)
                ·
                  refine ⟨260626748215124216344901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2780018647627991641012277 260626748215124216344901)
                  ·
                    rfl

theorem cell23_4568119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 7, 5].length) (baseStart_4568119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4568119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4568119 prefixEnd_4568119 := by exact prefixLift 4568119
  have htrace : WordTrace (prefixWord ++ tailWord_4568119) baseStart_4568119 baseEnd_4568119 := by
    simpa [prefixWord, tailWord_4568119, baseEnd_4568119] using wordTrace_append hprefix tailTrace_4568119
  have hstable : (prefixWord ++ tailWord_4568119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4568119).length < 2 ^ (prefixWord ++ tailWord_4568119).sum := by decide
  have hdescent : baseEnd_4568119 < baseStart_4568119 := by decide
  rcases family_descends (prefixWord ++ tailWord_4568119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4568146 : List Nat := [3, 2, 2, 1, 3, 2, 1, 1, 2, 3, 3]
def baseStart_4568146 : Nat := 118140960795 + 4568146 * 2 ^ 59
def prefixEnd_4568146 : Nat := 4983230072969 + 3 ^ 40 * 4568146 * 2
def baseEnd_4568146 : Nat := 2345654597913789341466485

theorem tailTrace_4568146 : CollatzResearch.WordTrace tailWord_4568146 prefixEnd_4568146 2345654597913789341466485 := by
  unfold tailWord_4568146
  simp only [CollatzResearch.WordTrace]
  refine ⟨41653493127098673517207073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 111075981672263129379218861 41653493127098673517207073)
  ·
    refine ⟨31240119845324005137905305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41653493127098673517207073 31240119845324005137905305)
    ·
      refine ⟨23430089883993003853428979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31240119845324005137905305 23430089883993003853428979)
      ·
        refine ⟨35145134825989505780143469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23430089883993003853428979 35145134825989505780143469)
        ·
          refine ⟨13179425559746064667553801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35145134825989505780143469 13179425559746064667553801)
          ·
            refine ⟨9884569169809548500665351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13179425559746064667553801 9884569169809548500665351)
            ·
              refine ⟨14826853754714322750998027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9884569169809548500665351 14826853754714322750998027)
              ·
                refine ⟨22240280632071484126497041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14826853754714322750998027 22240280632071484126497041)
                ·
                  refine ⟨16680210474053613094872781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22240280632071484126497041 16680210474053613094872781)
                  ·
                    refine ⟨6255078927770104910577293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16680210474053613094872781 6255078927770104910577293)
                    ·
                      refine ⟨2345654597913789341466485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6255078927770104910577293 2345654597913789341466485)
                      ·
                        rfl

theorem cell23_4568146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 2, 1, 1, 2, 3, 3].length) (baseStart_4568146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4568146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4568146 prefixEnd_4568146 := by exact prefixLift 4568146
  have htrace : WordTrace (prefixWord ++ tailWord_4568146) baseStart_4568146 baseEnd_4568146 := by
    simpa [prefixWord, tailWord_4568146, baseEnd_4568146] using wordTrace_append hprefix tailTrace_4568146
  have hstable : (prefixWord ++ tailWord_4568146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4568146).length < 2 ^ (prefixWord ++ tailWord_4568146).sum := by decide
  have hdescent : baseEnd_4568146 < baseStart_4568146 := by decide
  rcases family_descends (prefixWord ++ tailWord_4568146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4568156 : List Nat := [2, 2, 4, 1, 1, 1, 1, 2, 2, 5, 2]
def baseStart_4568156 : Nat := 118140960795 + 4568156 * 2 ^ 59
def prefixEnd_4568156 : Nat := 4983230072969 + 3 ^ 40 * 4568156 * 2
def baseEnd_4568156 : Nat := 2345659732720334302341439

theorem tailTrace_4568156 : CollatzResearch.WordTrace tailWord_4568156 prefixEnd_4568156 2345659732720334302341439 := by
  unfold tailWord_4568156
  simp only [CollatzResearch.WordTrace]
  refine ⟨83307168619179232888346161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111076224825572310517794881 83307168619179232888346161)
  ·
    refine ⟨62480376464384424666259621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83307168619179232888346161 62480376464384424666259621)
    ·
      refine ⟨11715070587072079624923679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 62480376464384424666259621 11715070587072079624923679)
      ·
        refine ⟨17572605880608119437385519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11715070587072079624923679 17572605880608119437385519)
        ·
          refine ⟨26358908820912179156078279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17572605880608119437385519 26358908820912179156078279)
          ·
            refine ⟨39538363231368268734117419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26358908820912179156078279 39538363231368268734117419)
            ·
              refine ⟨59307544847052403101176129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39538363231368268734117419 59307544847052403101176129)
              ·
                refine ⟨44480658635289302325882097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 59307544847052403101176129 44480658635289302325882097)
                ·
                  refine ⟨33360493976466976744411573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 44480658635289302325882097 33360493976466976744411573)
                  ·
                    refine ⟨3127546310293779069788585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 33360493976466976744411573 3127546310293779069788585)
                    ·
                      refine ⟨2345659732720334302341439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3127546310293779069788585 2345659732720334302341439)
                      ·
                        rfl

theorem cell23_4568156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 1, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 1, 2, 2, 5, 2].length) (baseStart_4568156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4568156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4568156 prefixEnd_4568156 := by exact prefixLift 4568156
  have htrace : WordTrace (prefixWord ++ tailWord_4568156) baseStart_4568156 baseEnd_4568156 := by
    simpa [prefixWord, tailWord_4568156, baseEnd_4568156] using wordTrace_append hprefix tailTrace_4568156
  have hstable : (prefixWord ++ tailWord_4568156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4568156).length < 2 ^ (prefixWord ++ tailWord_4568156).sum := by decide
  have hdescent : baseEnd_4568156 < baseStart_4568156 := by decide
  rcases family_descends (prefixWord ++ tailWord_4568156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4568169 : List Nat := [1, 2, 1, 1, 1, 7, 1, 1, 1, 3, 4]
def baseStart_4568169 : Nat := 118140960795 + 4568169 * 2 ^ 59
def prefixEnd_4568169 : Nat := 4983230072969 + 3 ^ 40 * 4568169 * 2
def baseEnd_4568169 : Nat := 2345666407968842751478879

theorem tailTrace_4568169 : CollatzResearch.WordTrace tailWord_4568169 prefixEnd_4568169 2345666407968842751478879 := by
  unfold tailWord_4568169
  simp only [CollatzResearch.WordTrace]
  refine ⟨166614811387311368996915561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111076540924874245997943707 166614811387311368996915561)
  ·
    refine ⟨124961108540483526747686671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 166614811387311368996915561 124961108540483526747686671)
    ·
      refine ⟨187441662810725290121530007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 124961108540483526747686671 187441662810725290121530007)
      ·
        refine ⟨281162494216087935182295011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 187441662810725290121530007 281162494216087935182295011)
        ·
          refine ⟨421743741324131902773442517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 281162494216087935182295011 421743741324131902773442517)
          ·
            refine ⟨9884618937284341471252559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 421743741324131902773442517 9884618937284341471252559)
            ·
              refine ⟨14826928405926512206878839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9884618937284341471252559 14826928405926512206878839)
              ·
                refine ⟨22240392608889768310318259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14826928405926512206878839 22240392608889768310318259)
                ·
                  refine ⟨33360588913334652465477389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22240392608889768310318259 33360588913334652465477389)
                  ·
                    refine ⟨12510220842500494674554021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 33360588913334652465477389 12510220842500494674554021)
                    ·
                      refine ⟨2345666407968842751478879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12510220842500494674554021 2345666407968842751478879)
                      ·
                        rfl

theorem cell23_4568169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 7, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 7, 1, 1, 1, 3, 4].length) (baseStart_4568169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4568169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4568169 prefixEnd_4568169 := by exact prefixLift 4568169
  have htrace : WordTrace (prefixWord ++ tailWord_4568169) baseStart_4568169 baseEnd_4568169 := by
    simpa [prefixWord, tailWord_4568169, baseEnd_4568169] using wordTrace_append hprefix tailTrace_4568169
  have hstable : (prefixWord ++ tailWord_4568169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4568169).length < 2 ^ (prefixWord ++ tailWord_4568169).sum := by decide
  have hdescent : baseEnd_4568169 < baseStart_4568169 := by decide
  rcases family_descends (prefixWord ++ tailWord_4568169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4568196 : List Nat := [2, 3, 2, 1, 2, 2, 1, 3, 3, 4]
def baseStart_4568196 : Nat := 118140960795 + 4568196 * 2 ^ 59
def prefixEnd_4568196 : Nat := 4983230072969 + 3 ^ 40 * 4568196 * 2
def baseEnd_4568196 : Nat := 781893423982171381947085

theorem tailTrace_4568196 : CollatzResearch.WordTrace tailWord_4568196 prefixEnd_4568196 781893423982171381947085 := by
  unfold tailWord_4568196
  simp only [CollatzResearch.WordTrace]
  refine ⟨83307898079106776304074221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111077197438809035072098961 83307898079106776304074221)
  ·
    refine ⟨31240461779665041114027833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 83307898079106776304074221 31240461779665041114027833)
    ·
      refine ⟨23430346334748780835520875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31240461779665041114027833 23430346334748780835520875)
      ·
        refine ⟨35145519502123171253281313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23430346334748780835520875 35145519502123171253281313)
        ·
          refine ⟨26359139626592378439960985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35145519502123171253281313 26359139626592378439960985)
          ·
            refine ⟨19769354719944283829970739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26359139626592378439960985 19769354719944283829970739)
            ·
              refine ⟨29654032079916425744956109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19769354719944283829970739 29654032079916425744956109)
              ·
                refine ⟨11120262029968659654358541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29654032079916425744956109 11120262029968659654358541)
                ·
                  refine ⟨4170098261238247370384453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11120262029968659654358541 4170098261238247370384453)
                  ·
                    refine ⟨781893423982171381947085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4170098261238247370384453 781893423982171381947085)
                    ·
                      rfl

theorem cell23_4568196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 1, 3, 3, 4].length) (baseStart_4568196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4568196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4568196 prefixEnd_4568196 := by exact prefixLift 4568196
  have htrace : WordTrace (prefixWord ++ tailWord_4568196) baseStart_4568196 baseEnd_4568196 := by
    simpa [prefixWord, tailWord_4568196, baseEnd_4568196] using wordTrace_append hprefix tailTrace_4568196
  have hstable : (prefixWord ++ tailWord_4568196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4568196).length < 2 ^ (prefixWord ++ tailWord_4568196).sum := by decide
  have hdescent : baseEnd_4568196 < baseStart_4568196 := by decide
  rcases family_descends (prefixWord ++ tailWord_4568196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4568206 : List Nat := [4, 1, 1, 3, 2, 1, 1, 2, 1, 4, 3]
def baseStart_4568206 : Nat := 118140960795 + 4568206 * 2 ^ 59
def prefixEnd_4568206 : Nat := 4983230072969 + 3 ^ 40 * 4568206 * 2
def baseEnd_4568206 : Nat := 2345685406753059106716209

theorem tailTrace_4568206 : CollatzResearch.WordTrace tailWord_4568206 prefixEnd_4568206 2345685406753059106716209 := by
  unfold tailWord_4568206
  simp only [CollatzResearch.WordTrace]
  refine ⟨20827020111022165539501559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 111077440592118216210674981 20827020111022165539501559)
  ·
    refine ⟨31240530166533248309252339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20827020111022165539501559 31240530166533248309252339)
    ·
      refine ⟨46860795249799872463878509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31240530166533248309252339 46860795249799872463878509)
      ·
        refine ⟨17572798218674952173954441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46860795249799872463878509 17572798218674952173954441)
        ·
          refine ⟨13179598664006214130465831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17572798218674952173954441 13179598664006214130465831)
          ·
            refine ⟨19769397996009321195698747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13179598664006214130465831 19769397996009321195698747)
            ·
              refine ⟨29654096994013981793548121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19769397996009321195698747 29654096994013981793548121)
              ·
                refine ⟨22240572745510486345161091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29654096994013981793548121 22240572745510486345161091)
                ·
                  refine ⟨33360859118265729517741637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22240572745510486345161091 33360859118265729517741637)
                  ·
                    refine ⟨6255161084674824284576557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 33360859118265729517741637 6255161084674824284576557)
                    ·
                      refine ⟨2345685406753059106716209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6255161084674824284576557 2345685406753059106716209)
                      ·
                        rfl

theorem cell23_4568206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 1, 2, 1, 4, 3].length) (baseStart_4568206 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4568206 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4568206 prefixEnd_4568206 := by exact prefixLift 4568206
  have htrace : WordTrace (prefixWord ++ tailWord_4568206) baseStart_4568206 baseEnd_4568206 := by
    simpa [prefixWord, tailWord_4568206, baseEnd_4568206] using wordTrace_append hprefix tailTrace_4568206
  have hstable : (prefixWord ++ tailWord_4568206).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4568206).length < 2 ^ (prefixWord ++ tailWord_4568206).sum := by decide
  have hdescent : baseEnd_4568206 < baseStart_4568206 := by decide
  rcases family_descends (prefixWord ++ tailWord_4568206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4568253 : List Nat := [1, 4, 1, 2, 1, 1, 5, 1, 3, 1, 3]
def baseStart_4568253 : Nat := 118140960795 + 4568253 * 2 ^ 59
def prefixEnd_4568253 : Nat := 4983230072969 + 3 ^ 40 * 4568253 * 2
def baseEnd_4568253 : Nat := 2345709540343820422828493

theorem tailTrace_4568253 : CollatzResearch.WordTrace tailWord_4568253 prefixEnd_4568253 2345709540343820422828493 := by
  unfold tailWord_4568253
  simp only [CollatzResearch.WordTrace]
  refine ⟨166617875119007051342973413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111078583412671367561982275 166617875119007051342973413)
  ·
    refine ⟨31240851584813822126807515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 166617875119007051342973413 31240851584813822126807515)
    ·
      refine ⟨46861277377220733190211273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31240851584813822126807515 46861277377220733190211273)
      ·
        refine ⟨35145958032915549892658455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46861277377220733190211273 35145958032915549892658455)
        ·
          refine ⟨52718937049373324838987683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35145958032915549892658455 52718937049373324838987683)
          ·
            refine ⟨79078405574059987258481525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52718937049373324838987683 79078405574059987258481525)
            ·
              refine ⟨7413600522568123805482643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 79078405574059987258481525 7413600522568123805482643)
              ·
                refine ⟨11120400783852185708223965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7413600522568123805482643 11120400783852185708223965)
                ·
                  refine ⟨4170150293944569640583987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11120400783852185708223965 4170150293944569640583987)
                  ·
                    refine ⟨6255225440916854460875981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4170150293944569640583987 6255225440916854460875981)
                    ·
                      refine ⟨2345709540343820422828493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6255225440916854460875981 2345709540343820422828493)
                      ·
                        rfl

theorem cell23_4568253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 5, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 5, 1, 3, 1, 3].length) (baseStart_4568253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4568253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4568253 prefixEnd_4568253 := by exact prefixLift 4568253
  have htrace : WordTrace (prefixWord ++ tailWord_4568253) baseStart_4568253 baseEnd_4568253 := by
    simpa [prefixWord, tailWord_4568253, baseEnd_4568253] using wordTrace_append hprefix tailTrace_4568253
  have hstable : (prefixWord ++ tailWord_4568253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4568253).length < 2 ^ (prefixWord ++ tailWord_4568253).sum := by decide
  have hdescent : baseEnd_4568253 < baseStart_4568253 := by decide
  rcases family_descends (prefixWord ++ tailWord_4568253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4568260 : List Nat := [2, 3, 3, 1, 3, 2, 2, 1, 6]
def baseStart_4568260 : Nat := 118140960795 + 4568260 * 2 ^ 59
def prefixEnd_4568260 : Nat := 4983230072969 + 3 ^ 40 * 4568260 * 2
def baseEnd_4568260 : Nat := 260634792745377988382329

theorem tailTrace_4568260 : CollatzResearch.WordTrace tailWord_4568260 prefixEnd_4568260 260634792745377988382329 := by
  unfold tailWord_4568260
  simp only [CollatzResearch.WordTrace]
  refine ⟨83309065214990845769239117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111078753619987794358985489 83309065214990845769239117)
  ·
    refine ⟨31240899455621567163464669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 83309065214990845769239117 31240899455621567163464669)
    ·
      refine ⟨11715337295858087686299251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31240899455621567163464669 11715337295858087686299251)
      ·
        refine ⟨17573005943787131529448877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11715337295858087686299251 17573005943787131529448877)
        ·
          refine ⟨6589877228920174323543329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17573005943787131529448877 6589877228920174323543329)
          ·
            refine ⟨4942407921690130742657497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6589877228920174323543329 4942407921690130742657497)
            ·
              refine ⟨3706805941267598056993123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4942407921690130742657497 3706805941267598056993123)
              ·
                refine ⟨5560208911901397085489685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3706805941267598056993123 5560208911901397085489685)
                ·
                  refine ⟨260634792745377988382329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5560208911901397085489685 260634792745377988382329)
                  ·
                    rfl

theorem cell23_4568260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 2, 2, 1, 6].length) (baseStart_4568260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4568260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4568260 prefixEnd_4568260 := by exact prefixLift 4568260
  have htrace : WordTrace (prefixWord ++ tailWord_4568260) baseStart_4568260 baseEnd_4568260 := by
    simpa [prefixWord, tailWord_4568260, baseEnd_4568260] using wordTrace_append hprefix tailTrace_4568260
  have hstable : (prefixWord ++ tailWord_4568260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4568260).length < 2 ^ (prefixWord ++ tailWord_4568260).sum := by decide
  have hdescent : baseEnd_4568260 < baseStart_4568260 := by decide
  rcases family_descends (prefixWord ++ tailWord_4568260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4568279 : List Nat := [1, 1, 3, 2, 1, 2, 2, 2, 3, 1, 5]
def baseStart_4568279 : Nat := 118140960795 + 4568279 * 2 ^ 59
def prefixEnd_4568279 : Nat := 4983230072969 + 3 ^ 40 * 4568279 * 2
def baseEnd_4568279 : Nat := 2345722890840837321103373

theorem tailTrace_4568279 : CollatzResearch.WordTrace tailWord_4568279 prefixEnd_4568279 2345722890840837321103373 := by
  unfold tailWord_4568279
  simp only [CollatzResearch.WordTrace]
  refine ⟨166618823416912857783419891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111079215611275238522279927 166618823416912857783419891)
  ·
    refine ⟨249928235125369286675129837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 166618823416912857783419891 249928235125369286675129837)
    ·
      refine ⟨93723088172013482503173689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 249928235125369286675129837 93723088172013482503173689)
      ·
        refine ⟨70292316129010111877380267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 93723088172013482503173689 70292316129010111877380267)
        ·
          refine ⟨105438474193515167816070401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70292316129010111877380267 105438474193515167816070401)
          ·
            refine ⟨79078855645136375862052801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 105438474193515167816070401 79078855645136375862052801)
            ·
              refine ⟨59309141733852281896539601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 79078855645136375862052801 59309141733852281896539601)
              ·
                refine ⟨44481856300389211422404701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 59309141733852281896539601 44481856300389211422404701)
                ·
                  refine ⟨16680696112645954283401763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 44481856300389211422404701 16680696112645954283401763)
                  ·
                    refine ⟨25021044168968931425102645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16680696112645954283401763 25021044168968931425102645)
                    ·
                      refine ⟨2345722890840837321103373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25021044168968931425102645 2345722890840837321103373)
                      ·
                        rfl

theorem cell23_4568279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 2, 2, 3, 1, 5].length) (baseStart_4568279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4568279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4568279 prefixEnd_4568279 := by exact prefixLift 4568279
  have htrace : WordTrace (prefixWord ++ tailWord_4568279) baseStart_4568279 baseEnd_4568279 := by
    simpa [prefixWord, tailWord_4568279, baseEnd_4568279] using wordTrace_append hprefix tailTrace_4568279
  have hstable : (prefixWord ++ tailWord_4568279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4568279).length < 2 ^ (prefixWord ++ tailWord_4568279).sum := by decide
  have hdescent : baseEnd_4568279 < baseStart_4568279 := by decide
  rcases family_descends (prefixWord ++ tailWord_4568279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4568280 : List Nat := [2, 1, 2, 2, 5, 1, 2, 1, 2, 3, 2]
def baseStart_4568280 : Nat := 118140960795 + 4568280 * 2 ^ 59
def prefixEnd_4568280 : Nat := 4983230072969 + 3 ^ 40 * 4568280 * 2
def baseEnd_4568280 : Nat := 2345723404321491817190869

theorem tailTrace_4568280 : CollatzResearch.WordTrace tailWord_4568280 prefixEnd_4568280 2345723404321491817190869 := by
  unfold tailWord_4568280
  simp only [CollatzResearch.WordTrace]
  refine ⟨83309429944954617477103147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111079239926606156636137529 83309429944954617477103147)
  ·
    refine ⟨124964144917431926215654721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83309429944954617477103147 124964144917431926215654721)
    ·
      refine ⟨93723108688073944661741041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 124964144917431926215654721 93723108688073944661741041)
      ·
        refine ⟨70292331516055458496305781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 93723108688073944661741041 70292331516055458496305781)
        ·
          refine ⟨6589906079630199234028667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 70292331516055458496305781 6589906079630199234028667)
          ·
            refine ⟨9884859119445298851043001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6589906079630199234028667 9884859119445298851043001)
            ·
              refine ⟨7413644339583974138282251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9884859119445298851043001 7413644339583974138282251)
              ·
                refine ⟨11120466509375961207423377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7413644339583974138282251 11120466509375961207423377)
                ·
                  refine ⟨8340349882031970905567533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11120466509375961207423377 8340349882031970905567533)
                  ·
                    refine ⟨3127631205761989089587825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8340349882031970905567533 3127631205761989089587825)
                    ·
                      refine ⟨2345723404321491817190869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3127631205761989089587825 2345723404321491817190869)
                      ·
                        rfl

theorem cell23_4568280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 1, 2, 1, 2, 3, 2].length) (baseStart_4568280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4568280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4568280 prefixEnd_4568280 := by exact prefixLift 4568280
  have htrace : WordTrace (prefixWord ++ tailWord_4568280) baseStart_4568280 baseEnd_4568280 := by
    simpa [prefixWord, tailWord_4568280, baseEnd_4568280] using wordTrace_append hprefix tailTrace_4568280
  have hstable : (prefixWord ++ tailWord_4568280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4568280).length < 2 ^ (prefixWord ++ tailWord_4568280).sum := by decide
  have hdescent : baseEnd_4568280 < baseStart_4568280 := by decide
  rcases family_descends (prefixWord ++ tailWord_4568280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4568310 : List Nat := [5, 1, 1, 1, 1, 1, 1, 5, 3, 2, 2]
def baseStart_4568310 : Nat := 118140960795 + 4568310 * 2 ^ 59
def prefixEnd_4568310 : Nat := 4983230072969 + 3 ^ 40 * 4568310 * 2
def baseEnd_4568310 : Nat := 2345738808741126699815731

theorem tailTrace_4568310 : CollatzResearch.WordTrace tailWord_4568310 prefixEnd_4568310 2345738808741126699815731 := by
  unfold tailWord_4568310
  simp only [CollatzResearch.WordTrace]
  refine ⟨10413747129987534379862399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 111079969386533700051865589 10413747129987534379862399)
  ·
    refine ⟨15620620694981301569793599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10413747129987534379862399 15620620694981301569793599)
    ·
      refine ⟨23430931042471952354690399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15620620694981301569793599 23430931042471952354690399)
      ·
        refine ⟨35146396563707928532035599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23430931042471952354690399 35146396563707928532035599)
        ·
          refine ⟨52719594845561892798053399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35146396563707928532035599 52719594845561892798053399)
          ·
            refine ⟨79079392268342839197080099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52719594845561892798053399 79079392268342839197080099)
            ·
              refine ⟨118619088402514258795620149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 79079392268342839197080099 118619088402514258795620149)
              ·
                refine ⟨11120539537735711762089389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 118619088402514258795620149 11120539537735711762089389)
                ·
                  refine ⟨4170202326650891910783521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11120539537735711762089389 4170202326650891910783521)
                  ·
                    refine ⟨3127651744988168933087641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4170202326650891910783521 3127651744988168933087641)
                    ·
                      refine ⟨2345738808741126699815731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3127651744988168933087641 2345738808741126699815731)
                      ·
                        rfl

theorem cell23_4568310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 5, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 5, 3, 2, 2].length) (baseStart_4568310 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4568310 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4568310 prefixEnd_4568310 := by exact prefixLift 4568310
  have htrace : WordTrace (prefixWord ++ tailWord_4568310) baseStart_4568310 baseEnd_4568310 := by
    simpa [prefixWord, tailWord_4568310, baseEnd_4568310] using wordTrace_append hprefix tailTrace_4568310
  have hstable : (prefixWord ++ tailWord_4568310).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4568310).length < 2 ^ (prefixWord ++ tailWord_4568310).sum := by decide
  have hdescent : baseEnd_4568310 < baseStart_4568310 := by decide
  rcases family_descends (prefixWord ++ tailWord_4568310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4568329 : List Nat := [1, 2, 1, 1, 3, 3, 1, 2, 2, 7]
def baseStart_4568329 : Nat := 118140960795 + 4568329 * 2 ^ 59
def prefixEnd_4568329 : Nat := 4983230072969 + 3 ^ 40 * 4568329 * 2
def baseEnd_4568329 : Nat := 781916188291187375159381

theorem tailTrace_4568329 : CollatzResearch.WordTrace tailWord_4568329 prefixEnd_4568329 781916188291187375159381 := by
  unfold tailWord_4568329
  simp only [CollatzResearch.WordTrace]
  refine ⟨166620647066731716322740041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111080431377821144215160027 166620647066731716322740041)
  ·
    refine ⟨124965485300048787242055031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 166620647066731716322740041 124965485300048787242055031)
    ·
      refine ⟨187448227950073180863082547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 124965485300048787242055031 187448227950073180863082547)
      ·
        refine ⟨281172341925109771294623821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 187448227950073180863082547 281172341925109771294623821)
        ·
          refine ⟨105439628221916164235483933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 281172341925109771294623821 105439628221916164235483933)
          ·
            refine ⟨39539860583218561588306475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 105439628221916164235483933 39539860583218561588306475)
            ·
              refine ⟨59309790874827842382459713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39539860583218561588306475 59309790874827842382459713)
              ·
                refine ⟨44482343156120881786844785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 59309790874827842382459713 44482343156120881786844785)
                ·
                  refine ⟨33361757367090661340133589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 44482343156120881786844785 33361757367090661340133589)
                  ·
                    refine ⟨781916188291187375159381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 33361757367090661340133589 781916188291187375159381)
                    ·
                      rfl

theorem cell23_4568329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 1, 2, 2, 7].length) (baseStart_4568329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4568329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4568329 prefixEnd_4568329 := by exact prefixLift 4568329
  have htrace : WordTrace (prefixWord ++ tailWord_4568329) baseStart_4568329 baseEnd_4568329 := by
    simpa [prefixWord, tailWord_4568329, baseEnd_4568329] using wordTrace_append hprefix tailTrace_4568329
  have hstable : (prefixWord ++ tailWord_4568329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4568329).length < 2 ^ (prefixWord ++ tailWord_4568329).sum := by decide
  have hdescent : baseEnd_4568329 < baseStart_4568329 := by decide
  rcases family_descends (prefixWord ++ tailWord_4568329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4568343 : List Nat := [1, 1, 3, 4, 1, 1, 2, 2, 4, 1, 3]
def baseStart_4568343 : Nat := 118140960795 + 4568343 * 2 ^ 59
def prefixEnd_4568343 : Nat := 4983230072969 + 3 ^ 40 * 4568343 * 2
def baseEnd_4568343 : Nat := 2345755753602725070703079

theorem tailTrace_4568343 : CollatzResearch.WordTrace tailWord_4568343 prefixEnd_4568343 2345755753602725070703079 := by
  unfold tailWord_4568343
  simp only [CollatzResearch.WordTrace]
  refine ⟨166621157688680996713749683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111080771792453997809166455 166621157688680996713749683)
  ·
    refine ⟨249931736533021495070624525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 166621157688680996713749683 249931736533021495070624525)
    ·
      refine ⟨93724401199883060651484197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 249931736533021495070624525 93724401199883060651484197)
      ·
        refine ⟨17573325224978073872153287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 93724401199883060651484197 17573325224978073872153287)
        ·
          refine ⟨26359987837467110808229931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17573325224978073872153287 26359987837467110808229931)
          ·
            refine ⟨39539981756200666212344897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26359987837467110808229931 39539981756200666212344897)
            ·
              refine ⟨29654986317150499659258673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39539981756200666212344897 29654986317150499659258673)
              ·
                refine ⟨22241239737862874744444005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29654986317150499659258673 22241239737862874744444005)
                ·
                  refine ⟨4170232450849289014583251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22241239737862874744444005 4170232450849289014583251)
                  ·
                    refine ⟨6255348676273933521874877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4170232450849289014583251 6255348676273933521874877)
                    ·
                      refine ⟨2345755753602725070703079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6255348676273933521874877 2345755753602725070703079)
                      ·
                        rfl

theorem cell23_4568343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 2, 2, 4, 1, 3].length) (baseStart_4568343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4568343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4568343 prefixEnd_4568343 := by exact prefixLift 4568343
  have htrace : WordTrace (prefixWord ++ tailWord_4568343) baseStart_4568343 baseEnd_4568343 := by
    simpa [prefixWord, tailWord_4568343, baseEnd_4568343] using wordTrace_append hprefix tailTrace_4568343
  have hstable : (prefixWord ++ tailWord_4568343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4568343).length < 2 ^ (prefixWord ++ tailWord_4568343).sum := by decide
  have hdescent : baseEnd_4568343 < baseStart_4568343 := by decide
  rcases family_descends (prefixWord ++ tailWord_4568343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4568360 : List Nat := [2, 1, 5, 1, 2, 2, 1, 1, 4, 1, 3]
def baseStart_4568360 : Nat := 118140960795 + 4568360 * 2 ^ 59
def prefixEnd_4568360 : Nat := 4983230072969 + 3 ^ 40 * 4568360 * 2
def baseEnd_4568360 : Nat := 2345764482773851504190501

theorem tailTrace_4568360 : CollatzResearch.WordTrace tailWord_4568360 prefixEnd_4568360 2345764482773851504190501 := by
  unfold tailWord_4568360
  simp only [CollatzResearch.WordTrace]
  refine ⟨83310888864809704308559267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111081185153079605744745689 83310888864809704308559267)
  ·
    refine ⟨124966333297214556462838901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83310888864809704308559267 124966333297214556462838901)
    ·
      refine ⟨11715593746613864668391147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 124966333297214556462838901 11715593746613864668391147)
      ·
        refine ⟨17573390619920797002586721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11715593746613864668391147 17573390619920797002586721)
        ·
          refine ⟨13180042964940597751940041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17573390619920797002586721 13180042964940597751940041)
          ·
            refine ⟨9885032223705448313955031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13180042964940597751940041 9885032223705448313955031)
            ·
              refine ⟨14827548335558172470932547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9885032223705448313955031 14827548335558172470932547)
              ·
                refine ⟨22241322503337258706398821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14827548335558172470932547 22241322503337258706398821)
                ·
                  refine ⟨4170247969375736007449779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22241322503337258706398821 4170247969375736007449779)
                  ·
                    refine ⟨6255371954063604011174669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4170247969375736007449779 6255371954063604011174669)
                    ·
                      refine ⟨2345764482773851504190501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6255371954063604011174669 2345764482773851504190501)
                      ·
                        rfl

theorem cell23_4568360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 2, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 2, 1, 1, 4, 1, 3].length) (baseStart_4568360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4568360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4568360 prefixEnd_4568360 := by exact prefixLift 4568360
  have htrace : WordTrace (prefixWord ++ tailWord_4568360) baseStart_4568360 baseEnd_4568360 := by
    simpa [prefixWord, tailWord_4568360, baseEnd_4568360] using wordTrace_append hprefix tailTrace_4568360
  have hstable : (prefixWord ++ tailWord_4568360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4568360).length < 2 ^ (prefixWord ++ tailWord_4568360).sum := by decide
  have hdescent : baseEnd_4568360 < baseStart_4568360 := by decide
  rcases family_descends (prefixWord ++ tailWord_4568360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4568374 : List Nat := [5, 1, 2, 3, 2, 1, 1, 1, 1, 2, 4]
def baseStart_4568374 : Nat := 118140960795 + 4568374 * 2 ^ 59
def prefixEnd_4568374 : Nat := 4983230072969 + 3 ^ 40 * 4568374 * 2
def baseEnd_4568374 : Nat := 2345771671503014449415437

theorem tailTrace_4568374 : CollatzResearch.WordTrace tailWord_4568374 prefixEnd_4568374 2345771671503014449415437 := by
  unfold tailWord_4568374
  simp only [CollatzResearch.WordTrace]
  refine ⟨10413893021973043063008011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 111081525567712459338752117 10413893021973043063008011)
  ·
    refine ⟨15620839532959564594512017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10413893021973043063008011 15620839532959564594512017)
    ·
      refine ⟨11715629649719673445884013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15620839532959564594512017 11715629649719673445884013)
      ·
        refine ⟨4393361118644877542206505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11715629649719673445884013 4393361118644877542206505)
        ·
          refine ⟨3295020838983658156654879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4393361118644877542206505 3295020838983658156654879)
          ·
            refine ⟨4942531258475487234982319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3295020838983658156654879 4942531258475487234982319)
            ·
              refine ⟨7413796887713230852473479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4942531258475487234982319 7413796887713230852473479)
              ·
                refine ⟨11120695331569846278710219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7413796887713230852473479 11120695331569846278710219)
                ·
                  refine ⟨16681042997354769418065329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11120695331569846278710219 16681042997354769418065329)
                  ·
                    refine ⟨12510782248016077063548997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16681042997354769418065329 12510782248016077063548997)
                    ·
                      refine ⟨2345771671503014449415437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12510782248016077063548997 2345771671503014449415437)
                      ·
                        rfl

theorem cell23_4568374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 2, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 2, 1, 1, 1, 1, 2, 4].length) (baseStart_4568374 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4568374 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4568374 prefixEnd_4568374 := by exact prefixLift 4568374
  have htrace : WordTrace (prefixWord ++ tailWord_4568374) baseStart_4568374 baseEnd_4568374 := by
    simpa [prefixWord, tailWord_4568374, baseEnd_4568374] using wordTrace_append hprefix tailTrace_4568374
  have hstable : (prefixWord ++ tailWord_4568374).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4568374).length < 2 ^ (prefixWord ++ tailWord_4568374).sum := by decide
  have hdescent : baseEnd_4568374 < baseStart_4568374 := by decide
  rcases family_descends (prefixWord ++ tailWord_4568374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4568377 : List Nat := [1, 2, 1, 6, 3, 1, 1, 1, 1, 3, 3]
def baseStart_4568377 : Nat := 118140960795 + 4568377 * 2 ^ 59
def prefixEnd_4568377 : Nat := 4983230072969 + 3 ^ 40 * 4568377 * 2
def baseEnd_4568377 : Nat := 2345773211944977937677923

theorem tailTrace_4568377 : CollatzResearch.WordTrace tailWord_4568377 prefixEnd_4568377 2345773211944977937677923 := by
  unfold tailWord_4568377
  simp only [CollatzResearch.WordTrace]
  refine ⟨166622397770557820520487385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111081598513705213680324923 166622397770557820520487385)
  ·
    refine ⟨124966798327918365390365539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 166622397770557820520487385 124966798327918365390365539)
    ·
      refine ⟨187450197491877548085548309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 124966798327918365390365539 187450197491877548085548309)
      ·
        refine ⟨8786728007431760066510077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 187450197491877548085548309 8786728007431760066510077)
        ·
          refine ⟨3295023002786910024941279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8786728007431760066510077 3295023002786910024941279)
          ·
            refine ⟨4942534504180365037411919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3295023002786910024941279 4942534504180365037411919)
            ·
              refine ⟨7413801756270547556117879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4942534504180365037411919 7413801756270547556117879)
              ·
                refine ⟨11120702634405821334176819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7413801756270547556117879 11120702634405821334176819)
                ·
                  refine ⟨16681053951608732001265229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11120702634405821334176819 16681053951608732001265229)
                  ·
                    refine ⟨6255395231853274500474461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16681053951608732001265229 6255395231853274500474461)
                    ·
                      refine ⟨2345773211944977937677923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6255395231853274500474461 2345773211944977937677923)
                      ·
                        rfl

theorem cell23_4568377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 3, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 3, 1, 1, 1, 1, 3, 3].length) (baseStart_4568377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4568377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4568377 prefixEnd_4568377 := by exact prefixLift 4568377
  have htrace : WordTrace (prefixWord ++ tailWord_4568377) baseStart_4568377 baseEnd_4568377 := by
    simpa [prefixWord, tailWord_4568377, baseEnd_4568377] using wordTrace_append hprefix tailTrace_4568377
  have hstable : (prefixWord ++ tailWord_4568377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4568377).length < 2 ^ (prefixWord ++ tailWord_4568377).sum := by decide
  have hdescent : baseEnd_4568377 < baseStart_4568377 := by decide
  rcases family_descends (prefixWord ++ tailWord_4568377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4568473 : List Nat := [1, 2, 1, 2, 1, 5, 2, 2, 2, 1, 4]
def baseStart_4568473 : Nat := 118140960795 + 4568473 * 2 ^ 59
def prefixEnd_4568473 : Nat := 4983230072969 + 3 ^ 40 * 4568473 * 2
def baseEnd_4568473 : Nat := 2345822506087809562077481

theorem tailTrace_4568473 : CollatzResearch.WordTrace tailWord_4568473 prefixEnd_4568473 2345822506087809562077481 := by
  unfold tailWord_4568473
  simp only [CollatzResearch.WordTrace]
  refine ⟨166625899178210028915982073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111083932785473352610654715 166625899178210028915982073)
  ·
    refine ⟨124969424383657521686986555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 166625899178210028915982073 124969424383657521686986555)
    ·
      refine ⟨187454136575486282530479833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 124969424383657521686986555 187454136575486282530479833)
      ·
        refine ⟨140590602431614711897859875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 187454136575486282530479833 140590602431614711897859875)
        ·
          refine ⟨210885903647422067846789813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 140590602431614711897859875 210885903647422067846789813)
          ·
            refine ⟨19770553466945818860636545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 210885903647422067846789813 19770553466945818860636545)
            ·
              refine ⟨14827915100209364145477409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19770553466945818860636545 14827915100209364145477409)
              ·
                refine ⟨11120936325157023109108057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14827915100209364145477409 11120936325157023109108057)
                ·
                  refine ⟨8340702243867767331831043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11120936325157023109108057 8340702243867767331831043)
                  ·
                    refine ⟨12511053365801650997746565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8340702243867767331831043 12511053365801650997746565)
                    ·
                      refine ⟨2345822506087809562077481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12511053365801650997746565 2345822506087809562077481)
                      ·
                        rfl

theorem cell23_4568473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 2, 2, 2, 1, 4].length) (baseStart_4568473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4568473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4568473 prefixEnd_4568473 := by exact prefixLift 4568473
  have htrace : WordTrace (prefixWord ++ tailWord_4568473) baseStart_4568473 baseEnd_4568473 := by
    simpa [prefixWord, tailWord_4568473, baseEnd_4568473] using wordTrace_append hprefix tailTrace_4568473
  have hstable : (prefixWord ++ tailWord_4568473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4568473).length < 2 ^ (prefixWord ++ tailWord_4568473).sum := by decide
  have hdescent : baseEnd_4568473 < baseStart_4568473 := by decide
  rcases family_descends (prefixWord ++ tailWord_4568473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4568483 : List Nat := [1, 1, 1, 4, 1, 3, 2, 3, 3, 4]
def baseStart_4568483 : Nat := 118140960795 + 4568483 * 2 ^ 59
def prefixEnd_4568483 : Nat := 4983230072969 + 3 ^ 40 * 4568483 * 2
def baseEnd_4568483 : Nat := 781942546964784840984145

theorem tailTrace_4568483 : CollatzResearch.WordTrace tailWord_4568483 prefixEnd_4568483 781942546964784840984145 := by
  unfold tailWord_4568483
  simp only [CollatzResearch.WordTrace]
  refine ⟨166626263908173800623846103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111084175938782533749230735 166626263908173800623846103)
  ·
    refine ⟨249939395862260700935769155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 166626263908173800623846103 249939395862260700935769155)
    ·
      refine ⟨374909093793391051403653733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 249939395862260700935769155 374909093793391051403653733)
      ·
        refine ⟨70295455086260822138185075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 374909093793391051403653733 70295455086260822138185075)
        ·
          refine ⟨105443182629391233207277613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70295455086260822138185075 105443182629391233207277613)
          ·
            refine ⟨39541193486021712452729105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 105443182629391233207277613 39541193486021712452729105)
            ·
              refine ⟨29655895114516284339546829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39541193486021712452729105 29655895114516284339546829)
              ·
                refine ⟨11120960667943606627330061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29655895114516284339546829 11120960667943606627330061)
                ·
                  refine ⟨4170360250478852485248773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11120960667943606627330061 4170360250478852485248773)
                  ·
                    refine ⟨781942546964784840984145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4170360250478852485248773 781942546964784840984145)
                    ·
                      rfl

theorem cell23_4568483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 2, 3, 3, 4].length) (baseStart_4568483 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4568483 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4568483 prefixEnd_4568483 := by exact prefixLift 4568483
  have htrace : WordTrace (prefixWord ++ tailWord_4568483) baseStart_4568483 baseEnd_4568483 := by
    simpa [prefixWord, tailWord_4568483, baseEnd_4568483] using wordTrace_append hprefix tailTrace_4568483
  have hstable : (prefixWord ++ tailWord_4568483).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4568483).length < 2 ^ (prefixWord ++ tailWord_4568483).sum := by decide
  have hdescent : baseEnd_4568483 < baseStart_4568483 := by decide
  rcases family_descends (prefixWord ++ tailWord_4568483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4568534 : List Nat := [5, 2, 1, 1, 1, 2, 2, 4, 1, 4]
def baseStart_4568534 : Nat := 118140960795 + 4568534 * 2 ^ 59
def prefixEnd_4568534 : Nat := 4983230072969 + 3 ^ 40 * 4568534 * 2
def baseEnd_4568534 : Nat := 781951276135911274471567

theorem tailTrace_4568534 : CollatzResearch.WordTrace tailWord_4568534 prefixEnd_4568534 781951276135911274471567 := by
  unfold tailWord_4568534
  simp only [CollatzResearch.WordTrace]
  refine ⟨10414257751936814770872041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 111085416020659357555968437 10414257751936814770872041)
  ·
    refine ⟨7810693313952611078154031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10414257751936814770872041 7810693313952611078154031)
    ·
      refine ⟨11716039970928916617231047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7810693313952611078154031 11716039970928916617231047)
      ·
        refine ⟨17574059956393374925846571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11716039970928916617231047 17574059956393374925846571)
        ·
          refine ⟨26361089934590062388769857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17574059956393374925846571 26361089934590062388769857)
          ·
            refine ⟨19770817450942546791577393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26361089934590062388769857 19770817450942546791577393)
            ·
              refine ⟨14828113088206910093683045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19770817450942546791577393 14828113088206910093683045)
              ·
                refine ⟨2780271204038795642565571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14828113088206910093683045 2780271204038795642565571)
                ·
                  refine ⟨4170406806058193463848357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2780271204038795642565571 4170406806058193463848357)
                  ·
                    refine ⟨781951276135911274471567, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4170406806058193463848357 781951276135911274471567)
                    ·
                      rfl

theorem cell23_4568534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 2, 4, 1, 4].length) (baseStart_4568534 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4568534 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4568534 prefixEnd_4568534 := by exact prefixLift 4568534
  have htrace : WordTrace (prefixWord ++ tailWord_4568534) baseStart_4568534 baseEnd_4568534 := by
    simpa [prefixWord, tailWord_4568534, baseEnd_4568534] using wordTrace_append hprefix tailTrace_4568534
  have hstable : (prefixWord ++ tailWord_4568534).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4568534).length < 2 ^ (prefixWord ++ tailWord_4568534).sum := by decide
  have hdescent : baseEnd_4568534 < baseStart_4568534 := by decide
  rcases family_descends (prefixWord ++ tailWord_4568534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4568560 : List Nat := [2, 1, 1, 1, 3, 5, 2, 2, 1, 5]
def baseStart_4568560 : Nat := 118140960795 + 4568560 * 2 ^ 59
def prefixEnd_4568560 : Nat := 4983230072969 + 3 ^ 40 * 4568560 * 2
def baseEnd_4568560 : Nat := 781955726301583573896527

theorem tailTrace_4568560 : CollatzResearch.WordTrace tailWord_4568560 prefixEnd_4568560 781955726301583573896527 := by
  unfold tailWord_4568560
  simp only [CollatzResearch.WordTrace]
  refine ⟨83314536164447421387199567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111086048219263228516266089 83314536164447421387199567)
  ·
    refine ⟨124971804246671132080799351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83314536164447421387199567 124971804246671132080799351)
    ·
      refine ⟨187457706370006698121199027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 124971804246671132080799351 187457706370006698121199027)
      ·
        refine ⟨281186559555010047181798541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 187457706370006698121199027 281186559555010047181798541)
        ·
          refine ⟨105444959833128767693174453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 281186559555010047181798541 105444959833128767693174453)
          ·
            refine ⟨9885464984355821971235105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 105444959833128767693174453 9885464984355821971235105)
            ·
              refine ⟨7414098738266866478426329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9885464984355821971235105 7414098738266866478426329)
              ·
                refine ⟨5560574053700149858819747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7414098738266866478426329 5560574053700149858819747)
                ·
                  refine ⟨8340861080550224788229621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5560574053700149858819747 8340861080550224788229621)
                  ·
                    refine ⟨781955726301583573896527, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8340861080550224788229621 781955726301583573896527)
                    ·
                      rfl

theorem cell23_4568560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 5, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 5, 2, 2, 1, 5].length) (baseStart_4568560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4568560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4568560 prefixEnd_4568560 := by exact prefixLift 4568560
  have htrace : WordTrace (prefixWord ++ tailWord_4568560) baseStart_4568560 baseEnd_4568560 := by
    simpa [prefixWord, tailWord_4568560, baseEnd_4568560] using wordTrace_append hprefix tailTrace_4568560
  have hstable : (prefixWord ++ tailWord_4568560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4568560).length < 2 ^ (prefixWord ++ tailWord_4568560).sum := by decide
  have hdescent : baseEnd_4568560 < baseStart_4568560 := by decide
  rcases family_descends (prefixWord ++ tailWord_4568560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4568607 : List Nat := [1, 1, 2, 4, 1, 1, 6, 1, 2, 4]
def baseStart_4568607 : Nat := 118140960795 + 4568607 * 2 ^ 59
def prefixEnd_4568607 : Nat := 4983230072969 + 3 ^ 40 * 4568607 * 2
def baseEnd_4568607 : Nat := 781963770831837345933955

theorem tailTrace_4568607 : CollatzResearch.WordTrace tailWord_4568607 prefixEnd_4568607 781963770831837345933955 := by
  unfold tailWord_4568607
  simp only [CollatzResearch.WordTrace]
  refine ⟨166630786559724569801360075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111087191039816379867573383 166630786559724569801360075)
  ·
    refine ⟨249946179839586854702040113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 166630786559724569801360075 249946179839586854702040113)
    ·
      refine ⟨187459634879690141026530085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 249946179839586854702040113 187459634879690141026530085)
      ·
        refine ⟨35148681539941901442474391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 187459634879690141026530085 35148681539941901442474391)
        ·
          refine ⟨52723022309912852163711587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35148681539941901442474391 52723022309912852163711587)
          ·
            refine ⟨79084533464869278245567381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52723022309912852163711587 79084533464869278245567381)
            ·
              refine ⟨3707087506165747417760971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 79084533464869278245567381 3707087506165747417760971)
              ·
                refine ⟨5560631259248621126641457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3707087506165747417760971 5560631259248621126641457)
                ·
                  refine ⟨4170473444436465844981093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5560631259248621126641457 4170473444436465844981093)
                  ·
                    refine ⟨781963770831837345933955, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4170473444436465844981093 781963770831837345933955)
                    ·
                      rfl

theorem cell23_4568607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 6, 1, 2, 4].length) (baseStart_4568607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4568607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4568607 prefixEnd_4568607 := by exact prefixLift 4568607
  have htrace : WordTrace (prefixWord ++ tailWord_4568607) baseStart_4568607 baseEnd_4568607 := by
    simpa [prefixWord, tailWord_4568607, baseEnd_4568607] using wordTrace_append hprefix tailTrace_4568607
  have hstable : (prefixWord ++ tailWord_4568607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4568607).length < 2 ^ (prefixWord ++ tailWord_4568607).sum := by decide
  have hdescent : baseEnd_4568607 < baseStart_4568607 := by decide
  rcases family_descends (prefixWord ++ tailWord_4568607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4568663 : List Nat := [1, 1, 3, 2, 2, 3, 1, 1, 1, 8]
def baseStart_4568663 : Nat := 118140960795 + 4568663 * 2 ^ 59
def prefixEnd_4568663 : Nat := 4983230072969 + 3 ^ 40 * 4568663 * 2
def baseEnd_4568663 : Nat := 781973355804054606233869

theorem tailTrace_4568663 : CollatzResearch.WordTrace tailWord_4568663 prefixEnd_4568663 781973355804054606233869 := by
  unfold tailWord_4568663
  simp only [CollatzResearch.WordTrace]
  refine ⟨166632829047521691365398643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111088552698347794243599095 166632829047521691365398643)
  ·
    refine ⟨249949243571282537048097965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 166632829047521691365398643 249949243571282537048097965)
    ·
      refine ⟨93730966339230951393036737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 249949243571282537048097965 93730966339230951393036737)
      ·
        refine ⟨70298224754423213544777553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 93730966339230951393036737 70298224754423213544777553)
        ·
          refine ⟨52723668565817410158583165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 70298224754423213544777553 52723668565817410158583165)
          ·
            refine ⟨19771375712181528809468687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 52723668565817410158583165 19771375712181528809468687)
            ·
              refine ⟨29657063568272293214203031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19771375712181528809468687 29657063568272293214203031)
              ·
                refine ⟨44485595352408439821304547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29657063568272293214203031 44485595352408439821304547)
                ·
                  refine ⟨66728393028612659731956821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 44485595352408439821304547 66728393028612659731956821)
                  ·
                    refine ⟨781973355804054606233869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 66728393028612659731956821 781973355804054606233869)
                    ·
                      rfl

theorem cell23_4568663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 1, 1, 1, 8].length) (baseStart_4568663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4568663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4568663 prefixEnd_4568663 := by exact prefixLift 4568663
  have htrace : WordTrace (prefixWord ++ tailWord_4568663) baseStart_4568663 baseEnd_4568663 := by
    simpa [prefixWord, tailWord_4568663, baseEnd_4568663] using wordTrace_append hprefix tailTrace_4568663
  have hstable : (prefixWord ++ tailWord_4568663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4568663).length < 2 ^ (prefixWord ++ tailWord_4568663).sum := by decide
  have hdescent : baseEnd_4568663 < baseStart_4568663 := by decide
  rcases family_descends (prefixWord ++ tailWord_4568663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4568687 : List Nat := [1, 1, 2, 1, 3, 2, 1, 4, 4, 2, 2]
def baseStart_4568687 : Nat := 118140960795 + 4568687 * 2 ^ 59
def prefixEnd_4568687 : Nat := 4983230072969 + 3 ^ 40 * 4568687 * 2
def baseEnd_4568687 : Nat := 2345932390947871724801497

theorem tailTrace_4568687 : CollatzResearch.WordTrace tailWord_4568687 prefixEnd_4568687 2345932390947871724801497 := by
  unfold tailWord_4568687
  simp only [CollatzResearch.WordTrace]
  refine ⟨166633704399434743464272315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111089136266289828976181543 166633704399434743464272315)
  ·
    refine ⟨249950556599152115196408473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 166633704399434743464272315 249950556599152115196408473)
    ·
      refine ⟨187462917449364086397306355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 249950556599152115196408473 187462917449364086397306355)
      ·
        refine ⟨281194376174046129595959533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 187462917449364086397306355 281194376174046129595959533)
        ·
          refine ⟨105447891065267298598484825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 281194376174046129595959533 105447891065267298598484825)
          ·
            refine ⟨79085918298950473948863619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 105447891065267298598484825 79085918298950473948863619)
            ·
              refine ⟨118628877448425710923295429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 79085918298950473948863619 118628877448425710923295429)
              ·
                refine ⟨22242914521579820798117893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 118628877448425710923295429 22242914521579820798117893)
                ·
                  refine ⟨4170546472796216399647105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22242914521579820798117893 4170546472796216399647105)
                  ·
                    refine ⟨3127909854597162299735329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4170546472796216399647105 3127909854597162299735329)
                    ·
                      refine ⟨2345932390947871724801497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3127909854597162299735329 2345932390947871724801497)
                      ·
                        rfl

theorem cell23_4568687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 4, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 4, 4, 2, 2].length) (baseStart_4568687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4568687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4568687 prefixEnd_4568687 := by exact prefixLift 4568687
  have htrace : WordTrace (prefixWord ++ tailWord_4568687) baseStart_4568687 baseEnd_4568687 := by
    simpa [prefixWord, tailWord_4568687, baseEnd_4568687] using wordTrace_append hprefix tailTrace_4568687
  have hstable : (prefixWord ++ tailWord_4568687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4568687).length < 2 ^ (prefixWord ++ tailWord_4568687).sum := by decide
  have hdescent : baseEnd_4568687 < baseStart_4568687 := by decide
  rcases family_descends (prefixWord ++ tailWord_4568687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4568740 : List Nat := [2, 3, 1, 2, 2, 2, 2, 1, 1, 7]
def baseStart_4568740 : Nat := 118140960795 + 4568740 * 2 ^ 59
def prefixEnd_4568740 : Nat := 4983230072969 + 3 ^ 40 * 4568740 * 2
def baseEnd_4568740 : Nat := 781986535140853339146251

theorem tailTrace_4568740 : CollatzResearch.WordTrace tailWord_4568740 prefixEnd_4568740 781986535140853339146251 := by
  unfold tailWord_4568740
  simp only [CollatzResearch.WordTrace]
  refine ⟨83317818734121366757975837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111090424978828489010634449 83317818734121366757975837)
  ·
    refine ⟨31244182025295512534240939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 83317818734121366757975837 31244182025295512534240939)
    ·
      refine ⟨46866273037943268801361409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31244182025295512534240939 46866273037943268801361409)
      ·
        refine ⟨35149704778457451601021057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46866273037943268801361409 35149704778457451601021057)
        ·
          refine ⟨26362278583843088700765793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35149704778457451601021057 26362278583843088700765793)
          ·
            refine ⟨19771708937882316525574345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26362278583843088700765793 19771708937882316525574345)
            ·
              refine ⟨14828781703411737394180759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19771708937882316525574345 14828781703411737394180759)
              ·
                refine ⟨22243172555117606091271139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14828781703411737394180759 22243172555117606091271139)
                ·
                  refine ⟨33364758832676409136906709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22243172555117606091271139 33364758832676409136906709)
                  ·
                    refine ⟨781986535140853339146251, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 33364758832676409136906709 781986535140853339146251)
                    ·
                      rfl

theorem cell23_4568740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 2, 1, 1, 7].length) (baseStart_4568740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4568740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4568740 prefixEnd_4568740 := by exact prefixLift 4568740
  have htrace : WordTrace (prefixWord ++ tailWord_4568740) baseStart_4568740 baseEnd_4568740 := by
    simpa [prefixWord, tailWord_4568740, baseEnd_4568740] using wordTrace_append hprefix tailTrace_4568740
  have hstable : (prefixWord ++ tailWord_4568740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4568740).length < 2 ^ (prefixWord ++ tailWord_4568740).sum := by decide
  have hdescent : baseEnd_4568740 < baseStart_4568740 := by decide
  rcases family_descends (prefixWord ++ tailWord_4568740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4568804 : List Nat := [2, 3, 1, 1, 1, 3, 2, 5, 1, 4]
def baseStart_4568804 : Nat := 118140960795 + 4568804 * 2 ^ 59
def prefixEnd_4568804 : Nat := 4983230072969 + 3 ^ 40 * 4568804 * 2
def baseEnd_4568804 : Nat := 781997489394815922346153

theorem tailTrace_4568804 : CollatzResearch.WordTrace tailWord_4568804 prefixEnd_4568804 781997489394815922346153 := by
  unfold tailWord_4568804
  simp only [CollatzResearch.WordTrace]
  refine ⟨83318985870005436223140733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111091981160007248297520977 83318985870005436223140733)
  ·
    refine ⟨31244619701252038583677775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 83318985870005436223140733 31244619701252038583677775)
    ·
      refine ⟨46866929551878057875516663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31244619701252038583677775 46866929551878057875516663)
      ·
        refine ⟨70300394327817086813274995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46866929551878057875516663 70300394327817086813274995)
        ·
          refine ⟨105450591491725630219912493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70300394327817086813274995 105450591491725630219912493)
          ·
            refine ⟨39543971809397111332467185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 105450591491725630219912493 39543971809397111332467185)
            ·
              refine ⟨29657978857047833499350389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39543971809397111332467185 29657978857047833499350389)
              ·
                refine ⟨2780435517848234390564099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 29657978857047833499350389 2780435517848234390564099)
                ·
                  refine ⟨4170653276772351585846149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2780435517848234390564099 4170653276772351585846149)
                  ·
                    refine ⟨781997489394815922346153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4170653276772351585846149 781997489394815922346153)
                    ·
                      rfl

theorem cell23_4568804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 2, 5, 1, 4].length) (baseStart_4568804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4568804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4568804 prefixEnd_4568804 := by exact prefixLift 4568804
  have htrace : WordTrace (prefixWord ++ tailWord_4568804) baseStart_4568804 baseEnd_4568804 := by
    simpa [prefixWord, tailWord_4568804, baseEnd_4568804] using wordTrace_append hprefix tailTrace_4568804
  have hstable : (prefixWord ++ tailWord_4568804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4568804).length < 2 ^ (prefixWord ++ tailWord_4568804).sum := by decide
  have hdescent : baseEnd_4568804 < baseStart_4568804 := by decide
  rcases family_descends (prefixWord ++ tailWord_4568804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4568817 : List Nat := [1, 2, 2, 2, 2, 4, 2, 2, 6]
def baseStart_4568817 : Nat := 118140960795 + 4568817 * 2 ^ 59
def prefixEnd_4568817 : Nat := 4983230072969 + 3 ^ 40 * 4568817 * 2
def baseEnd_4568817 : Nat := 260666571492550690686211

theorem tailTrace_4568817 : CollatzResearch.WordTrace tailWord_4568817 prefixEnd_4568817 260666571492550690686211 := by
  unfold tailWord_4568817
  simp only [CollatzResearch.WordTrace]
  refine ⟨166638445888963775666504705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111092297259309183777669803 166638445888963775666504705)
  ·
    refine ⟨124978834416722831749878529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 166638445888963775666504705 124978834416722831749878529)
    ·
      refine ⟨93734125812542123812408897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 124978834416722831749878529 93734125812542123812408897)
      ·
        refine ⟨70300594359406592859306673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 93734125812542123812408897 70300594359406592859306673)
        ·
          refine ⟨52725445769554944644480005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 70300594359406592859306673 52725445769554944644480005)
          ·
            refine ⟨9886021081791552120840001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 52725445769554944644480005 9886021081791552120840001)
            ·
              refine ⟨7414515811343664090630001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9886021081791552120840001 7414515811343664090630001)
              ·
                refine ⟨5560886858507748067972501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7414515811343664090630001 5560886858507748067972501)
                ·
                  refine ⟨260666571492550690686211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5560886858507748067972501 260666571492550690686211)
                  ·
                    rfl

theorem cell23_4568817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 4, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 4, 2, 2, 6].length) (baseStart_4568817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4568817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4568817 prefixEnd_4568817 := by exact prefixLift 4568817
  have htrace : WordTrace (prefixWord ++ tailWord_4568817) baseStart_4568817 baseEnd_4568817 := by
    simpa [prefixWord, tailWord_4568817, baseEnd_4568817] using wordTrace_append hprefix tailTrace_4568817
  have hstable : (prefixWord ++ tailWord_4568817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4568817).length < 2 ^ (prefixWord ++ tailWord_4568817).sum := by decide
  have hdescent : baseEnd_4568817 < baseStart_4568817 := by decide
  rcases family_descends (prefixWord ++ tailWord_4568817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4568840 : List Nat := [2, 1, 3, 2, 2, 1, 1, 1, 2, 1, 7]
def baseStart_4568840 : Nat := 118140960795 + 4568840 * 2 ^ 59
def prefixEnd_4568840 : Nat := 4983230072969 + 3 ^ 40 * 4568840 * 2
def baseEnd_4568840 : Nat := 2346010953488009626188293

theorem tailTrace_4568840 : CollatzResearch.WordTrace tailWord_4568840 prefixEnd_4568840 2346010953488009626188293 := by
  unfold tailWord_4568840
  simp only [CollatzResearch.WordTrace]
  refine ⟨83319642383940225297295987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111092856511920300396394649 83319642383940225297295987)
  ·
    refine ⟨124979463575910337945943981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83319642383940225297295987 124979463575910337945943981)
    ·
      refine ⟨46867298840966376729728993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 124979463575910337945943981 46867298840966376729728993)
      ·
        refine ⟨35150474130724782547296745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46867298840966376729728993 35150474130724782547296745)
        ·
          refine ⟨26362855598043586910472559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35150474130724782547296745 26362855598043586910472559)
          ·
            refine ⟨39544283397065380365708839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26362855598043586910472559 39544283397065380365708839)
            ·
              refine ⟨59316425095598070548563259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39544283397065380365708839 59316425095598070548563259)
              ·
                refine ⟨88974637643397105822844889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 59316425095598070548563259 88974637643397105822844889)
                ·
                  refine ⟨66730978232547829367133667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 88974637643397105822844889 66730978232547829367133667)
                  ·
                    refine ⟨100096467348821744050700501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 66730978232547829367133667 100096467348821744050700501)
                    ·
                      refine ⟨2346010953488009626188293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 100096467348821744050700501 2346010953488009626188293)
                      ·
                        rfl

theorem cell23_4568840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 1, 1, 2, 1, 7].length) (baseStart_4568840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4568840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4568840 prefixEnd_4568840 := by exact prefixLift 4568840
  have htrace : WordTrace (prefixWord ++ tailWord_4568840) baseStart_4568840 baseEnd_4568840 := by
    simpa [prefixWord, tailWord_4568840, baseEnd_4568840] using wordTrace_append hprefix tailTrace_4568840
  have hstable : (prefixWord ++ tailWord_4568840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4568840).length < 2 ^ (prefixWord ++ tailWord_4568840).sum := by decide
  have hdescent : baseEnd_4568840 < baseStart_4568840 := by decide
  rcases family_descends (prefixWord ++ tailWord_4568840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4568878 : List Nat := [4, 1, 3, 2, 2, 1, 2, 1, 3, 1, 3]
def baseStart_4568878 : Nat := 118140960795 + 4568878 * 2 ^ 59
def prefixEnd_4568878 : Nat := 4983230072969 + 3 ^ 40 * 4568878 * 2
def baseEnd_4568878 : Nat := 2346030465752880477513119

theorem tailTrace_4568878 : CollatzResearch.WordTrace tailWord_4568878 prefixEnd_4568878 2346030465752880477513119 := by
  unfold tailWord_4568878
  simp only [CollatzResearch.WordTrace]
  refine ⟨20830083842717847885559411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 111093780494495188722983525 20830083842717847885559411)
  ·
    refine ⟨31245125764076771828339117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20830083842717847885559411 31245125764076771828339117)
    ·
      refine ⟨11716922161528789435627169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31245125764076771828339117 11716922161528789435627169)
      ·
        refine ⟨8787691621146592076720377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11716922161528789435627169 8787691621146592076720377)
        ·
          refine ⟨6590768715859944057540283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8787691621146592076720377 6590768715859944057540283)
          ·
            refine ⟨9886153073789916086310425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6590768715859944057540283 9886153073789916086310425)
            ·
              refine ⟨7414614805342437064732819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9886153073789916086310425 7414614805342437064732819)
              ·
                refine ⟨11121922208013655597099229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7414614805342437064732819 11121922208013655597099229)
                ·
                  refine ⟨4170720828005120848912211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11121922208013655597099229 4170720828005120848912211)
                  ·
                    refine ⟨6256081242007681273368317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4170720828005120848912211 6256081242007681273368317)
                    ·
                      refine ⟨2346030465752880477513119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6256081242007681273368317 2346030465752880477513119)
                      ·
                        rfl

theorem cell23_4568878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 1, 2, 1, 3, 1, 3].length) (baseStart_4568878 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4568878 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4568878 prefixEnd_4568878 := by exact prefixLift 4568878
  have htrace : WordTrace (prefixWord ++ tailWord_4568878) baseStart_4568878 baseEnd_4568878 := by
    simpa [prefixWord, tailWord_4568878, baseEnd_4568878] using wordTrace_append hprefix tailTrace_4568878
  have hstable : (prefixWord ++ tailWord_4568878).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4568878).length < 2 ^ (prefixWord ++ tailWord_4568878).sum := by decide
  have hdescent : baseEnd_4568878 < baseStart_4568878 := by decide
  rcases family_descends (prefixWord ++ tailWord_4568878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4568880 : List Nat := [2, 1, 1, 1, 2, 2, 1, 1, 2, 6, 4]
def baseStart_4568880 : Nat := 118140960795 + 4568880 * 2 ^ 59
def prefixEnd_4568880 : Nat := 4983230072969 + 3 ^ 40 * 4568880 * 2
def baseEnd_4568880 : Nat := 2346031492714189469688109

theorem tailTrace_4568880 : CollatzResearch.WordTrace tailWord_4568880 prefixEnd_4568880 2346031492714189469688109 := by
  unfold tailWord_4568880
  simp only [CollatzResearch.WordTrace]
  refine ⟨83320371843867768713024047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111093829125157024950698729 83320371843867768713024047)
  ·
    refine ⟨124980557765801653069536071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83320371843867768713024047 124980557765801653069536071)
    ·
      refine ⟨187470836648702479604304107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 124980557765801653069536071 187470836648702479604304107)
      ·
        refine ⟨281206254973053719406456161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 187470836648702479604304107 281206254973053719406456161)
        ·
          refine ⟨210904691229790289554842121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 281206254973053719406456161 210904691229790289554842121)
          ·
            refine ⟨158178518422342717166131591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 210904691229790289554842121 158178518422342717166131591)
            ·
              refine ⟨237267777633514075749197387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 158178518422342717166131591 237267777633514075749197387)
              ·
                refine ⟨355901666450271113623796081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 237267777633514075749197387 355901666450271113623796081)
                ·
                  refine ⟨266926249837703335217847061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 355901666450271113623796081 266926249837703335217847061)
                  ·
                    refine ⟨12512167961142343838336581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 266926249837703335217847061 12512167961142343838336581)
                    ·
                      refine ⟨2346031492714189469688109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12512167961142343838336581 2346031492714189469688109)
                      ·
                        rfl

theorem cell23_4568880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 1, 2, 6, 4].length) (baseStart_4568880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4568880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4568880 prefixEnd_4568880 := by exact prefixLift 4568880
  have htrace : WordTrace (prefixWord ++ tailWord_4568880) baseStart_4568880 baseEnd_4568880 := by
    simpa [prefixWord, tailWord_4568880, baseEnd_4568880] using wordTrace_append hprefix tailTrace_4568880
  have hstable : (prefixWord ++ tailWord_4568880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4568880).length < 2 ^ (prefixWord ++ tailWord_4568880).sum := by decide
  have hdescent : baseEnd_4568880 < baseStart_4568880 := by decide
  rcases family_descends (prefixWord ++ tailWord_4568880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4568887 : List Nat := [1, 1, 3, 1, 2, 1, 2, 4, 3, 2, 3]
def baseStart_4568887 : Nat := 118140960795 + 4568887 * 2 ^ 59
def prefixEnd_4568887 : Nat := 4983230072969 + 3 ^ 40 * 4568887 * 2
def baseEnd_4568887 : Nat := 2346035087078770942300577

theorem tailTrace_4568887 : CollatzResearch.WordTrace tailWord_4568887 prefixEnd_4568887 2346035087078770942300577 := by
  unfold tailWord_4568887
  simp only [CollatzResearch.WordTrace]
  refine ⟨166640998998710177621552915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111093999332473451747701943 166640998998710177621552915)
  ·
    refine ⟨249961498498065266432329373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 166640998998710177621552915 249961498498065266432329373)
    ·
      refine ⟨93735561936774474912123515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 249961498498065266432329373 93735561936774474912123515)
      ·
        refine ⟨140603342905161712368185273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93735561936774474912123515 140603342905161712368185273)
        ·
          refine ⟨105452507178871284276138955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 140603342905161712368185273 105452507178871284276138955)
          ·
            refine ⟨158178760768306926414208433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 105452507178871284276138955 158178760768306926414208433)
            ·
              refine ⟨118634070576230194810656325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 158178760768306926414208433 118634070576230194810656325)
              ·
                refine ⟨22243888233043161526998061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 118634070576230194810656325 22243888233043161526998061)
                ·
                  refine ⟨8341458087391185572624273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22243888233043161526998061 8341458087391185572624273)
                  ·
                    refine ⟨6256093565543389179468205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8341458087391185572624273 6256093565543389179468205)
                    ·
                      refine ⟨2346035087078770942300577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6256093565543389179468205 2346035087078770942300577)
                      ·
                        rfl

theorem cell23_4568887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 4, 3, 2, 3].length) (baseStart_4568887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4568887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4568887 prefixEnd_4568887 := by exact prefixLift 4568887
  have htrace : WordTrace (prefixWord ++ tailWord_4568887) baseStart_4568887 baseEnd_4568887 := by
    simpa [prefixWord, tailWord_4568887, baseEnd_4568887] using wordTrace_append hprefix tailTrace_4568887
  have hstable : (prefixWord ++ tailWord_4568887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4568887).length < 2 ^ (prefixWord ++ tailWord_4568887).sum := by decide
  have hdescent : baseEnd_4568887 < baseStart_4568887 := by decide
  rcases family_descends (prefixWord ++ tailWord_4568887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4568894 : List Nat := [4, 2, 1, 2, 2, 1, 3, 1, 1, 6]
def baseStart_4568894 : Nat := 118140960795 + 4568894 * 2 ^ 59
def prefixEnd_4568894 : Nat := 4983230072969 + 3 ^ 40 * 4568894 * 2
def baseEnd_4568894 : Nat := 782012893814450804971015

theorem tailTrace_4568894 : CollatzResearch.WordTrace tailWord_4568894 prefixEnd_4568894 782012893814450804971015 := by
  unfold tailWord_4568894
  simp only [CollatzResearch.WordTrace]
  refine ⟨20830156788710602227132217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 111094169539789878544705157 20830156788710602227132217)
  ·
    refine ⟨15622617591532951670349163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20830156788710602227132217 15622617591532951670349163)
    ·
      refine ⟨23433926387299427505523745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15622617591532951670349163 23433926387299427505523745)
      ·
        refine ⟨17575444790474570629142809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23433926387299427505523745 17575444790474570629142809)
        ·
          refine ⟨13181583592855927971857107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17575444790474570629142809 13181583592855927971857107)
          ·
            refine ⟨19772375389283891957785661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13181583592855927971857107 19772375389283891957785661)
            ·
              refine ⟨7414640770981459484169623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19772375389283891957785661 7414640770981459484169623)
              ·
                refine ⟨11121961156472189226254435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7414640770981459484169623 11121961156472189226254435)
                ·
                  refine ⟨16682941734708283839381653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11121961156472189226254435 16682941734708283839381653)
                  ·
                    refine ⟨782012893814450804971015, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16682941734708283839381653 782012893814450804971015)
                    ·
                      rfl

theorem cell23_4568894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 3, 1, 1, 6].length) (baseStart_4568894 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4568894 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4568894 prefixEnd_4568894 := by exact prefixLift 4568894
  have htrace : WordTrace (prefixWord ++ tailWord_4568894) baseStart_4568894 baseEnd_4568894 := by
    simpa [prefixWord, tailWord_4568894, baseEnd_4568894] using wordTrace_append hprefix tailTrace_4568894
  have hstable : (prefixWord ++ tailWord_4568894).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4568894).length < 2 ^ (prefixWord ++ tailWord_4568894).sum := by decide
  have hdescent : baseEnd_4568894 < baseStart_4568894 := by decide
  rcases family_descends (prefixWord ++ tailWord_4568894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4568904 : List Nat := [2, 1, 3, 1, 1, 4, 1, 4, 1, 2, 3]
def baseStart_4568904 : Nat := 118140960795 + 4568904 * 2 ^ 59
def prefixEnd_4568904 : Nat := 4983230072969 + 3 ^ 40 * 4568904 * 2
def baseEnd_4568904 : Nat := 2346043816249897375787999

theorem tailTrace_4568904 : CollatzResearch.WordTrace tailWord_4568904 prefixEnd_4568904 2346043816249897375787999 := by
  unfold tailWord_4568904
  simp only [CollatzResearch.WordTrace]
  refine ⟨83320809519824294762460883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111094412693099059683281177 83320809519824294762460883)
  ·
    refine ⟨124981214279736442143691325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83320809519824294762460883 124981214279736442143691325)
    ·
      refine ⟨46867955354901165803884247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 124981214279736442143691325 46867955354901165803884247)
      ·
        refine ⟨70301933032351748705826371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46867955354901165803884247 70301933032351748705826371)
        ·
          refine ⟨105452899548527623058739557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70301933032351748705826371 105452899548527623058739557)
          ·
            refine ⟨19772418665348929323513667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 105452899548527623058739557 19772418665348929323513667)
            ·
              refine ⟨29658627998023393985270501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19772418665348929323513667 29658627998023393985270501)
              ·
                refine ⟨5560992749629386372238219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 29658627998023393985270501 5560992749629386372238219)
                ·
                  refine ⟨8341489124444079558357329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5560992749629386372238219 8341489124444079558357329)
                  ·
                    refine ⟨6256116843333059668767997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8341489124444079558357329 6256116843333059668767997)
                    ·
                      refine ⟨2346043816249897375787999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6256116843333059668767997 2346043816249897375787999)
                      ·
                        rfl

theorem cell23_4568904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 1, 4, 1, 2, 3].length) (baseStart_4568904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4568904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4568904 prefixEnd_4568904 := by exact prefixLift 4568904
  have htrace : WordTrace (prefixWord ++ tailWord_4568904) baseStart_4568904 baseEnd_4568904 := by
    simpa [prefixWord, tailWord_4568904, baseEnd_4568904] using wordTrace_append hprefix tailTrace_4568904
  have hstable : (prefixWord ++ tailWord_4568904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4568904).length < 2 ^ (prefixWord ++ tailWord_4568904).sum := by decide
  have hdescent : baseEnd_4568904 < baseStart_4568904 := by decide
  rcases family_descends (prefixWord ++ tailWord_4568904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4568920 : List Nat := [2, 1, 2, 2, 1, 1, 1, 1, 3, 9]
def baseStart_4568920 : Nat := 118140960795 + 4568920 * 2 ^ 59
def prefixEnd_4568920 : Nat := 4983230072969 + 3 ^ 40 * 4568920 * 2
def baseEnd_4568920 : Nat := 782017343980123104395975

theorem tailTrace_4568920 : CollatzResearch.WordTrace tailWord_4568920 prefixEnd_4568920 782017343980123104395975 := by
  unfold tailWord_4568920
  simp only [CollatzResearch.WordTrace]
  refine ⟨83321101303795312128752107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111094801738393749505002809 83321101303795312128752107)
  ·
    refine ⟨124981651955692968193128161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83321101303795312128752107 124981651955692968193128161)
    ·
      refine ⟨93736238966769726144846121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 124981651955692968193128161 93736238966769726144846121)
      ·
        refine ⟨70302179225077294608634591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 93736238966769726144846121 70302179225077294608634591)
        ·
          refine ⟨105453268837615941912951887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70302179225077294608634591 105453268837615941912951887)
          ·
            refine ⟨158179903256423912869427831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 105453268837615941912951887 158179903256423912869427831)
            ·
              refine ⟨237269854884635869304141747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 158179903256423912869427831 237269854884635869304141747)
              ·
                refine ⟨355904782326953803956212621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 237269854884635869304141747 355904782326953803956212621)
                ·
                  refine ⟨133464293372607676483579733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 355904782326953803956212621 133464293372607676483579733)
                  ·
                    refine ⟨782017343980123104395975, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 133464293372607676483579733 782017343980123104395975)
                    ·
                      rfl

theorem cell23_4568920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 1, 3, 9].length) (baseStart_4568920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4568920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4568920 prefixEnd_4568920 := by exact prefixLift 4568920
  have htrace : WordTrace (prefixWord ++ tailWord_4568920) baseStart_4568920 baseEnd_4568920 := by
    simpa [prefixWord, tailWord_4568920, baseEnd_4568920] using wordTrace_append hprefix tailTrace_4568920
  have hstable : (prefixWord ++ tailWord_4568920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4568920).length < 2 ^ (prefixWord ++ tailWord_4568920).sum := by decide
  have hdescent : baseEnd_4568920 < baseStart_4568920 := by decide
  rcases family_descends (prefixWord ++ tailWord_4568920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4568924 : List Nat := [2, 2, 4, 2, 2, 2, 9]
def baseStart_4568924 : Nat := 118140960795 + 4568924 * 2 ^ 59
def prefixEnd_4568924 : Nat := 4983230072969 + 3 ^ 40 * 4568924 * 2
def baseEnd_4568924 : Nat := 28963630689666509846147

theorem tailTrace_4568924 : CollatzResearch.WordTrace tailWord_4568924 prefixEnd_4568924 28963630689666509846147 := by
  unfold tailWord_4568924
  simp only [CollatzResearch.WordTrace]
  refine ⟨83321174249788066470324913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111094898999717421960433217 83321174249788066470324913)
  ·
    refine ⟨62490880687341049852743685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83321174249788066470324913 62490880687341049852743685)
    ·
      refine ⟨11717040128876446847389441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 62490880687341049852743685 11717040128876446847389441)
      ·
        refine ⟨8787780096657335135542081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11717040128876446847389441 8787780096657335135542081)
        ·
          refine ⟨6590835072493001351656561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8787780096657335135542081 6590835072493001351656561)
          ·
            refine ⟨4943126304369751013742421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6590835072493001351656561 4943126304369751013742421)
            ·
              refine ⟨28963630689666509846147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 4943126304369751013742421 28963630689666509846147)
              ·
                rfl

theorem cell23_4568924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 2, 9].length) (baseStart_4568924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4568924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4568924 prefixEnd_4568924 := by exact prefixLift 4568924
  have htrace : WordTrace (prefixWord ++ tailWord_4568924) baseStart_4568924 baseEnd_4568924 := by
    simpa [prefixWord, tailWord_4568924, baseEnd_4568924] using wordTrace_append hprefix tailTrace_4568924
  have hstable : (prefixWord ++ tailWord_4568924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4568924).length < 2 ^ (prefixWord ++ tailWord_4568924).sum := by decide
  have hdescent : baseEnd_4568924 < baseStart_4568924 := by decide
  rcases family_descends (prefixWord ++ tailWord_4568924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4568935 : List Nat := [1, 1, 5, 1, 2, 1, 5, 2, 1, 2, 2]
def baseStart_4568935 : Nat := 118140960795 + 4568935 * 2 ^ 59
def prefixEnd_4568935 : Nat := 4983230072969 + 3 ^ 40 * 4568935 * 2
def baseEnd_4568935 : Nat := 2346059734150186754500357

theorem tailTrace_4568935 : CollatzResearch.WordTrace tailWord_4568935 prefixEnd_4568935 2346059734150186754500357 := by
  unfold tailWord_4568935
  simp only [CollatzResearch.WordTrace]
  refine ⟨166642749702536281819300259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111095166468357521212866839 166642749702536281819300259)
  ·
    refine ⟨249964124553804422728950389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 166642749702536281819300259 249964124553804422728950389)
    ·
      refine ⟨23434136676919164630839099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 249964124553804422728950389 23434136676919164630839099)
      ·
        refine ⟨35151205015378746946258649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23434136676919164630839099 35151205015378746946258649)
        ·
          refine ⟨26363403761534060209693987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35151205015378746946258649 26363403761534060209693987)
          ·
            refine ⟨39545105642301090314540981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26363403761534060209693987 39545105642301090314540981)
            ·
              refine ⟨3707353653965727216988217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 39545105642301090314540981 3707353653965727216988217)
              ·
                refine ⟨2780515240474295412741163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3707353653965727216988217 2780515240474295412741163)
                ·
                  refine ⟨4170772860711443119111745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2780515240474295412741163 4170772860711443119111745)
                  ·
                    refine ⟨3128079645533582339333809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4170772860711443119111745 3128079645533582339333809)
                    ·
                      refine ⟨2346059734150186754500357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3128079645533582339333809 2346059734150186754500357)
                      ·
                        rfl

theorem cell23_4568935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 5, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 5, 2, 1, 2, 2].length) (baseStart_4568935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4568935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4568935 prefixEnd_4568935 := by exact prefixLift 4568935
  have htrace : WordTrace (prefixWord ++ tailWord_4568935) baseStart_4568935 baseEnd_4568935 := by
    simpa [prefixWord, tailWord_4568935, baseEnd_4568935] using wordTrace_append hprefix tailTrace_4568935
  have hstable : (prefixWord ++ tailWord_4568935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4568935).length < 2 ^ (prefixWord ++ tailWord_4568935).sum := by decide
  have hdescent : baseEnd_4568935 < baseStart_4568935 := by decide
  rcases family_descends (prefixWord ++ tailWord_4568935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4568944 : List Nat := [2, 1, 1, 1, 4, 1, 1, 4, 3, 3, 2]
def baseStart_4568944 : Nat := 118140960795 + 4568944 * 2 ^ 59
def prefixEnd_4568944 : Nat := 4983230072969 + 3 ^ 40 * 4568944 * 2
def baseEnd_4568944 : Nat := 2346064355476077219287815

theorem tailTrace_4568944 : CollatzResearch.WordTrace tailWord_4568944 prefixEnd_4568944 2346064355476077219287815 := by
  unfold tailWord_4568944
  simp only [CollatzResearch.WordTrace]
  refine ⟨83321538979751838178188943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111095385306335784237585257 83321538979751838178188943)
  ·
    refine ⟨124982308469627757267283415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83321538979751838178188943 124982308469627757267283415)
    ·
      refine ⟨187473462704441635900925123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 124982308469627757267283415 187473462704441635900925123)
      ·
        refine ⟨281210194056662453851387685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 187473462704441635900925123 281210194056662453851387685)
        ·
          refine ⟨52726911385624210097135191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 281210194056662453851387685 52726911385624210097135191)
          ·
            refine ⟨79090367078436315145702787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52726911385624210097135191 79090367078436315145702787)
            ·
              refine ⟨118635550617654472718554181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 79090367078436315145702787 118635550617654472718554181)
              ·
                refine ⟨22244165740810213634728909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 118635550617654472718554181 22244165740810213634728909)
                ·
                  refine ⟨8341562152803830113023341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22244165740810213634728909 8341562152803830113023341)
                  ·
                    refine ⟨3128085807301436292383753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8341562152803830113023341 3128085807301436292383753)
                    ·
                      refine ⟨2346064355476077219287815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3128085807301436292383753 2346064355476077219287815)
                      ·
                        rfl

theorem cell23_4568944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 4, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 4, 3, 3, 2].length) (baseStart_4568944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4568944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4568944 prefixEnd_4568944 := by exact prefixLift 4568944
  have htrace : WordTrace (prefixWord ++ tailWord_4568944) baseStart_4568944 baseEnd_4568944 := by
    simpa [prefixWord, tailWord_4568944, baseEnd_4568944] using wordTrace_append hprefix tailTrace_4568944
  have hstable : (prefixWord ++ tailWord_4568944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4568944).length < 2 ^ (prefixWord ++ tailWord_4568944).sum := by decide
  have hdescent : baseEnd_4568944 < baseStart_4568944 := by decide
  rcases family_descends (prefixWord ++ tailWord_4568944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4568977 : List Nat := [1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 5]
def baseStart_4568977 : Nat := 118140960795 + 4568977 * 2 ^ 59
def prefixEnd_4568977 : Nat := 4983230072969 + 3 ^ 40 * 4568977 * 2
def baseEnd_4568977 : Nat := 2346081300337675590175163

theorem tailTrace_4568977 : CollatzResearch.WordTrace tailWord_4568977 prefixEnd_4568977 2346081300337675590175163 := by
  unfold tailWord_4568977
  simp only [CollatzResearch.WordTrace]
  refine ⟨166644281568384122992329185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111096187712256081994886123 166644281568384122992329185)
  ·
    refine ⟨124983211176288092244246889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 166644281568384122992329185 124983211176288092244246889)
    ·
      refine ⟨93737408382216069183185167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 124983211176288092244246889 93737408382216069183185167)
      ·
        refine ⟨140606112573324103774777751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93737408382216069183185167 140606112573324103774777751)
        ·
          refine ⟨210909168859986155662166627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 140606112573324103774777751 210909168859986155662166627)
          ·
            refine ⟨316363753289979233493249941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 210909168859986155662166627 316363753289979233493249941)
            ·
              refine ⟨14829550935467776569996091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 316363753289979233493249941 14829550935467776569996091)
              ·
                refine ⟨22244326403201664854994137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14829550935467776569996091 22244326403201664854994137)
                ·
                  refine ⟨16683244802401248641245603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22244326403201664854994137 16683244802401248641245603)
                  ·
                    refine ⟨25024867203601872961868405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16683244802401248641245603 25024867203601872961868405)
                    ·
                      refine ⟨2346081300337675590175163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25024867203601872961868405 2346081300337675590175163)
                      ·
                        rfl

theorem cell23_4568977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 5].length) (baseStart_4568977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4568977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4568977 prefixEnd_4568977 := by exact prefixLift 4568977
  have htrace : WordTrace (prefixWord ++ tailWord_4568977) baseStart_4568977 baseEnd_4568977 := by
    simpa [prefixWord, tailWord_4568977, baseEnd_4568977] using wordTrace_append hprefix tailTrace_4568977
  have hstable : (prefixWord ++ tailWord_4568977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4568977).length < 2 ^ (prefixWord ++ tailWord_4568977).sum := by decide
  have hdescent : baseEnd_4568977 < baseStart_4568977 := by decide
  rcases family_descends (prefixWord ++ tailWord_4568977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4569042 : List Nat := [3, 2, 2, 3, 2, 2, 1, 2, 2, 2, 2]
def baseStart_4569042 : Nat := 118140960795 + 4569042 * 2 ^ 59
def prefixEnd_4569042 : Nat := 4983230072969 + 3 ^ 40 * 4569042 * 2
def baseEnd_4569042 : Nat := 2346114676580217835862365

theorem tailTrace_4569042 : CollatzResearch.WordTrace tailWord_4569042 prefixEnd_4569042 2346114676580217835862365 := by
  unfold tailWord_4569042
  simp only [CollatzResearch.WordTrace]
  refine ⟨41661663078287159773361345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 111097768208765759395630253 41661663078287159773361345)
  ·
    refine ⟨31246247308715369830021009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41661663078287159773361345 31246247308715369830021009)
    ·
      refine ⟨23434685481536527372515757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31246247308715369830021009 23434685481536527372515757)
      ·
        refine ⟨8788007055576197764693409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23434685481536527372515757 8788007055576197764693409)
        ·
          refine ⟨6591005291682148323520057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8788007055576197764693409 6591005291682148323520057)
          ·
            refine ⟨4943253968761611242640043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6591005291682148323520057 4943253968761611242640043)
            ·
              refine ⟨7414880953142416863960065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4943253968761611242640043 7414880953142416863960065)
              ·
                refine ⟨5561160714856812647970049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7414880953142416863960065 5561160714856812647970049)
                ·
                  refine ⟨4170870536142609485977537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5561160714856812647970049 4170870536142609485977537)
                  ·
                    refine ⟨3128152902106957114483153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4170870536142609485977537 3128152902106957114483153)
                    ·
                      refine ⟨2346114676580217835862365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3128152902106957114483153 2346114676580217835862365)
                      ·
                        rfl

theorem cell23_4569042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 2, 1, 2, 2, 2, 2].length) (baseStart_4569042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4569042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4569042 prefixEnd_4569042 := by exact prefixLift 4569042
  have htrace : WordTrace (prefixWord ++ tailWord_4569042) baseStart_4569042 baseEnd_4569042 := by
    simpa [prefixWord, tailWord_4569042, baseEnd_4569042] using wordTrace_append hprefix tailTrace_4569042
  have hstable : (prefixWord ++ tailWord_4569042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4569042).length < 2 ^ (prefixWord ++ tailWord_4569042).sum := by decide
  have hdescent : baseEnd_4569042 < baseStart_4569042 := by decide
  rcases family_descends (prefixWord ++ tailWord_4569042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4569044 : List Nat := [2, 4, 1, 2, 1, 1, 2, 1, 4, 5]
def baseStart_4569044 : Nat := 118140960795 + 4569044 * 2 ^ 59
def prefixEnd_4569044 : Nat := 4983230072969 + 3 ^ 40 * 4569044 * 2
def baseEnd_4569044 : Nat := 782038567847175609345785

theorem tailTrace_4569044 : CollatzResearch.WordTrace tailWord_4569044 prefixEnd_4569044 782038567847175609345785 := by
  unfold tailWord_4569044
  simp only [CollatzResearch.WordTrace]
  refine ⟨83323362629570696717509093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111097816839427595623345457 83323362629570696717509093)
  ·
    refine ⟨15623130493044505634532955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 83323362629570696717509093 15623130493044505634532955)
    ·
      refine ⟨23434695739566758451799433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15623130493044505634532955 23434695739566758451799433)
      ·
        refine ⟨17576021804675068838849575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23434695739566758451799433 17576021804675068838849575)
        ·
          refine ⟨26364032707012603258274363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17576021804675068838849575 26364032707012603258274363)
          ·
            refine ⟨39546049060518904887411545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26364032707012603258274363 39546049060518904887411545)
            ·
              refine ⟨29659536795389178665558659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39546049060518904887411545 29659536795389178665558659)
              ·
                refine ⟨44489305193083767998337989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29659536795389178665558659 44489305193083767998337989)
                ·
                  refine ⟨8341744723703206499688373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 44489305193083767998337989 8341744723703206499688373)
                  ·
                    refine ⟨782038567847175609345785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8341744723703206499688373 782038567847175609345785)
                    ·
                      rfl

theorem cell23_4569044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 2, 1, 4, 5].length) (baseStart_4569044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4569044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4569044 prefixEnd_4569044 := by exact prefixLift 4569044
  have htrace : WordTrace (prefixWord ++ tailWord_4569044) baseStart_4569044 baseEnd_4569044 := by
    simpa [prefixWord, tailWord_4569044, baseEnd_4569044] using wordTrace_append hprefix tailTrace_4569044
  have hstable : (prefixWord ++ tailWord_4569044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4569044).length < 2 ^ (prefixWord ++ tailWord_4569044).sum := by decide
  have hdescent : baseEnd_4569044 < baseStart_4569044 := by decide
  rcases family_descends (prefixWord ++ tailWord_4569044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4569084 : List Nat := [2, 2, 2, 1, 2, 2, 1, 3, 1, 4, 3]
def baseStart_4569084 : Nat := 118140960795 + 4569084 * 2 ^ 59
def prefixEnd_4569084 : Nat := 4983230072969 + 3 ^ 40 * 4569084 * 2
def baseEnd_4569084 : Nat := 2346136242767706671537171

theorem tailTrace_4569084 : CollatzResearch.WordTrace tailWord_4569084 prefixEnd_4569084 2346136242767706671537171 := by
  unfold tailWord_4569084
  simp only [CollatzResearch.WordTrace]
  refine ⟨83324092089498240133237153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111098789452664320177649537 83324092089498240133237153)
  ·
    refine ⟨62493069067123680099927865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83324092089498240133237153 62493069067123680099927865)
    ·
      refine ⟨46869801800342760074945899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62493069067123680099927865 46869801800342760074945899)
      ·
        refine ⟨70304702700514140112418849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46869801800342760074945899 70304702700514140112418849)
        ·
          refine ⟨52728527025385605084314137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 70304702700514140112418849 52728527025385605084314137)
          ·
            refine ⟨39546395269039203813235603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52728527025385605084314137 39546395269039203813235603)
            ·
              refine ⟨59319592903558805719853405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39546395269039203813235603 59319592903558805719853405)
              ·
                refine ⟨22244847338834552144945027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 59319592903558805719853405 22244847338834552144945027)
                ·
                  refine ⟨33367271008251828217417541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22244847338834552144945027 33367271008251828217417541)
                  ·
                    refine ⟨6256363314047217790765789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 33367271008251828217417541 6256363314047217790765789)
                    ·
                      refine ⟨2346136242767706671537171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6256363314047217790765789 2346136242767706671537171)
                      ·
                        rfl

theorem cell23_4569084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 1, 3, 1, 4, 3].length) (baseStart_4569084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4569084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4569084 prefixEnd_4569084 := by exact prefixLift 4569084
  have htrace : WordTrace (prefixWord ++ tailWord_4569084) baseStart_4569084 baseEnd_4569084 := by
    simpa [prefixWord, tailWord_4569084, baseEnd_4569084] using wordTrace_append hprefix tailTrace_4569084
  have hstable : (prefixWord ++ tailWord_4569084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4569084).length < 2 ^ (prefixWord ++ tailWord_4569084).sum := by decide
  have hdescent : baseEnd_4569084 < baseStart_4569084 := by decide
  rcases family_descends (prefixWord ++ tailWord_4569084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4569107 : List Nat := [1, 1, 1, 2, 1, 4, 2, 1, 1, 1, 8]
def baseStart_4569107 : Nat := 118140960795 + 4569107 * 2 ^ 59
def prefixEnd_4569107 : Nat := 4983230072969 + 3 ^ 40 * 4569107 * 2
def baseEnd_4569107 : Nat := 2346148052822760081549565

theorem tailTrace_4569107 : CollatzResearch.WordTrace tailWord_4569107 prefixEnd_4569107 2346148052822760081549565 := by
  unfold tailWord_4569107
  simp only [CollatzResearch.WordTrace]
  refine ⟨166649023057913155194561575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111099348705275436796374383 166649023057913155194561575)
  ·
    refine ⟨249973534586869732791842363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 166649023057913155194561575 249973534586869732791842363)
    ·
      refine ⟨374960301880304599187763545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 249973534586869732791842363 374960301880304599187763545)
      ·
        refine ⟨281220226410228449390822659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 374960301880304599187763545 281220226410228449390822659)
        ·
          refine ⟨421830339615342674086233989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 281220226410228449390822659 421830339615342674086233989)
          ·
            refine ⟨79093188677876751391168873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 421830339615342674086233989 79093188677876751391168873)
            ·
              refine ⟨59319891508407563543376655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 79093188677876751391168873 59319891508407563543376655)
              ·
                refine ⟨88979837262611345315064983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 59319891508407563543376655 88979837262611345315064983)
                ·
                  refine ⟨133469755893917017972597475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 88979837262611345315064983 133469755893917017972597475)
                  ·
                    refine ⟨200204633840875526958896213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 133469755893917017972597475 200204633840875526958896213)
                    ·
                      refine ⟨2346148052822760081549565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 200204633840875526958896213 2346148052822760081549565)
                      ·
                        rfl

theorem cell23_4569107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 2, 1, 1, 1, 8].length) (baseStart_4569107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4569107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4569107 prefixEnd_4569107 := by exact prefixLift 4569107
  have htrace : WordTrace (prefixWord ++ tailWord_4569107) baseStart_4569107 baseEnd_4569107 := by
    simpa [prefixWord, tailWord_4569107, baseEnd_4569107] using wordTrace_append hprefix tailTrace_4569107
  have hstable : (prefixWord ++ tailWord_4569107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4569107).length < 2 ^ (prefixWord ++ tailWord_4569107).sum := by decide
  have hdescent : baseEnd_4569107 < baseStart_4569107 := by decide
  rcases family_descends (prefixWord ++ tailWord_4569107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4569121 : List Nat := [1, 2, 3, 2, 4, 1, 1, 3, 6]
def baseStart_4569121 : Nat := 118140960795 + 4569121 * 2 ^ 59
def prefixEnd_4569121 : Nat := 4983230072969 + 3 ^ 40 * 4569121 * 2
def baseEnd_4569121 : Nat := 260683915727991447419389

theorem tailTrace_4569121 : CollatzResearch.WordTrace tailWord_4569121 prefixEnd_4569121 260683915727991447419389 := by
  unfold tailWord_4569121
  simp only [CollatzResearch.WordTrace]
  refine ⟨166649533679862435585571217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111099689119908290390380811 166649533679862435585571217)
  ·
    refine ⟨124987150259896826689178413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 166649533679862435585571217 124987150259896826689178413)
    ·
      refine ⟨46870181347461310008441905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 124987150259896826689178413 46870181347461310008441905)
      ·
        refine ⟨35152636010595982506331429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46870181347461310008441905 35152636010595982506331429)
        ·
          refine ⟨6591119251986746719937143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 35152636010595982506331429 6591119251986746719937143)
          ·
            refine ⟨9886678877980120079905715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6591119251986746719937143 9886678877980120079905715)
            ·
              refine ⟨14830018316970180119858573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9886678877980120079905715 14830018316970180119858573)
              ·
                refine ⟨5561256868863817544946965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14830018316970180119858573 5561256868863817544946965)
                ·
                  refine ⟨260683915727991447419389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5561256868863817544946965 260683915727991447419389)
                  ·
                    rfl

theorem cell23_4569121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 1, 1, 3, 6].length) (baseStart_4569121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4569121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4569121 prefixEnd_4569121 := by exact prefixLift 4569121
  have htrace : WordTrace (prefixWord ++ tailWord_4569121) baseStart_4569121 baseEnd_4569121 := by
    simpa [prefixWord, tailWord_4569121, baseEnd_4569121] using wordTrace_append hprefix tailTrace_4569121
  have hstable : (prefixWord ++ tailWord_4569121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4569121).length < 2 ^ (prefixWord ++ tailWord_4569121).sum := by decide
  have hdescent : baseEnd_4569121 < baseStart_4569121 := by decide
  rcases family_descends (prefixWord ++ tailWord_4569121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4569141 : List Nat := [1, 3, 3, 1, 1, 1, 2, 3, 1, 5, 2]
def baseStart_4569141 : Nat := 118140960795 + 4569141 * 2 ^ 59
def prefixEnd_4569141 : Nat := 4983230072969 + 3 ^ 40 * 4569141 * 2
def baseEnd_4569141 : Nat := 2346165511165012948524409

theorem tailTrace_4569141 : CollatzResearch.WordTrace tailWord_4569141 prefixEnd_4569141 2346165511165012948524409 := by
  unfold tailWord_4569141
  simp only [CollatzResearch.WordTrace]
  refine ⟨166650263139789979001299277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111100175426526652667532851 166650263139789979001299277)
  ·
    refine ⟨62493848677421242125487229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 166650263139789979001299277 62493848677421242125487229)
    ·
      refine ⟨23435193254032965797057711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 62493848677421242125487229 23435193254032965797057711)
      ·
        refine ⟨35152789881049448695586567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23435193254032965797057711 35152789881049448695586567)
        ·
          refine ⟨52729184821574173043379851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35152789881049448695586567 52729184821574173043379851)
          ·
            refine ⟨79093777232361259565069777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52729184821574173043379851 79093777232361259565069777)
            ·
              refine ⟨59320332924270944673802333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 79093777232361259565069777 59320332924270944673802333)
              ·
                refine ⟨22245124846601604252675875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 59320332924270944673802333 22245124846601604252675875)
                ·
                  refine ⟨33367687269902406379013813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22245124846601604252675875 33367687269902406379013813)
                  ·
                    refine ⟨3128220681553350598032545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 33367687269902406379013813 3128220681553350598032545)
                    ·
                      refine ⟨2346165511165012948524409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3128220681553350598032545 2346165511165012948524409)
                      ·
                        rfl

theorem cell23_4569141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 2, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 2, 3, 1, 5, 2].length) (baseStart_4569141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4569141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4569141 prefixEnd_4569141 := by exact prefixLift 4569141
  have htrace : WordTrace (prefixWord ++ tailWord_4569141) baseStart_4569141 baseEnd_4569141 := by
    simpa [prefixWord, tailWord_4569141, baseEnd_4569141] using wordTrace_append hprefix tailTrace_4569141
  have hstable : (prefixWord ++ tailWord_4569141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4569141).length < 2 ^ (prefixWord ++ tailWord_4569141).sum := by decide
  have hdescent : baseEnd_4569141 < baseStart_4569141 := by decide
  rcases family_descends (prefixWord ++ tailWord_4569141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4569188 : List Nat := [2, 3, 1, 1, 2, 1, 3, 1, 5, 2, 2]
def baseStart_4569188 : Nat := 118140960795 + 4569188 * 2 ^ 59
def prefixEnd_4569188 : Nat := 4983230072969 + 3 ^ 40 * 4569188 * 2
def baseEnd_4569188 : Nat := 2346189644755774264636693

theorem tailTrace_4569188 : CollatzResearch.WordTrace tailWord_4569188 prefixEnd_4569188 2346189644755774264636693 := by
  unfold tailWord_4569188
  simp only [CollatzResearch.WordTrace]
  refine ⟨83325988685309853014130109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111101318247079804018840145 83325988685309853014130109)
  ·
    refine ⟨31247245756991194880298791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 83325988685309853014130109 31247245756991194880298791)
    ·
      refine ⟨46870868635486792320448187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31247245756991194880298791 46870868635486792320448187)
      ·
        refine ⟨70306302953230188480672281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46870868635486792320448187 70306302953230188480672281)
        ·
          refine ⟨52729727214922641360504211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 70306302953230188480672281 52729727214922641360504211)
          ·
            refine ⟨79094590822383962040756317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52729727214922641360504211 79094590822383962040756317)
            ·
              refine ⟨29660471558393985765283619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 79094590822383962040756317 29660471558393985765283619)
              ·
                refine ⟨44490707337590978647925429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29660471558393985765283619 44490707337590978647925429)
                ·
                  refine ⟨4171003812899154248243009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 44490707337590978647925429 4171003812899154248243009)
                  ·
                    refine ⟨3128252859674365686182257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4171003812899154248243009 3128252859674365686182257)
                    ·
                      refine ⟨2346189644755774264636693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3128252859674365686182257 2346189644755774264636693)
                      ·
                        rfl

theorem cell23_4569188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 3, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 3, 1, 5, 2, 2].length) (baseStart_4569188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4569188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4569188 prefixEnd_4569188 := by exact prefixLift 4569188
  have htrace : WordTrace (prefixWord ++ tailWord_4569188) baseStart_4569188 baseEnd_4569188 := by
    simpa [prefixWord, tailWord_4569188, baseEnd_4569188] using wordTrace_append hprefix tailTrace_4569188
  have hstable : (prefixWord ++ tailWord_4569188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4569188).length < 2 ^ (prefixWord ++ tailWord_4569188).sum := by decide
  have hdescent : baseEnd_4569188 < baseStart_4569188 := by decide
  rcases family_descends (prefixWord ++ tailWord_4569188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4569191 : List Nat := [1, 1, 5, 1, 1, 2, 1, 3, 3, 2, 3]
def baseStart_4569191 : Nat := 118140960795 + 4569191 * 2 ^ 59
def prefixEnd_4569191 : Nat := 4983230072969 + 3 ^ 40 * 4569191 * 2
def baseEnd_4569191 : Nat := 2346191185197737752899179

theorem tailTrace_4569191 : CollatzResearch.WordTrace tailWord_4569191 prefixEnd_4569191 2346191185197737752899179 := by
  unfold tailWord_4569191
  simp only [CollatzResearch.WordTrace]
  refine ⟨166652086789608837540619427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111101391193072558360412951 166652086789608837540619427)
  ·
    refine ⟨249978130184413256310929141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 166652086789608837540619427 249978130184413256310929141)
    ·
      refine ⟨23435449704788742779149607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 249978130184413256310929141 23435449704788742779149607)
      ·
        refine ⟨35153174557183114168724411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23435449704788742779149607 35153174557183114168724411)
        ·
          refine ⟨52729761835774671253086617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35153174557183114168724411 52729761835774671253086617)
          ·
            refine ⟨39547321376831003439814963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52729761835774671253086617 39547321376831003439814963)
            ·
              refine ⟨59320982065246505159722445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39547321376831003439814963 59320982065246505159722445)
              ·
                refine ⟨22245368274467439434895917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 59320982065246505159722445 22245368274467439434895917)
                ·
                  refine ⟨8342013102925289788085969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22245368274467439434895917 8342013102925289788085969)
                  ·
                    refine ⟨6256509827193967341064477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8342013102925289788085969 6256509827193967341064477)
                    ·
                      refine ⟨2346191185197737752899179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6256509827193967341064477 2346191185197737752899179)
                      ·
                        rfl

theorem cell23_4569191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 1, 3, 3, 2, 3].length) (baseStart_4569191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4569191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4569191 prefixEnd_4569191 := by exact prefixLift 4569191
  have htrace : WordTrace (prefixWord ++ tailWord_4569191) baseStart_4569191 baseEnd_4569191 := by
    simpa [prefixWord, tailWord_4569191, baseEnd_4569191] using wordTrace_append hprefix tailTrace_4569191
  have hstable : (prefixWord ++ tailWord_4569191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4569191).length < 2 ^ (prefixWord ++ tailWord_4569191).sum := by decide
  have hdescent : baseEnd_4569191 < baseStart_4569191 := by decide
  rcases family_descends (prefixWord ++ tailWord_4569191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4569295 : List Nat := [1, 1, 2, 1, 1, 3, 5, 3, 2, 2, 2]
def baseStart_4569295 : Nat := 118140960795 + 4569295 * 2 ^ 59
def prefixEnd_4569295 : Nat := 4983230072969 + 3 ^ 40 * 4569295 * 2
def baseEnd_4569295 : Nat := 2346244587185805345998701

theorem tailTrace_4569295 : CollatzResearch.WordTrace tailWord_4569295 prefixEnd_4569295 2346244587185805345998701 := by
  unfold tailWord_4569295
  simp only [CollatzResearch.WordTrace]
  refine ⟨166655879981232063302405339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111103919987488042201603559 166655879981232063302405339)
  ·
    refine ⟨249983819971848094953608009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 166655879981232063302405339 249983819971848094953608009)
    ·
      refine ⟨187487864978886071215206007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 249983819971848094953608009 187487864978886071215206007)
      ·
        refine ⟨281231797468329106822809011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 187487864978886071215206007 281231797468329106822809011)
        ·
          refine ⟨421847696202493660234213517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 281231797468329106822809011 421847696202493660234213517)
          ·
            refine ⟨158192886075935122587830069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 421847696202493660234213517 158192886075935122587830069)
            ·
              refine ⟨14830583069618917742609069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 158192886075935122587830069 14830583069618917742609069)
              ·
                refine ⟨5561468651107094153478401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14830583069618917742609069 5561468651107094153478401)
                ·
                  refine ⟨4171101488330320615108801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5561468651107094153478401 4171101488330320615108801)
                  ·
                    refine ⟨3128326116247740461331601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4171101488330320615108801 3128326116247740461331601)
                    ·
                      refine ⟨2346244587185805345998701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3128326116247740461331601 2346244587185805345998701)
                      ·
                        rfl

theorem cell23_4569295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 5, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 5, 3, 2, 2, 2].length) (baseStart_4569295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4569295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4569295 prefixEnd_4569295 := by exact prefixLift 4569295
  have htrace : WordTrace (prefixWord ++ tailWord_4569295) baseStart_4569295 baseEnd_4569295 := by
    simpa [prefixWord, tailWord_4569295, baseEnd_4569295] using wordTrace_append hprefix tailTrace_4569295
  have hstable : (prefixWord ++ tailWord_4569295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4569295).length < 2 ^ (prefixWord ++ tailWord_4569295).sum := by decide
  have hdescent : baseEnd_4569295 < baseStart_4569295 := by decide
  rcases family_descends (prefixWord ++ tailWord_4569295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4569311 : List Nat := [1, 1, 2, 3, 2, 1, 1, 2, 4, 3, 3]
def baseStart_4569311 : Nat := 118140960795 + 4569311 * 2 ^ 59
def prefixEnd_4569311 : Nat := 4983230072969 + 3 ^ 40 * 4569311 * 2
def baseEnd_4569311 : Nat := 2346252802876277283398627

theorem tailTrace_4569311 : CollatzResearch.WordTrace tailWord_4569311 prefixEnd_4569311 2346252802876277283398627 := by
  unfold tailWord_4569311
  simp only [CollatzResearch.WordTrace]
  refine ⟨166656463549174098034987787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111104309032782732023325191 166656463549174098034987787)
  ·
    refine ⟨249984695323761147052481681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 166656463549174098034987787 249984695323761147052481681)
    ·
      refine ⟨187488521492820860289361261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 249984695323761147052481681 187488521492820860289361261)
      ·
        refine ⟨70308195559807822608510473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 187488521492820860289361261 70308195559807822608510473)
        ·
          refine ⟨52731146669855866956382855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 70308195559807822608510473 52731146669855866956382855)
          ·
            refine ⟨79096720004783800434574283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52731146669855866956382855 79096720004783800434574283)
            ·
              refine ⟨118645080007175700651861425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 79096720004783800434574283 118645080007175700651861425)
              ·
                refine ⟨88983810005381775488896069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 118645080007175700651861425 88983810005381775488896069)
                ·
                  refine ⟨16684464376009082904168013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 88983810005381775488896069 16684464376009082904168013)
                  ·
                    refine ⟨6256674141003406089063005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16684464376009082904168013 6256674141003406089063005)
                    ·
                      refine ⟨2346252802876277283398627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6256674141003406089063005 2346252802876277283398627)
                      ·
                        rfl

theorem cell23_4569311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 2, 4, 3, 3].length) (baseStart_4569311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4569311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4569311 prefixEnd_4569311 := by exact prefixLift 4569311
  have htrace : WordTrace (prefixWord ++ tailWord_4569311) baseStart_4569311 baseEnd_4569311 := by
    simpa [prefixWord, tailWord_4569311, baseEnd_4569311] using wordTrace_append hprefix tailTrace_4569311
  have hstable : (prefixWord ++ tailWord_4569311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4569311).length < 2 ^ (prefixWord ++ tailWord_4569311).sum := by decide
  have hdescent : baseEnd_4569311 < baseStart_4569311 := by decide
  rcases family_descends (prefixWord ++ tailWord_4569311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4569331 : List Nat := [1, 1, 1, 2, 2, 4, 1, 4, 2, 5]
def baseStart_4569331 : Nat := 118140960795 + 4569331 * 2 ^ 59
def prefixEnd_4569331 : Nat := 4983230072969 + 3 ^ 40 * 4569331 * 2
def baseEnd_4569331 : Nat := 782087690829789068382845

theorem tailTrace_4569331 : CollatzResearch.WordTrace tailWord_4569331 prefixEnd_4569331 782087690829789068382845 := by
  unfold tailWord_4569331
  simp only [CollatzResearch.WordTrace]
  refine ⟨166657193009101641450715847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111104795339401094300477231 166657193009101641450715847)
  ·
    refine ⟨249985789513652462176073771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 166657193009101641450715847 249985789513652462176073771)
    ·
      refine ⟨374978684270478693264110657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 249985789513652462176073771 374978684270478693264110657)
      ·
        refine ⟨281234013202859019948082993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 374978684270478693264110657 281234013202859019948082993)
        ·
          refine ⟨210925509902144264961062245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 281234013202859019948082993 210925509902144264961062245)
          ·
            refine ⟨39548533106652049680199171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 210925509902144264961062245 39548533106652049680199171)
            ·
              refine ⟨59322799659978074520298757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39548533106652049680199171 59322799659978074520298757)
              ·
                refine ⟨11123024936245888972556017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 59322799659978074520298757 11123024936245888972556017)
                ·
                  refine ⟨8342268702184416729417013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11123024936245888972556017 8342268702184416729417013)
                  ·
                    refine ⟨782087690829789068382845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8342268702184416729417013 782087690829789068382845)
                    ·
                      rfl

theorem cell23_4569331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 1, 4, 2, 5].length) (baseStart_4569331 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4569331 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4569331 prefixEnd_4569331 := by exact prefixLift 4569331
  have htrace : WordTrace (prefixWord ++ tailWord_4569331) baseStart_4569331 baseEnd_4569331 := by
    simpa [prefixWord, tailWord_4569331, baseEnd_4569331] using wordTrace_append hprefix tailTrace_4569331
  have hstable : (prefixWord ++ tailWord_4569331).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4569331).length < 2 ^ (prefixWord ++ tailWord_4569331).sum := by decide
  have hdescent : baseEnd_4569331 < baseStart_4569331 := by decide
  rcases family_descends (prefixWord ++ tailWord_4569331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4569338 : List Nat := [3, 1, 1, 1, 1, 5, 1, 1, 2, 5, 2]
def baseStart_4569338 : Nat := 118140960795 + 4569338 * 2 ^ 59
def prefixEnd_4569338 : Nat := 4983230072969 + 3 ^ 40 * 4569338 * 2
def baseEnd_4569338 : Nat := 2346266666853948677761003

theorem tailTrace_4569338 : CollatzResearch.WordTrace tailWord_4569338 prefixEnd_4569338 2346266666853948677761003 := by
  unfold tailWord_4569338
  simp only [CollatzResearch.WordTrace]
  refine ⟨41664362080019070411555167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 111104965546717521097480445 41664362080019070411555167)
  ·
    refine ⟨62496543120028605617332751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41664362080019070411555167 62496543120028605617332751)
    ·
      refine ⟨93744814680042908425999127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62496543120028605617332751 93744814680042908425999127)
      ·
        refine ⟨140617222020064362638998691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93744814680042908425999127 140617222020064362638998691)
        ·
          refine ⟨210925833030096543958498037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 140617222020064362638998691 210925833030096543958498037)
          ·
            refine ⟨19774296846571550996109191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 210925833030096543958498037 19774296846571550996109191)
            ·
              refine ⟨29661445269857326494163787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19774296846571550996109191 29661445269857326494163787)
              ·
                refine ⟨44492167904785989741245681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29661445269857326494163787 44492167904785989741245681)
                ·
                  refine ⟨33369125928589492305934261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 44492167904785989741245681 33369125928589492305934261)
                  ·
                    refine ⟨3128355555805264903681337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 33369125928589492305934261 3128355555805264903681337)
                    ·
                      refine ⟨2346266666853948677761003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3128355555805264903681337 2346266666853948677761003)
                      ·
                        rfl

theorem cell23_4569338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 1, 1, 2, 5, 2].length) (baseStart_4569338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4569338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4569338 prefixEnd_4569338 := by exact prefixLift 4569338
  have htrace : WordTrace (prefixWord ++ tailWord_4569338) baseStart_4569338 baseEnd_4569338 := by
    simpa [prefixWord, tailWord_4569338, baseEnd_4569338] using wordTrace_append hprefix tailTrace_4569338
  have hstable : (prefixWord ++ tailWord_4569338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4569338).length < 2 ^ (prefixWord ++ tailWord_4569338).sum := by decide
  have hdescent : baseEnd_4569338 < baseStart_4569338 := by decide
  rcases family_descends (prefixWord ++ tailWord_4569338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4569368 : List Nat := [2, 1, 2, 3, 1, 2, 1, 2, 1, 6, 2]
def baseStart_4569368 : Nat := 118140960795 + 4569368 * 2 ^ 59
def prefixEnd_4569368 : Nat := 4983230072969 + 3 ^ 40 * 4569368 * 2
def baseEnd_4569368 : Nat := 2346282071273583560385865

theorem tailTrace_4569368 : CollatzResearch.WordTrace tailWord_4569368 prefixEnd_4569368 2346282071273583560385865 := by
  unfold tailWord_4569368
  simp only [CollatzResearch.WordTrace]
  refine ⟨83329271254983798384906379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111105695006645064513208505 83329271254983798384906379)
  ·
    refine ⟨124993906882475697577359569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83329271254983798384906379 124993906882475697577359569)
    ·
      refine ⟨93745430161856773183019677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 124993906882475697577359569 93745430161856773183019677)
      ·
        refine ⟨35154536310696289943632379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 93745430161856773183019677 35154536310696289943632379)
        ·
          refine ⟨52731804466044434915448569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35154536310696289943632379 52731804466044434915448569)
          ·
            refine ⟨39548853349533326186586427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52731804466044434915448569 39548853349533326186586427)
            ·
              refine ⟨59323280024299989279879641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39548853349533326186586427 59323280024299989279879641)
              ·
                refine ⟨44492460018224991959909731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 59323280024299989279879641 44492460018224991959909731)
                ·
                  refine ⟨66738690027337487939864597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 44492460018224991959909731 66738690027337487939864597)
                  ·
                    refine ⟨3128376095031444747181153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 66738690027337487939864597 3128376095031444747181153)
                    ·
                      refine ⟨2346282071273583560385865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3128376095031444747181153 2346282071273583560385865)
                      ·
                        rfl

theorem cell23_4569368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 1, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 1, 2, 1, 6, 2].length) (baseStart_4569368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4569368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4569368 prefixEnd_4569368 := by exact prefixLift 4569368
  have htrace : WordTrace (prefixWord ++ tailWord_4569368) baseStart_4569368 baseEnd_4569368 := by
    simpa [prefixWord, tailWord_4569368, baseEnd_4569368] using wordTrace_append hprefix tailTrace_4569368
  have hstable : (prefixWord ++ tailWord_4569368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4569368).length < 2 ^ (prefixWord ++ tailWord_4569368).sum := by decide
  have hdescent : baseEnd_4569368 < baseStart_4569368 := by decide
  rcases family_descends (prefixWord ++ tailWord_4569368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4569388 : List Nat := [2, 2, 1, 1, 1, 3, 2, 4, 2, 2, 3]
def baseStart_4569388 : Nat := 118140960795 + 4569388 * 2 ^ 59
def prefixEnd_4569388 : Nat := 4983230072969 + 3 ^ 40 * 4569388 * 2
def baseEnd_4569388 : Nat := 2346292340886673482135773

theorem tailTrace_4569388 : CollatzResearch.WordTrace tailWord_4569388 prefixEnd_4569388 2346292340886673482135773 := by
  unfold tailWord_4569388
  simp only [CollatzResearch.WordTrace]
  refine ⟨83329635984947570092770409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111106181313263426790360545 83329635984947570092770409)
  ·
    refine ⟨62497226988710677569577807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83329635984947570092770409 62497226988710677569577807)
    ·
      refine ⟨93745840483066016354366711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62497226988710677569577807 93745840483066016354366711)
      ·
        refine ⟨140618760724599024531550067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93745840483066016354366711 140618760724599024531550067)
        ·
          refine ⟨210928141086898536797325101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 140618760724599024531550067 210928141086898536797325101)
          ·
            refine ⟨79098052907586951298996913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 210928141086898536797325101 79098052907586951298996913)
            ·
              refine ⟨59323539680690213474247685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 79098052907586951298996913 59323539680690213474247685)
              ·
                refine ⟨11123163690129415026421441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 59323539680690213474247685 11123163690129415026421441)
                ·
                  refine ⟨8342372767597061269816081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11123163690129415026421441 8342372767597061269816081)
                  ·
                    refine ⟨6256779575697795952362061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8342372767597061269816081 6256779575697795952362061)
                    ·
                      refine ⟨2346292340886673482135773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6256779575697795952362061 2346292340886673482135773)
                      ·
                        rfl

theorem cell23_4569388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 2, 3].length) (baseStart_4569388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4569388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4569388 prefixEnd_4569388 := by exact prefixLift 4569388
  have htrace : WordTrace (prefixWord ++ tailWord_4569388) baseStart_4569388 baseEnd_4569388 := by
    simpa [prefixWord, tailWord_4569388, baseEnd_4569388] using wordTrace_append hprefix tailTrace_4569388
  have hstable : (prefixWord ++ tailWord_4569388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4569388).length < 2 ^ (prefixWord ++ tailWord_4569388).sum := by decide
  have hdescent : baseEnd_4569388 < baseStart_4569388 := by decide
  rcases family_descends (prefixWord ++ tailWord_4569388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4569395 : List Nat := [1, 1, 1, 2, 5, 1, 1, 6, 1, 4]
def baseStart_4569395 : Nat := 118140960795 + 4569395 * 2 ^ 59
def prefixEnd_4569395 : Nat := 4983230072969 + 3 ^ 40 * 4569395 * 2
def baseEnd_4569395 : Nat := 782098645083751651582747

theorem tailTrace_4569395 : CollatzResearch.WordTrace tailWord_4569395 prefixEnd_4569395 782098645083751651582747 := by
  unfold tailWord_4569395
  simp only [CollatzResearch.WordTrace]
  refine ⟨166659527280869780381045639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111106351520579853587363759 166659527280869780381045639)
  ·
    refine ⟨249989290921304670571568459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 166659527280869780381045639 249989290921304670571568459)
    ·
      refine ⟨374983936381957005857352689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 249989290921304670571568459 374983936381957005857352689)
      ·
        refine ⟨281237952286467754393014517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 374983936381957005857352689 281237952286467754393014517)
        ·
          refine ⟨26366058026856351974345111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 281237952286467754393014517 26366058026856351974345111)
          ·
            refine ⟨39549087040284527961517667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26366058026856351974345111 39549087040284527961517667)
            ·
              refine ⟨59323630560426791942276501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39549087040284527961517667 59323630560426791942276501)
              ·
                refine ⟨2780795182520005872294211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 59323630560426791942276501 2780795182520005872294211)
                ·
                  refine ⟨4171192773780008808441317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2780795182520005872294211 4171192773780008808441317)
                  ·
                    refine ⟨782098645083751651582747, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4171192773780008808441317 782098645083751651582747)
                    ·
                      rfl

theorem cell23_4569395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 1, 6, 1, 4].length) (baseStart_4569395 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4569395 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4569395 prefixEnd_4569395 := by exact prefixLift 4569395
  have htrace : WordTrace (prefixWord ++ tailWord_4569395) baseStart_4569395 baseEnd_4569395 := by
    simpa [prefixWord, tailWord_4569395, baseEnd_4569395] using wordTrace_append hprefix tailTrace_4569395
  have hstable : (prefixWord ++ tailWord_4569395).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4569395).length < 2 ^ (prefixWord ++ tailWord_4569395).sum := by decide
  have hdescent : baseEnd_4569395 < baseStart_4569395 := by decide
  rcases family_descends (prefixWord ++ tailWord_4569395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4569429 : List Nat := [1, 3, 2, 2, 4, 2, 1, 3, 1, 4]
def baseStart_4569429 : Nat := 118140960795 + 4569429 * 2 ^ 59
def prefixEnd_4569429 : Nat := 4983230072969 + 3 ^ 40 * 4569429 * 2
def baseEnd_4569429 : Nat := 782104464531169273907695

theorem tailTrace_4569429 : CollatzResearch.WordTrace tailWord_4569429 prefixEnd_4569429 782104464531169273907695 := by
  unfold tailWord_4569429
  simp only [CollatzResearch.WordTrace]
  refine ⟨166660767362746604187783341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111107178241831069458522227 166660767362746604187783341)
  ·
    refine ⟨62497787761029976570418753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 166660767362746604187783341 62497787761029976570418753)
    ·
      refine ⟨46873340820772482427814065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62497787761029976570418753 46873340820772482427814065)
      ·
        refine ⟨35155005615579361820860549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46873340820772482427814065 35155005615579361820860549)
        ·
          refine ⟨6591563552921130341411353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 35155005615579361820860549 6591563552921130341411353)
          ·
            refine ⟨4943672664690847756058515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6591563552921130341411353 4943672664690847756058515)
            ·
              refine ⟨7415508997036271634087773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4943672664690847756058515 7415508997036271634087773)
              ·
                refine ⟨2780815873888601862782915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7415508997036271634087773 2780815873888601862782915)
                ·
                  refine ⟨4171223810832902794174373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2780815873888601862782915 4171223810832902794174373)
                  ·
                    refine ⟨782104464531169273907695, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4171223810832902794174373 782104464531169273907695)
                    ·
                      rfl

theorem cell23_4569429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 2, 1, 3, 1, 4].length) (baseStart_4569429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4569429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4569429 prefixEnd_4569429 := by exact prefixLift 4569429
  have htrace : WordTrace (prefixWord ++ tailWord_4569429) baseStart_4569429 baseEnd_4569429 := by
    simpa [prefixWord, tailWord_4569429, baseEnd_4569429] using wordTrace_append hprefix tailTrace_4569429
  have hstable : (prefixWord ++ tailWord_4569429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4569429).length < 2 ^ (prefixWord ++ tailWord_4569429).sum := by decide
  have hdescent : baseEnd_4569429 < baseStart_4569429 := by decide
  rcases family_descends (prefixWord ++ tailWord_4569429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4569445 : List Nat := [1, 3, 1, 3, 1, 3, 1, 1, 4, 3, 2]
def baseStart_4569445 : Nat := 118140960795 + 4569445 * 2 ^ 59
def prefixEnd_4569445 : Nat := 4983230072969 + 3 ^ 40 * 4569445 * 2
def baseEnd_4569445 : Nat := 2346321609283979759123011

theorem tailTrace_4569445 : CollatzResearch.WordTrace tailWord_4569445 prefixEnd_4569445 2346321609283979759123011 := by
  unfold tailWord_4569445
  simp only [CollatzResearch.WordTrace]
  refine ⟨166661350930688638920365789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111107567287125759280243859 166661350930688638920365789)
  ·
    refine ⟨62498006599008239595137171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 166661350930688638920365789 62498006599008239595137171)
    ·
      refine ⟨93747009898512359392705757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62498006599008239595137171 93747009898512359392705757)
      ·
        refine ⟨35155128711942134772264659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 93747009898512359392705757 35155128711942134772264659)
        ·
          refine ⟨52732693067913202158396989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35155128711942134772264659 52732693067913202158396989)
          ·
            refine ⟨19774759900467450809398871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 52732693067913202158396989 19774759900467450809398871)
            ·
              refine ⟨29662139850701176214098307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19774759900467450809398871 29662139850701176214098307)
              ·
                refine ⟨44493209776051764321147461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29662139850701176214098307 44493209776051764321147461)
                ·
                  refine ⟨8342476833009705810215149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 44493209776051764321147461 8342476833009705810215149)
                  ·
                    refine ⟨3128428812378639678830681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8342476833009705810215149 3128428812378639678830681)
                    ·
                      refine ⟨2346321609283979759123011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3128428812378639678830681 2346321609283979759123011)
                      ·
                        rfl

theorem cell23_4569445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 1, 1, 4, 3, 2].length) (baseStart_4569445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4569445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4569445 prefixEnd_4569445 := by exact prefixLift 4569445
  have htrace : WordTrace (prefixWord ++ tailWord_4569445) baseStart_4569445 baseEnd_4569445 := by
    simpa [prefixWord, tailWord_4569445, baseEnd_4569445] using wordTrace_append hprefix tailTrace_4569445
  have hstable : (prefixWord ++ tailWord_4569445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4569445).length < 2 ^ (prefixWord ++ tailWord_4569445).sum := by decide
  have hdescent : baseEnd_4569445 < baseStart_4569445 := by decide
  rcases family_descends (prefixWord ++ tailWord_4569445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4569451 : List Nat := [1, 1, 1, 1, 2, 2, 2, 4, 3, 6]
def baseStart_4569451 : Nat := 118140960795 + 4569451 * 2 ^ 59
def prefixEnd_4569451 : Nat := 4983230072969 + 3 ^ 40 * 4569451 * 2
def baseEnd_4569451 : Nat := 782108230055968911882661

theorem tailTrace_4569451 : CollatzResearch.WordTrace tailWord_4569451 prefixEnd_4569451 782108230055968911882661 := by
  unfold tailWord_4569451
  simp only [CollatzResearch.WordTrace]
  refine ⟨166661569768666901945084207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111107713179111267963389471 166661569768666901945084207)
  ·
    refine ⟨249992354653000352917626311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 166661569768666901945084207 249992354653000352917626311)
    ·
      refine ⟨374988531979500529376439467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 249992354653000352917626311 374988531979500529376439467)
      ·
        refine ⟨562482797969250794064659201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 374988531979500529376439467 562482797969250794064659201)
        ·
          refine ⟨421862098476938095548494401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 562482797969250794064659201 421862098476938095548494401)
          ·
            refine ⟨316396573857703571661370801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 421862098476938095548494401 316396573857703571661370801)
            ·
              refine ⟨237297430393277678746028101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 316396573857703571661370801 237297430393277678746028101)
              ·
                refine ⟨44493268198739564764880269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 237297430393277678746028101 44493268198739564764880269)
                ·
                  refine ⟨16684975574527336786830101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 44493268198739564764880269 16684975574527336786830101)
                  ·
                    refine ⟨782108230055968911882661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16684975574527336786830101 782108230055968911882661)
                    ·
                      rfl

theorem cell23_4569451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 4, 3, 6].length) (baseStart_4569451 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4569451 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4569451 prefixEnd_4569451 := by exact prefixLift 4569451
  have htrace : WordTrace (prefixWord ++ tailWord_4569451) baseStart_4569451 baseEnd_4569451 := by
    simpa [prefixWord, tailWord_4569451, baseEnd_4569451] using wordTrace_append hprefix tailTrace_4569451
  have hstable : (prefixWord ++ tailWord_4569451).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4569451).length < 2 ^ (prefixWord ++ tailWord_4569451).sum := by decide
  have hdescent : baseEnd_4569451 < baseStart_4569451 := by decide
  rcases family_descends (prefixWord ++ tailWord_4569451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4569468 : List Nat := [2, 2, 2, 1, 1, 1, 2, 2, 6, 4]
def baseStart_4569468 : Nat := 118140960795 + 4569468 * 2 ^ 59
def prefixEnd_4569468 : Nat := 4983230072969 + 3 ^ 40 * 4569468 * 2
def baseEnd_4569468 : Nat := 782111139779677723045135

theorem tailTrace_4569468 : CollatzResearch.WordTrace tailWord_4569468 prefixEnd_4569468 782111139779677723045135 := by
  unfold tailWord_4569468
  simp only [CollatzResearch.WordTrace]
  refine ⟨83331094904802656924226529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111108126539736875898968705 83331094904802656924226529)
  ·
    refine ⟨62498321178601992693169897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83331094904802656924226529 62498321178601992693169897)
    ·
      refine ⟨46873740883951494519877423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62498321178601992693169897 46873740883951494519877423)
      ·
        refine ⟨70310611325927241779816135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46873740883951494519877423 70310611325927241779816135)
        ·
          refine ⟨105465916988890862669724203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70310611325927241779816135 105465916988890862669724203)
          ·
            refine ⟨158198875483336294004586305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 105465916988890862669724203 158198875483336294004586305)
            ·
              refine ⟨118649156612502220503439729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 158198875483336294004586305 118649156612502220503439729)
              ·
                refine ⟨88986867459376665377579797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 118649156612502220503439729 88986867459376665377579797)
                ·
                  refine ⟨4171259412158281189574053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 88986867459376665377579797 4171259412158281189574053)
                  ·
                    refine ⟨782111139779677723045135, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4171259412158281189574053 782111139779677723045135)
                    ·
                      rfl

theorem cell23_4569468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 2, 6, 4].length) (baseStart_4569468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4569468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4569468 prefixEnd_4569468 := by exact prefixLift 4569468
  have htrace : WordTrace (prefixWord ++ tailWord_4569468) baseStart_4569468 baseEnd_4569468 := by
    simpa [prefixWord, tailWord_4569468, baseEnd_4569468] using wordTrace_append hprefix tailTrace_4569468
  have hstable : (prefixWord ++ tailWord_4569468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4569468).length < 2 ^ (prefixWord ++ tailWord_4569468).sum := by decide
  have hdescent : baseEnd_4569468 < baseStart_4569468 := by decide
  rcases family_descends (prefixWord ++ tailWord_4569468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4569475 : List Nat := [1, 1, 1, 3, 6, 1, 1, 1, 3, 1, 4]
def baseStart_4569475 : Nat := 118140960795 + 4569475 * 2 ^ 59
def prefixEnd_4569475 : Nat := 4983230072969 + 3 ^ 40 * 4569475 * 2
def baseEnd_4569475 : Nat := 2346337013703614641747873

theorem tailTrace_4569475 : CollatzResearch.WordTrace tailWord_4569475 prefixEnd_4569475 2346337013703614641747873 := by
  unfold tailWord_4569475
  simp only [CollatzResearch.WordTrace]
  refine ⟨166662445120579954043957879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111108296747053302695971919 166662445120579954043957879)
  ·
    refine ⟨249993667680869931065936819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 166662445120579954043957879 249993667680869931065936819)
    ·
      refine ⟨374990501521304896598905229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 249993667680869931065936819 374990501521304896598905229)
      ·
        refine ⟨140621438070489336224589461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 374990501521304896598905229 140621438070489336224589461)
        ·
          refine ⟨6591629909554187635527631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 140621438070489336224589461 6591629909554187635527631)
          ·
            refine ⟨9887444864331281453291447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6591629909554187635527631 9887444864331281453291447)
            ·
              refine ⟨14831167296496922179937171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9887444864331281453291447 14831167296496922179937171)
              ·
                refine ⟨22246750944745383269905757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14831167296496922179937171 22246750944745383269905757)
                ·
                  refine ⟨8342531604279518726214659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22246750944745383269905757 8342531604279518726214659)
                  ·
                    refine ⟨12513797406419278089321989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8342531604279518726214659 12513797406419278089321989)
                    ·
                      refine ⟨2346337013703614641747873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12513797406419278089321989 2346337013703614641747873)
                      ·
                        rfl

theorem cell23_4569475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 1, 1, 1, 3, 1, 4].length) (baseStart_4569475 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4569475 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4569475 prefixEnd_4569475 := by exact prefixLift 4569475
  have htrace : WordTrace (prefixWord ++ tailWord_4569475) baseStart_4569475 baseEnd_4569475 := by
    simpa [prefixWord, tailWord_4569475, baseEnd_4569475] using wordTrace_append hprefix tailTrace_4569475
  have hstable : (prefixWord ++ tailWord_4569475).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4569475).length < 2 ^ (prefixWord ++ tailWord_4569475).sum := by decide
  have hdescent : baseEnd_4569475 < baseStart_4569475 := by decide
  rcases family_descends (prefixWord ++ tailWord_4569475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4569495 : List Nat := [1, 1, 3, 3, 1, 1, 2, 5, 1, 2, 3]
def baseStart_4569495 : Nat := 118140960795 + 4569495 * 2 ^ 59
def prefixEnd_4569495 : Nat := 4983230072969 + 3 ^ 40 * 4569495 * 2
def baseEnd_4569495 : Nat := 2346347283316704563497781

theorem tailTrace_4569495 : CollatzResearch.WordTrace tailWord_4569495 prefixEnd_4569495 2346347283316704563497781 := by
  unfold tailWord_4569495
  simp only [CollatzResearch.WordTrace]
  refine ⟨166663174580507497459685939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111108783053671664973123959 166663174580507497459685939)
  ·
    refine ⟨249994761870761246189528909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 166663174580507497459685939 249994761870761246189528909)
    ·
      refine ⟨93748035701535467321073341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 249994761870761246189528909 93748035701535467321073341)
      ·
        refine ⟨35155513388075800245402503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 93748035701535467321073341 35155513388075800245402503)
        ·
          refine ⟨52733270082113700368103755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35155513388075800245402503 52733270082113700368103755)
          ·
            refine ⟨79099905123170550552155633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52733270082113700368103755 79099905123170550552155633)
            ·
              refine ⟨59324928842377912914116725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 79099905123170550552155633 59324928842377912914116725)
              ·
                refine ⟨5561712078972929335698443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 59324928842377912914116725 5561712078972929335698443)
                ·
                  refine ⟨8342568118459394003547665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5561712078972929335698443 8342568118459394003547665)
                  ·
                    refine ⟨6256926088844545502660749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8342568118459394003547665 6256926088844545502660749)
                    ·
                      refine ⟨2346347283316704563497781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6256926088844545502660749 2346347283316704563497781)
                      ·
                        rfl

theorem cell23_4569495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 2, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 2, 5, 1, 2, 3].length) (baseStart_4569495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4569495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4569495 prefixEnd_4569495 := by exact prefixLift 4569495
  have htrace : WordTrace (prefixWord ++ tailWord_4569495) baseStart_4569495 baseEnd_4569495 := by
    simpa [prefixWord, tailWord_4569495, baseEnd_4569495] using wordTrace_append hprefix tailTrace_4569495
  have hstable : (prefixWord ++ tailWord_4569495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4569495).length < 2 ^ (prefixWord ++ tailWord_4569495).sum := by decide
  have hdescent : baseEnd_4569495 < baseStart_4569495 := by decide
  rcases family_descends (prefixWord ++ tailWord_4569495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4569509 : List Nat := [1, 3, 1, 2, 1, 1, 5, 4, 1, 2, 2]
def baseStart_4569509 : Nat := 118140960795 + 4569509 * 2 ^ 59
def prefixEnd_4569509 : Nat := 4983230072969 + 3 ^ 40 * 4569509 * 2
def baseEnd_4569509 : Nat := 2346354472045867508722717

theorem tailTrace_4569509 : CollatzResearch.WordTrace tailWord_4569509 prefixEnd_4569509 2346354472045867508722717 := by
  unfold tailWord_4569509
  simp only [CollatzResearch.WordTrace]
  refine ⟨166663685202456777850695581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111109123468304518567130387 166663685202456777850695581)
  ·
    refine ⟨62498881950921291694010843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 166663685202456777850695581 62498881950921291694010843)
    ·
      refine ⟨93748322926381937541016265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62498881950921291694010843 93748322926381937541016265)
      ·
        refine ⟨70311242194786453155762199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 93748322926381937541016265 70311242194786453155762199)
        ·
          refine ⟨105466863292179679733643299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70311242194786453155762199 105466863292179679733643299)
          ·
            refine ⟨158200294938269519600464949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 105466863292179679733643299 158200294938269519600464949)
            ·
              refine ⟨14831277650462767462543589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 158200294938269519600464949 14831277650462767462543589)
              ·
                refine ⟨2780864559461768899226923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14831277650462767462543589 2780864559461768899226923)
                ·
                  refine ⟨4171296839192653348840385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2780864559461768899226923 4171296839192653348840385)
                  ·
                    refine ⟨3128472629394490011630289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4171296839192653348840385 3128472629394490011630289)
                    ·
                      refine ⟨2346354472045867508722717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3128472629394490011630289 2346354472045867508722717)
                      ·
                        rfl

theorem cell23_4569509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 5, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 5, 4, 1, 2, 2].length) (baseStart_4569509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4569509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4569509 prefixEnd_4569509 := by exact prefixLift 4569509
  have htrace : WordTrace (prefixWord ++ tailWord_4569509) baseStart_4569509 baseEnd_4569509 := by
    simpa [prefixWord, tailWord_4569509, baseEnd_4569509] using wordTrace_append hprefix tailTrace_4569509
  have hstable : (prefixWord ++ tailWord_4569509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4569509).length < 2 ^ (prefixWord ++ tailWord_4569509).sum := by decide
  have hdescent : baseEnd_4569509 < baseStart_4569509 := by decide
  rcases family_descends (prefixWord ++ tailWord_4569509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4569512 : List Nat := [2, 1, 6, 1, 1, 1, 1, 2, 3, 2, 3]
def baseStart_4569512 : Nat := 118140960795 + 4569512 * 2 ^ 59
def prefixEnd_4569512 : Nat := 4983230072969 + 3 ^ 40 * 4569512 * 2
def baseEnd_4569512 : Nat := 2346356012487830996985203

theorem tailTrace_4569512 : CollatzResearch.WordTrace tailWord_4569512 prefixEnd_4569512 2346356012487830996985203 := by
  unfold tailWord_4569512
  simp only [CollatzResearch.WordTrace]
  refine ⟨83331897310722954681527395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111109196414297272908703193 83331897310722954681527395)
  ·
    refine ⟨124997845966084432022291093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83331897310722954681527395 124997845966084432022291093)
    ·
      refine ⟨5859274029660207751044895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 124997845966084432022291093 5859274029660207751044895)
      ·
        refine ⟨8788911044490311626567343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5859274029660207751044895 8788911044490311626567343)
        ·
          refine ⟨13183366566735467439851015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8788911044490311626567343 13183366566735467439851015)
          ·
            refine ⟨19775049850103201159776523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13183366566735467439851015 19775049850103201159776523)
            ·
              refine ⟨29662574775154801739664785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19775049850103201159776523 29662574775154801739664785)
              ·
                refine ⟨22246931081366101304748589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29662574775154801739664785 22246931081366101304748589)
                ·
                  refine ⟨8342599155512287989280721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22246931081366101304748589 8342599155512287989280721)
                  ·
                    refine ⟨6256949366634215991960541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8342599155512287989280721 6256949366634215991960541)
                    ·
                      refine ⟨2346356012487830996985203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6256949366634215991960541 2346356012487830996985203)
                      ·
                        rfl

theorem cell23_4569512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 1, 2, 3, 2, 3].length) (baseStart_4569512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4569512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4569512 prefixEnd_4569512 := by exact prefixLift 4569512
  have htrace : WordTrace (prefixWord ++ tailWord_4569512) baseStart_4569512 baseEnd_4569512 := by
    simpa [prefixWord, tailWord_4569512, baseEnd_4569512] using wordTrace_append hprefix tailTrace_4569512
  have hstable : (prefixWord ++ tailWord_4569512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4569512).length < 2 ^ (prefixWord ++ tailWord_4569512).sum := by decide
  have hdescent : baseEnd_4569512 < baseStart_4569512 := by decide
  rcases family_descends (prefixWord ++ tailWord_4569512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4569586 : List Nat := [3, 2, 1, 4, 2, 1, 2, 2, 1, 3, 2]
def baseStart_4569586 : Nat := 118140960795 + 4569586 * 2 ^ 59
def prefixEnd_4569586 : Nat := 4983230072969 + 3 ^ 40 * 4569586 * 2
def baseEnd_4569586 : Nat := 2346394010056263707459863

theorem tailTrace_4569586 : CollatzResearch.WordTrace tailWord_4569586 prefixEnd_4569586 2346394010056263707459863 := by
  unfold tailWord_4569586
  simp only [CollatzResearch.WordTrace]
  refine ⟨41666623405794455000312153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 111110995748785213334165741 41666623405794455000312153)
  ·
    refine ⟨31249967554345841250234115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41666623405794455000312153 31249967554345841250234115)
    ·
      refine ⟨46874951331518761875351173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31249967554345841250234115 46874951331518761875351173)
      ·
        refine ⟨8789053374659767851628345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 46874951331518761875351173 8789053374659767851628345)
        ·
          refine ⟨6591790030994825888721259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8789053374659767851628345 6591790030994825888721259)
          ·
            refine ⟨9887685046492238833081889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6591790030994825888721259 9887685046492238833081889)
            ·
              refine ⟨7415763784869179124811417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9887685046492238833081889 7415763784869179124811417)
              ·
                refine ⟨5561822838651884343608563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7415763784869179124811417 5561822838651884343608563)
                ·
                  refine ⟨8342734257977826515412845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5561822838651884343608563 8342734257977826515412845)
                  ·
                    refine ⟨3128525346741684943279817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8342734257977826515412845 3128525346741684943279817)
                    ·
                      refine ⟨2346394010056263707459863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3128525346741684943279817 2346394010056263707459863)
                      ·
                        rfl

theorem cell23_4569586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 1, 2, 2, 1, 3, 2].length) (baseStart_4569586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4569586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4569586 prefixEnd_4569586 := by exact prefixLift 4569586
  have htrace : WordTrace (prefixWord ++ tailWord_4569586) baseStart_4569586 baseEnd_4569586 := by
    simpa [prefixWord, tailWord_4569586, baseEnd_4569586] using wordTrace_append hprefix tailTrace_4569586
  have hstable : (prefixWord ++ tailWord_4569586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4569586).length < 2 ^ (prefixWord ++ tailWord_4569586).sum := by decide
  have hdescent : baseEnd_4569586 < baseStart_4569586 := by decide
  rcases family_descends (prefixWord ++ tailWord_4569586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4569625 : List Nat := [1, 2, 1, 2, 1, 1, 2, 3, 1, 7, 2]
def baseStart_4569625 : Nat := 118140960795 + 4569625 * 2 ^ 59
def prefixEnd_4569625 : Nat := 4983230072969 + 3 ^ 40 * 4569625 * 2
def baseEnd_4569625 : Nat := 2346414035801789054872183

theorem tailTrace_4569625 : CollatzResearch.WordTrace tailWord_4569625 prefixEnd_4569625 2346414035801789054872183 := by
  unfold tailWord_4569625
  simp only [CollatzResearch.WordTrace]
  refine ⟨166667916070036529661918329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111111944046691019774612219 166667916070036529661918329)
  ·
    refine ⟨125000937052527397246438747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 166667916070036529661918329 125000937052527397246438747)
    ·
      refine ⟨187501405578791095869658121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125000937052527397246438747 187501405578791095869658121)
      ·
        refine ⟨140626054184093321902243591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 187501405578791095869658121 140626054184093321902243591)
        ·
          refine ⟨210939081276139982853365387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 140626054184093321902243591 210939081276139982853365387)
          ·
            refine ⟨316408621914209974280048081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 210939081276139982853365387 316408621914209974280048081)
            ·
              refine ⟨237306466435657480710036061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 316408621914209974280048081 237306466435657480710036061)
              ·
                refine ⟨88989924913371555266263523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 237306466435657480710036061 88989924913371555266263523)
                ·
                  refine ⟨133484887370057332899395285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 88989924913371555266263523 133484887370057332899395285)
                  ·
                    refine ⟨3128552047735718739829577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 133484887370057332899395285 3128552047735718739829577)
                    ·
                      refine ⟨2346414035801789054872183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3128552047735718739829577 2346414035801789054872183)
                      ·
                        rfl

theorem cell23_4569625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 3, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 3, 1, 7, 2].length) (baseStart_4569625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4569625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4569625 prefixEnd_4569625 := by exact prefixLift 4569625
  have htrace : WordTrace (prefixWord ++ tailWord_4569625) baseStart_4569625 baseEnd_4569625 := by
    simpa [prefixWord, tailWord_4569625, baseEnd_4569625] using wordTrace_append hprefix tailTrace_4569625
  have hstable : (prefixWord ++ tailWord_4569625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4569625).length < 2 ^ (prefixWord ++ tailWord_4569625).sum := by decide
  have hdescent : baseEnd_4569625 < baseStart_4569625 := by decide
  rcases family_descends (prefixWord ++ tailWord_4569625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4569648 : List Nat := [2, 1, 1, 1, 2, 3, 2, 1, 2, 8]
def baseStart_4569648 : Nat := 118140960795 + 4569648 * 2 ^ 59
def prefixEnd_4569648 : Nat := 4983230072969 + 3 ^ 40 * 4569648 * 2
def baseEnd_4569648 : Nat := 782141948618947488294859

theorem tailTrace_4569648 : CollatzResearch.WordTrace tailWord_4569648 prefixEnd_4569648 782141948618947488294859 := by
  unfold tailWord_4569648
  simp only [CollatzResearch.WordTrace]
  refine ⟨83334377474476602295002799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111112503299302136393337065 83334377474476602295002799)
  ·
    refine ⟨125001566211714903442504199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83334377474476602295002799 125001566211714903442504199)
    ·
      refine ⟨187502349317572355163756299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125001566211714903442504199 187502349317572355163756299)
      ·
        refine ⟨281253523976358532745634449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 187502349317572355163756299 281253523976358532745634449)
        ·
          refine ⟨210940142982268899559225837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 281253523976358532745634449 210940142982268899559225837)
          ·
            refine ⟨79102553618350837334709689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 210940142982268899559225837 79102553618350837334709689)
            ·
              refine ⟨59326915213763128001032267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 79102553618350837334709689 59326915213763128001032267)
              ·
                refine ⟨88990372820644692001548401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 59326915213763128001032267 88990372820644692001548401)
                ·
                  refine ⟨66742779615483519001161301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 88990372820644692001548401 66742779615483519001161301)
                  ·
                    refine ⟨782141948618947488294859, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 66742779615483519001161301 782141948618947488294859)
                    ·
                      rfl

theorem cell23_4569648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 2, 1, 2, 8].length) (baseStart_4569648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4569648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4569648 prefixEnd_4569648 := by exact prefixLift 4569648
  have htrace : WordTrace (prefixWord ++ tailWord_4569648) baseStart_4569648 baseEnd_4569648 := by
    simpa [prefixWord, tailWord_4569648, baseEnd_4569648] using wordTrace_append hprefix tailTrace_4569648
  have hstable : (prefixWord ++ tailWord_4569648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4569648).length < 2 ^ (prefixWord ++ tailWord_4569648).sum := by decide
  have hdescent : baseEnd_4569648 < baseStart_4569648 := by decide
  rcases family_descends (prefixWord ++ tailWord_4569648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4569682 : List Nat := [3, 2, 2, 1, 2, 1, 2, 3, 3, 4]
def baseStart_4569682 : Nat := 118140960795 + 4569682 * 2 ^ 59
def prefixEnd_4569682 : Nat := 4983230072969 + 3 ^ 40 * 4569682 * 2
def baseEnd_4569682 : Nat := 782147768066365110619807

theorem tailTrace_4569682 : CollatzResearch.WordTrace tailWord_4569682 prefixEnd_4569682 782147768066365110619807 := by
  unfold tailWord_4569682
  simp only [CollatzResearch.WordTrace]
  refine ⟨41667498757707507099185825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 111113330020553352264495533 41667498757707507099185825)
  ·
    refine ⟨31250624068280630324389369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41667498757707507099185825 31250624068280630324389369)
    ·
      refine ⟨23437968051210472743292027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31250624068280630324389369 23437968051210472743292027)
      ·
        refine ⟨35156952076815709114938041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23437968051210472743292027 35156952076815709114938041)
        ·
          refine ⟨26367714057611781836203531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35156952076815709114938041 26367714057611781836203531)
          ·
            refine ⟨39551571086417672754305297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26367714057611781836203531 39551571086417672754305297)
            ·
              refine ⟨29663678314813254565728973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39551571086417672754305297 29663678314813254565728973)
              ·
                refine ⟨11123879368054970462148365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29663678314813254565728973 11123879368054970462148365)
                ·
                  refine ⟨4171454763020613923305637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11123879368054970462148365 4171454763020613923305637)
                  ·
                    refine ⟨782147768066365110619807, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4171454763020613923305637 782147768066365110619807)
                    ·
                      rfl

theorem cell23_4569682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 2, 3, 3, 4].length) (baseStart_4569682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4569682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4569682 prefixEnd_4569682 := by exact prefixLift 4569682
  have htrace : WordTrace (prefixWord ++ tailWord_4569682) baseStart_4569682 baseEnd_4569682 := by
    simpa [prefixWord, tailWord_4569682, baseEnd_4569682] using wordTrace_append hprefix tailTrace_4569682
  have hstable : (prefixWord ++ tailWord_4569682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4569682).length < 2 ^ (prefixWord ++ tailWord_4569682).sum := by decide
  have hdescent : baseEnd_4569682 < baseStart_4569682 := by decide
  rcases family_descends (prefixWord ++ tailWord_4569682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4569709 : List Nat := [1, 5, 1, 1, 3, 1, 3, 1, 2, 2, 3]
def baseStart_4569709 : Nat := 118140960795 + 4569709 * 2 ^ 59
def prefixEnd_4569709 : Nat := 4983230072969 + 3 ^ 40 * 4569709 * 2
def baseEnd_4569709 : Nat := 2346457168176766726221797

theorem tailTrace_4569709 : CollatzResearch.WordTrace tailWord_4569709 prefixEnd_4569709 2346457168176766726221797 := by
  unfold tailWord_4569709
  simp only [CollatzResearch.WordTrace]
  refine ⟨166670979801732212007976181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111113986534488141338650787 166670979801732212007976181)
  ·
    refine ⟨15625404356412394875747767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 166670979801732212007976181 15625404356412394875747767)
    ·
      refine ⟨23438106534618592313621651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15625404356412394875747767 23438106534618592313621651)
      ·
        refine ⟨35157159801927888470432477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23438106534618592313621651 35157159801927888470432477)
        ·
          refine ⟨13183934925722958176412179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35157159801927888470432477 13183934925722958176412179)
          ·
            refine ⟨19775902388584437264618269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13183934925722958176412179 19775902388584437264618269)
            ·
              refine ⟨7415963395719163974231851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19775902388584437264618269 7415963395719163974231851)
              ·
                refine ⟨11123945093578745961347777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7415963395719163974231851 11123945093578745961347777)
                ·
                  refine ⟨8342958820184059471010833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11123945093578745961347777 8342958820184059471010833)
                  ·
                    refine ⟨6257219115138044603258125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8342958820184059471010833 6257219115138044603258125)
                    ·
                      refine ⟨2346457168176766726221797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6257219115138044603258125 2346457168176766726221797)
                      ·
                        rfl

theorem cell23_4569709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 3, 1, 2, 2, 3].length) (baseStart_4569709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4569709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4569709 prefixEnd_4569709 := by exact prefixLift 4569709
  have htrace : WordTrace (prefixWord ++ tailWord_4569709) baseStart_4569709 baseEnd_4569709 := by
    simpa [prefixWord, tailWord_4569709, baseEnd_4569709] using wordTrace_append hprefix tailTrace_4569709
  have hstable : (prefixWord ++ tailWord_4569709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4569709).length < 2 ^ (prefixWord ++ tailWord_4569709).sum := by decide
  have hdescent : baseEnd_4569709 < baseStart_4569709 := by decide
  rcases family_descends (prefixWord ++ tailWord_4569709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4569765 : List Nat := [1, 3, 1, 2, 1, 2, 1, 1, 5, 1, 5]
def baseStart_4569765 : Nat := 118140960795 + 4569765 * 2 ^ 59
def prefixEnd_4569765 : Nat := 4983230072969 + 3 ^ 40 * 4569765 * 2
def baseEnd_4569765 : Nat := 2346485923093418507121539

theorem tailTrace_4569765 : CollatzResearch.WordTrace tailWord_4569765 prefixEnd_4569765 2346485923093418507121539 := by
  unfold tailWord_4569765
  simp only [CollatzResearch.WordTrace]
  refine ⟨166673022289529333572014749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111115348193019555714676499 166673022289529333572014749)
  ·
    refine ⟨62502383358573500089505531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 166673022289529333572014749 62502383358573500089505531)
    ·
      refine ⟨93753575037860250134258297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62502383358573500089505531 93753575037860250134258297)
      ·
        refine ⟨70315181278395187600693723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 93753575037860250134258297 70315181278395187600693723)
        ·
          refine ⟨105472771917592781401040585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70315181278395187600693723 105472771917592781401040585)
          ·
            refine ⟨79104578938194586050780439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 105472771917592781401040585 79104578938194586050780439)
            ·
              refine ⟨118656868407291879076170659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 79104578938194586050780439 118656868407291879076170659)
              ·
                refine ⟨177985302610937818614255989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 118656868407291879076170659 177985302610937818614255989)
                ·
                  refine ⟨16686122119775420495086499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 177985302610937818614255989 16686122119775420495086499)
                  ·
                    refine ⟨25029183179663130742629749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16686122119775420495086499 25029183179663130742629749)
                    ·
                      refine ⟨2346485923093418507121539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25029183179663130742629749 2346485923093418507121539)
                      ·
                        rfl

theorem cell23_4569765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 1, 5, 1, 5].length) (baseStart_4569765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4569765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4569765 prefixEnd_4569765 := by exact prefixLift 4569765
  have htrace : WordTrace (prefixWord ++ tailWord_4569765) baseStart_4569765 baseEnd_4569765 := by
    simpa [prefixWord, tailWord_4569765, baseEnd_4569765] using wordTrace_append hprefix tailTrace_4569765
  have hstable : (prefixWord ++ tailWord_4569765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4569765).length < 2 ^ (prefixWord ++ tailWord_4569765).sum := by decide
  have hdescent : baseEnd_4569765 < baseStart_4569765 := by decide
  rcases family_descends (prefixWord ++ tailWord_4569765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4569773 : List Nat := [1, 5, 2, 1, 1, 2, 3, 3, 1, 1, 3]
def baseStart_4569773 : Nat := 118140960795 + 4569773 * 2 ^ 59
def prefixEnd_4569773 : Nat := 4983230072969 + 3 ^ 40 * 4569773 * 2
def baseEnd_4569773 : Nat := 2346490030938654475821503

theorem tailTrace_4569773 : CollatzResearch.WordTrace tailWord_4569773 prefixEnd_4569773 2346490030938654475821503 := by
  unfold tailWord_4569773
  simp only [CollatzResearch.WordTrace]
  refine ⟨166673314073500350938305973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111115542715666900625537315 166673314073500350938305973)
  ·
    refine ⟨15625623194390657900466185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 166673314073500350938305973 15625623194390657900466185)
    ·
      refine ⟨11719217395792993425349639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15625623194390657900466185 11719217395792993425349639)
      ·
        refine ⟨17578826093689490138024459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11719217395792993425349639 17578826093689490138024459)
        ·
          refine ⟨26368239140534235207036689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17578826093689490138024459 26368239140534235207036689)
          ·
            refine ⟨19776179355400676405277517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26368239140534235207036689 19776179355400676405277517)
            ·
              refine ⟨7416067258275253651979069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19776179355400676405277517 7416067258275253651979069)
              ·
                refine ⟨2781025221853220119492151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7416067258275253651979069 2781025221853220119492151)
                ·
                  refine ⟨4171537832779830179238227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2781025221853220119492151 4171537832779830179238227)
                  ·
                    refine ⟨6257306749169745268857341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4171537832779830179238227 6257306749169745268857341)
                    ·
                      refine ⟨2346490030938654475821503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6257306749169745268857341 2346490030938654475821503)
                      ·
                        rfl

theorem cell23_4569773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 3, 3, 1, 1, 3].length) (baseStart_4569773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4569773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4569773 prefixEnd_4569773 := by exact prefixLift 4569773
  have htrace : WordTrace (prefixWord ++ tailWord_4569773) baseStart_4569773 baseEnd_4569773 := by
    simpa [prefixWord, tailWord_4569773, baseEnd_4569773] using wordTrace_append hprefix tailTrace_4569773
  have hstable : (prefixWord ++ tailWord_4569773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4569773).length < 2 ^ (prefixWord ++ tailWord_4569773).sum := by decide
  have hdescent : baseEnd_4569773 < baseStart_4569773 := by decide
  rcases family_descends (prefixWord ++ tailWord_4569773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4569802 : List Nat := [3, 1, 2, 1, 4, 2, 2, 8]
def baseStart_4569802 : Nat := 118140960795 + 4569802 * 2 ^ 59
def prefixEnd_4569802 : Nat := 4983230072969 + 3 ^ 40 * 4569802 * 2
def baseEnd_4569802 : Nat := 86907589699171661568847

theorem tailTrace_4569802 : CollatzResearch.WordTrace tailWord_4569802 prefixEnd_4569802 86907589699171661568847 := by
  unfold tailWord_4569802
  simp only [CollatzResearch.WordTrace]
  refine ⟨41668592947598822222777915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 111116247860263525927407773 41668592947598822222777915)
  ·
    refine ⟨62502889421398233334166873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41668592947598822222777915 62502889421398233334166873)
    ·
      refine ⟨46877167066048675000625155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62502889421398233334166873 46877167066048675000625155)
      ·
        refine ⟨70315750599073012500937733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46877167066048675000625155 70315750599073012500937733)
        ·
          refine ⟨13184203237326189843925825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 70315750599073012500937733 13184203237326189843925825)
          ·
            refine ⟨9888152427994642382944369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13184203237326189843925825 9888152427994642382944369)
            ·
              refine ⟨7416114320995981787208277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9888152427994642382944369 7416114320995981787208277)
              ·
                refine ⟨86907589699171661568847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7416114320995981787208277 86907589699171661568847)
                ·
                  rfl

theorem cell23_4569802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 2, 2, 8].length) (baseStart_4569802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4569802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4569802 prefixEnd_4569802 := by exact prefixLift 4569802
  have htrace : WordTrace (prefixWord ++ tailWord_4569802) baseStart_4569802 baseEnd_4569802 := by
    simpa [prefixWord, tailWord_4569802, baseEnd_4569802] using wordTrace_append hprefix tailTrace_4569802
  have hstable : (prefixWord ++ tailWord_4569802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4569802).length < 2 ^ (prefixWord ++ tailWord_4569802).sum := by decide
  have hdescent : baseEnd_4569802 < baseStart_4569802 := by decide
  rcases family_descends (prefixWord ++ tailWord_4569802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4569806 : List Nat := [4, 1, 1, 1, 3, 2, 4, 1, 2, 4]
def baseStart_4569806 : Nat := 118140960795 + 4569806 * 2 ^ 59
def prefixEnd_4569806 : Nat := 4983230072969 + 3 ^ 40 * 4569806 * 2
def baseEnd_4569806 : Nat := 782168991933417615569617

theorem tailTrace_4569806 : CollatzResearch.WordTrace tailWord_4569806 prefixEnd_4569806 782168991933417615569617 := by
  unfold tailWord_4569806
  simp only [CollatzResearch.WordTrace]
  refine ⟨20834314710297599696782159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 111116345121587198382838181 20834314710297599696782159)
  ·
    refine ⟨31251472065446399545173239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20834314710297599696782159 31251472065446399545173239)
    ·
      refine ⟨46877208098169599317759859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31251472065446399545173239 46877208098169599317759859)
      ·
        refine ⟨70315812147254398976639789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46877208098169599317759859 70315812147254398976639789)
        ·
          refine ⟨26368429555220399616239921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 70315812147254398976639789 26368429555220399616239921)
          ·
            refine ⟨19776322166415299712179941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26368429555220399616239921 19776322166415299712179941)
            ·
              refine ⟨3708060406202868696033739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19776322166415299712179941 3708060406202868696033739)
              ·
                refine ⟨5562090609304303044050609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3708060406202868696033739 5562090609304303044050609)
                ·
                  refine ⟨4171567956978227283037957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5562090609304303044050609 4171567956978227283037957)
                  ·
                    refine ⟨782168991933417615569617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4171567956978227283037957 782168991933417615569617)
                    ·
                      rfl

theorem cell23_4569806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 4, 1, 2, 4].length) (baseStart_4569806 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4569806 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4569806 prefixEnd_4569806 := by exact prefixLift 4569806
  have htrace : WordTrace (prefixWord ++ tailWord_4569806) baseStart_4569806 baseEnd_4569806 := by
    simpa [prefixWord, tailWord_4569806, baseEnd_4569806] using wordTrace_append hprefix tailTrace_4569806
  have hstable : (prefixWord ++ tailWord_4569806).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4569806).length < 2 ^ (prefixWord ++ tailWord_4569806).sum := by decide
  have hdescent : baseEnd_4569806 < baseStart_4569806 := by decide
  rcases family_descends (prefixWord ++ tailWord_4569806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4569813 : List Nat := [1, 3, 2, 5, 1, 2, 1, 2, 1, 1, 4]
def baseStart_4569813 : Nat := 118140960795 + 4569813 * 2 ^ 59
def prefixEnd_4569813 : Nat := 4983230072969 + 3 ^ 40 * 4569813 * 2
def baseEnd_4569813 : Nat := 2346510570164834319321319

theorem tailTrace_4569813 : CollatzResearch.WordTrace tailWord_4569813 prefixEnd_4569813 2346510570164834319321319 := by
  unfold tailWord_4569813
  simp only [CollatzResearch.WordTrace]
  refine ⟨166674772993355437769762093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111116515328903625179841395 166674772993355437769762093)
  ·
    refine ⟨62503039872508289163660785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 166674772993355437769762093 62503039872508289163660785)
    ·
      refine ⟨46877279904381216872745589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62503039872508289163660785 46877279904381216872745589)
      ·
        refine ⟨4394744991035739081819899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 46877279904381216872745589 4394744991035739081819899)
        ·
          refine ⟨6592117486553608622729849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4394744991035739081819899 6592117486553608622729849)
          ·
            refine ⟨4944088114915206467047387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6592117486553608622729849 4944088114915206467047387)
            ·
              refine ⟨7416132172372809700571081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4944088114915206467047387 7416132172372809700571081)
              ·
                refine ⟨5562099129279607275428311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7416132172372809700571081 5562099129279607275428311)
                ·
                  refine ⟨8343148693919410913142467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5562099129279607275428311 8343148693919410913142467)
                  ·
                    refine ⟨12514723040879116369713701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8343148693919410913142467 12514723040879116369713701)
                    ·
                      refine ⟨2346510570164834319321319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12514723040879116369713701 2346510570164834319321319)
                      ·
                        rfl

theorem cell23_4569813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 2, 1, 2, 1, 1, 4].length) (baseStart_4569813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4569813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4569813 prefixEnd_4569813 := by exact prefixLift 4569813
  have htrace : WordTrace (prefixWord ++ tailWord_4569813) baseStart_4569813 baseEnd_4569813 := by
    simpa [prefixWord, tailWord_4569813, baseEnd_4569813] using wordTrace_append hprefix tailTrace_4569813
  have hstable : (prefixWord ++ tailWord_4569813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4569813).length < 2 ^ (prefixWord ++ tailWord_4569813).sum := by decide
  have hdescent : baseEnd_4569813 < baseStart_4569813 := by decide
  rcases family_descends (prefixWord ++ tailWord_4569813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4569816 : List Nat := [2, 1, 2, 2, 3, 4, 1, 2, 1, 2, 3]
def baseStart_4569816 : Nat := 118140960795 + 4569816 * 2 ^ 59
def prefixEnd_4569816 : Nat := 4983230072969 + 3 ^ 40 * 4569816 * 2
def baseEnd_4569816 : Nat := 2346512110606797807583805

theorem tailTrace_4569816 : CollatzResearch.WordTrace tailWord_4569816 prefixEnd_4569816 2346512110606797807583805 := by
  unfold tailWord_4569816
  simp only [CollatzResearch.WordTrace]
  refine ⟨83337441206172284641060651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111116588274896379521414201 83337441206172284641060651)
  ·
    refine ⟨125006161809258426961590977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83337441206172284641060651 125006161809258426961590977)
    ·
      refine ⟨93754621356943820221193233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 125006161809258426961590977 93754621356943820221193233)
      ·
        refine ⟨70315966017707865165894925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 93754621356943820221193233 70315966017707865165894925)
        ·
          refine ⟨26368487256640449437210597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 70315966017707865165894925 26368487256640449437210597)
          ·
            refine ⟨4944091360620084269476987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 26368487256640449437210597 4944091360620084269476987)
            ·
              refine ⟨7416137040930126404215481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4944091360620084269476987 7416137040930126404215481)
              ·
                refine ⟨5562102780697594803161611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7416137040930126404215481 5562102780697594803161611)
                ·
                  refine ⟨8343154171046392204742417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5562102780697594803161611 8343154171046392204742417)
                  ·
                    refine ⟨6257365628284794153556813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8343154171046392204742417 6257365628284794153556813)
                    ·
                      refine ⟨2346512110606797807583805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6257365628284794153556813 2346512110606797807583805)
                      ·
                        rfl

theorem cell23_4569816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 4, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 4, 1, 2, 1, 2, 3].length) (baseStart_4569816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4569816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4569816 prefixEnd_4569816 := by exact prefixLift 4569816
  have htrace : WordTrace (prefixWord ++ tailWord_4569816) baseStart_4569816 baseEnd_4569816 := by
    simpa [prefixWord, tailWord_4569816, baseEnd_4569816] using wordTrace_append hprefix tailTrace_4569816
  have hstable : (prefixWord ++ tailWord_4569816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4569816).length < 2 ^ (prefixWord ++ tailWord_4569816).sum := by decide
  have hdescent : baseEnd_4569816 < baseStart_4569816 := by decide
  rcases family_descends (prefixWord ++ tailWord_4569816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4569829 : List Nat := [1, 3, 1, 4, 1, 3, 1, 2, 1, 3, 3]
def baseStart_4569829 : Nat := 118140960795 + 4569829 * 2 ^ 59
def prefixEnd_4569829 : Nat := 4983230072969 + 3 ^ 40 * 4569829 * 2
def baseEnd_4569829 : Nat := 2346518785855306256721245

theorem tailTrace_4569829 : CollatzResearch.WordTrace tailWord_4569829 prefixEnd_4569829 2346518785855306256721245 := by
  unfold tailWord_4569829
  simp only [CollatzResearch.WordTrace]
  refine ⟨166675356561297472502344541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111116904374198315001563027 166675356561297472502344541)
  ·
    refine ⟨62503258710486552188379203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 166675356561297472502344541 62503258710486552188379203)
    ·
      refine ⟨93754888065729828282568805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62503258710486552188379203 93754888065729828282568805)
      ·
        refine ⟨17579041512324342802981651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 93754888065729828282568805 17579041512324342802981651)
        ·
          refine ⟨26368562268486514204472477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17579041512324342802981651 26368562268486514204472477)
          ·
            refine ⟨9888210850682442826677179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26368562268486514204472477 9888210850682442826677179)
            ·
              refine ⟨14832316276023664240015769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9888210850682442826677179 14832316276023664240015769)
              ·
                refine ⟨11124237207017748180011827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14832316276023664240015769 11124237207017748180011827)
                ·
                  refine ⟨16686355810526622270017741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11124237207017748180011827 16686355810526622270017741)
                  ·
                    refine ⟨6257383428947483351256653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16686355810526622270017741 6257383428947483351256653)
                    ·
                      refine ⟨2346518785855306256721245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6257383428947483351256653 2346518785855306256721245)
                      ·
                        rfl

theorem cell23_4569829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 3, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 3, 1, 2, 1, 3, 3].length) (baseStart_4569829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4569829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4569829 prefixEnd_4569829 := by exact prefixLift 4569829
  have htrace : WordTrace (prefixWord ++ tailWord_4569829) baseStart_4569829 baseEnd_4569829 := by
    simpa [prefixWord, tailWord_4569829, baseEnd_4569829] using wordTrace_append hprefix tailTrace_4569829
  have hstable : (prefixWord ++ tailWord_4569829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4569829).length < 2 ^ (prefixWord ++ tailWord_4569829).sum := by decide
  have hdescent : baseEnd_4569829 < baseStart_4569829 := by decide
  rcases family_descends (prefixWord ++ tailWord_4569829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4569852 : List Nat := [2, 2, 2, 1, 3, 2, 1, 1, 2, 3, 4]
def baseStart_4569852 : Nat := 118140960795 + 4569852 * 2 ^ 59
def prefixEnd_4569852 : Nat := 4983230072969 + 3 ^ 40 * 4569852 * 2
def baseEnd_4569852 : Nat := 2346530595910359666733639

theorem tailTrace_4569852 : CollatzResearch.WordTrace tailWord_4569852 prefixEnd_4569852 2346530595910359666733639 := by
  unfold tailWord_4569852
  simp only [CollatzResearch.WordTrace]
  refine ⟨83338097720107073715215905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111117463626809431620287873 83338097720107073715215905)
  ·
    refine ⟨62503573290080305286411929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83338097720107073715215905 62503573290080305286411929)
    ·
      refine ⟨46877679967560228964808947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62503573290080305286411929 46877679967560228964808947)
      ·
        refine ⟨70316519951340343447213421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46877679967560228964808947 70316519951340343447213421)
        ·
          refine ⟨26368694981752628792705033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 70316519951340343447213421 26368694981752628792705033)
          ·
            refine ⟨19776521236314471594528775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26368694981752628792705033 19776521236314471594528775)
            ·
              refine ⟨29664781854471707391793163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19776521236314471594528775 29664781854471707391793163)
              ·
                refine ⟨44497172781707561087689745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29664781854471707391793163 44497172781707561087689745)
                ·
                  refine ⟨33372879586280670815767309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 44497172781707561087689745 33372879586280670815767309)
                  ·
                    refine ⟨12514829844855251555912741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 33372879586280670815767309 12514829844855251555912741)
                    ·
                      refine ⟨2346530595910359666733639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12514829844855251555912741 2346530595910359666733639)
                      ·
                        rfl

theorem cell23_4569852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 1, 1, 2, 3, 4].length) (baseStart_4569852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4569852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4569852 prefixEnd_4569852 := by exact prefixLift 4569852
  have htrace : WordTrace (prefixWord ++ tailWord_4569852) baseStart_4569852 baseEnd_4569852 := by
    simpa [prefixWord, tailWord_4569852, baseEnd_4569852] using wordTrace_append hprefix tailTrace_4569852
  have hstable : (prefixWord ++ tailWord_4569852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4569852).length < 2 ^ (prefixWord ++ tailWord_4569852).sum := by decide
  have hdescent : baseEnd_4569852 < baseStart_4569852 := by decide
  rcases family_descends (prefixWord ++ tailWord_4569852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4569882 : List Nat := [3, 1, 1, 3, 2, 1, 1, 2, 1, 4, 4]
def baseStart_4569882 : Nat := 118140960795 + 4569882 * 2 ^ 59
def prefixEnd_4569882 : Nat := 4983230072969 + 3 ^ 40 * 4569882 * 2
def baseEnd_4569882 : Nat := 2346546000329994549358501

theorem tailTrace_4569882 : CollatzResearch.WordTrace tailWord_4569882 prefixEnd_4569882 2346546000329994549358501 := by
  unfold tailWord_4569882
  simp only [CollatzResearch.WordTrace]
  refine ⟨41669322407526365638505975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 111118193086736975036015933 41669322407526365638505975)
  ·
    refine ⟨62503983611289548457758963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41669322407526365638505975 62503983611289548457758963)
    ·
      refine ⟨93755975416934322686638445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62503983611289548457758963 93755975416934322686638445)
      ·
        refine ⟨35158490781350371007489417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 93755975416934322686638445 35158490781350371007489417)
        ·
          refine ⟨26368868086012778255617063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35158490781350371007489417 26368868086012778255617063)
          ·
            refine ⟨39553302129019167383425595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26368868086012778255617063 39553302129019167383425595)
            ·
              refine ⟨59329953193528751075138393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39553302129019167383425595 59329953193528751075138393)
              ·
                refine ⟨44497464895146563306353795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 59329953193528751075138393 44497464895146563306353795)
                ·
                  refine ⟨66746197342719844959530693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 44497464895146563306353795 66746197342719844959530693)
                  ·
                    refine ⟨12514912001759970929912005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 66746197342719844959530693 12514912001759970929912005)
                    ·
                      refine ⟨2346546000329994549358501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12514912001759970929912005 2346546000329994549358501)
                      ·
                        rfl

theorem cell23_4569882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 1, 2, 1, 4, 4].length) (baseStart_4569882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4569882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4569882 prefixEnd_4569882 := by exact prefixLift 4569882
  have htrace : WordTrace (prefixWord ++ tailWord_4569882) baseStart_4569882 baseEnd_4569882 := by
    simpa [prefixWord, tailWord_4569882, baseEnd_4569882] using wordTrace_append hprefix tailTrace_4569882
  have hstable : (prefixWord ++ tailWord_4569882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4569882).length < 2 ^ (prefixWord ++ tailWord_4569882).sum := by decide
  have hdescent : baseEnd_4569882 < baseStart_4569882 := by decide
  rcases family_descends (prefixWord ++ tailWord_4569882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4569890 : List Nat := [3, 3, 1, 1, 2, 4, 2, 1, 1, 3, 2]
def baseStart_4569890 : Nat := 118140960795 + 4569890 * 2 ^ 59
def prefixEnd_4569890 : Nat := 4983230072969 + 3 ^ 40 * 4569890 * 2
def baseEnd_4569890 : Nat := 2346550108175230518058465

theorem tailTrace_4569890 : CollatzResearch.WordTrace tailWord_4569890 prefixEnd_4569890 2346550108175230518058465 := by
  unfold tailWord_4569890
  simp only [CollatzResearch.WordTrace]
  refine ⟨41669395353519119980078781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 111118387609384319946876749 41669395353519119980078781)
  ·
    refine ⟨15626023257569669992529543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41669395353519119980078781 15626023257569669992529543)
    ·
      refine ⟨23439034886354504988794315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15626023257569669992529543 23439034886354504988794315)
      ·
        refine ⟨35158552329531757483191473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23439034886354504988794315 35158552329531757483191473)
        ·
          refine ⟨26368914247148818112393605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35158552329531757483191473 26368914247148818112393605)
          ·
            refine ⟨4944171421340403396073801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 26368914247148818112393605 4944171421340403396073801)
            ·
              refine ⟨3708128566005302547055351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4944171421340403396073801 3708128566005302547055351)
              ·
                refine ⟨5562192849007953820583027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3708128566005302547055351 5562192849007953820583027)
                ·
                  refine ⟨8343289273511930730874541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5562192849007953820583027 8343289273511930730874541)
                  ·
                    refine ⟨3128733477566974024077953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8343289273511930730874541 3128733477566974024077953)
                    ·
                      refine ⟨2346550108175230518058465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3128733477566974024077953 2346550108175230518058465)
                      ·
                        rfl

theorem cell23_4569890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 4, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 4, 2, 1, 1, 3, 2].length) (baseStart_4569890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4569890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4569890 prefixEnd_4569890 := by exact prefixLift 4569890
  have htrace : WordTrace (prefixWord ++ tailWord_4569890) baseStart_4569890 baseEnd_4569890 := by
    simpa [prefixWord, tailWord_4569890, baseEnd_4569890] using wordTrace_append hprefix tailTrace_4569890
  have hstable : (prefixWord ++ tailWord_4569890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4569890).length < 2 ^ (prefixWord ++ tailWord_4569890).sum := by decide
  have hdescent : baseEnd_4569890 < baseStart_4569890 := by decide
  rcases family_descends (prefixWord ++ tailWord_4569890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4569909 : List Nat := [1, 3, 3, 1, 3, 2, 2, 1, 7]
def baseStart_4569909 : Nat := 118140960795 + 4569909 * 2 ^ 59
def prefixEnd_4569909 : Nat := 4983230072969 + 3 ^ 40 * 4569909 * 2
def baseEnd_4569909 : Nat := 260728873811962882635653

theorem tailTrace_4569909 : CollatzResearch.WordTrace tailWord_4569909 prefixEnd_4569909 260728873811962882635653 := by
  unfold tailWord_4569909
  simp only [CollatzResearch.WordTrace]
  refine ⟨166678274401007646165256781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111118849600671764110171187 166678274401007646165256781)
  ·
    refine ⟨62504352900377867311971293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 166678274401007646165256781 62504352900377867311971293)
    ·
      refine ⟨23439132337641700241989235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 62504352900377867311971293 23439132337641700241989235)
      ·
        refine ⟨35158698506462550362983853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23439132337641700241989235 35158698506462550362983853)
        ·
          refine ⟨13184511939923456386118945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35158698506462550362983853 13184511939923456386118945)
          ·
            refine ⟨9888383954942592289589209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13184511939923456386118945 9888383954942592289589209)
            ·
              refine ⟨7416287966206944217191907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9888383954942592289589209 7416287966206944217191907)
              ·
                refine ⟨11124431949310416325787861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7416287966206944217191907 11124431949310416325787861)
                ·
                  refine ⟨260728873811962882635653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11124431949310416325787861 260728873811962882635653)
                  ·
                    rfl

theorem cell23_4569909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 2, 2, 1, 7].length) (baseStart_4569909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4569909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4569909 prefixEnd_4569909 := by exact prefixLift 4569909
  have htrace : WordTrace (prefixWord ++ tailWord_4569909) baseStart_4569909 baseEnd_4569909 := by
    simpa [prefixWord, tailWord_4569909, baseEnd_4569909] using wordTrace_append hprefix tailTrace_4569909
  have hstable : (prefixWord ++ tailWord_4569909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4569909).length < 2 ^ (prefixWord ++ tailWord_4569909).sum := by decide
  have hdescent : baseEnd_4569909 < baseStart_4569909 := by decide
  rcases family_descends (prefixWord ++ tailWord_4569909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4569919 : List Nat := [1, 1, 2, 2, 5, 1, 2, 1, 2, 3, 3]
def baseStart_4569919 : Nat := 118140960795 + 4569919 * 2 ^ 59
def prefixEnd_4569919 : Nat := 4983230072969 + 3 ^ 40 * 4569919 * 2
def baseEnd_4569919 : Nat := 2346564999114210904595831

theorem tailTrace_4569919 : CollatzResearch.WordTrace tailWord_4569919 prefixEnd_4569919 2346564999114210904595831 := by
  unfold tailWord_4569919
  simp only [CollatzResearch.WordTrace]
  refine ⟨166678639130971417873120811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111119092753980945248747207 166678639130971417873120811)
  ·
    refine ⟨250017958696457126809681217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 166678639130971417873120811 250017958696457126809681217)
    ·
      refine ⟨187513469022342845107260913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 250017958696457126809681217 187513469022342845107260913)
      ·
        refine ⟨140635101766757133830445685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 187513469022342845107260913 140635101766757133830445685)
        ·
          refine ⟨13184540790633481296604283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 140635101766757133830445685 13184540790633481296604283)
          ·
            refine ⟨19776811185950221944906425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13184540790633481296604283 19776811185950221944906425)
            ·
              refine ⟨14832608389462666458679819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19776811185950221944906425 14832608389462666458679819)
              ·
                refine ⟨22248912584193999688019729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14832608389462666458679819 22248912584193999688019729)
                ·
                  refine ⟨16686684438145499766014797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22248912584193999688019729 16686684438145499766014797)
                  ·
                    refine ⟨6257506664304562412255549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16686684438145499766014797 6257506664304562412255549)
                    ·
                      refine ⟨2346564999114210904595831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6257506664304562412255549 2346564999114210904595831)
                      ·
                        rfl

theorem cell23_4569919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 2, 1, 2, 3, 3].length) (baseStart_4569919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4569919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4569919 prefixEnd_4569919 := by exact prefixLift 4569919
  have htrace : WordTrace (prefixWord ++ tailWord_4569919) baseStart_4569919 baseEnd_4569919 := by
    simpa [prefixWord, tailWord_4569919, baseEnd_4569919] using wordTrace_append hprefix tailTrace_4569919
  have hstable : (prefixWord ++ tailWord_4569919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4569919).length < 2 ^ (prefixWord ++ tailWord_4569919).sum := by decide
  have hdescent : baseEnd_4569919 < baseStart_4569919 := by decide
  rcases family_descends (prefixWord ++ tailWord_4569919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4569959 : List Nat := [1, 1, 5, 1, 2, 2, 1, 1, 4, 1, 4]
def baseStart_4569959 : Nat := 118140960795 + 4569959 * 2 ^ 59
def prefixEnd_4569959 : Nat := 4983230072969 + 3 ^ 40 * 4569959 * 2
def baseEnd_4569959 : Nat := 2346585538340390748095647

theorem tailTrace_4569959 : CollatzResearch.WordTrace tailWord_4569959 prefixEnd_4569959 2346585538340390748095647 := by
  unfold tailWord_4569959
  simp only [CollatzResearch.WordTrace]
  refine ⟨166680098050826504704576931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111120065367217669803051287 166680098050826504704576931)
  ·
    refine ⟨250020147076239757056865397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 166680098050826504704576931 250020147076239757056865397)
    ·
      refine ⟨23439388788397477224081131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 250020147076239757056865397 23439388788397477224081131)
      ·
        refine ⟨35159083182596215836121697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23439388788397477224081131 35159083182596215836121697)
        ·
          refine ⟨26369312386947161877091273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35159083182596215836121697 26369312386947161877091273)
          ·
            refine ⟨19776984290210371407818455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26369312386947161877091273 19776984290210371407818455)
            ·
              refine ⟨29665476435315557111727683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19776984290210371407818455 29665476435315557111727683)
              ·
                refine ⟨44498214652973335667591525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29665476435315557111727683 44498214652973335667591525)
                ·
                  refine ⟨8343415247432500437673411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 44498214652973335667591525 8343415247432500437673411)
                  ·
                    refine ⟨12515122871148750656510117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8343415247432500437673411 12515122871148750656510117)
                    ·
                      refine ⟨2346585538340390748095647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12515122871148750656510117 2346585538340390748095647)
                      ·
                        rfl

theorem cell23_4569959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 1, 1, 4, 1, 4].length) (baseStart_4569959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4569959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4569959 prefixEnd_4569959 := by exact prefixLift 4569959
  have htrace : WordTrace (prefixWord ++ tailWord_4569959) baseStart_4569959 baseEnd_4569959 := by
    simpa [prefixWord, tailWord_4569959, baseEnd_4569959] using wordTrace_append hprefix tailTrace_4569959
  have hstable : (prefixWord ++ tailWord_4569959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4569959).length < 2 ^ (prefixWord ++ tailWord_4569959).sum := by decide
  have hdescent : baseEnd_4569959 < baseStart_4569959 := by decide
  rcases family_descends (prefixWord ++ tailWord_4569959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4569966 : List Nat := [4, 1, 2, 3, 2, 1, 1, 1, 1, 2, 5]
def baseStart_4569966 : Nat := 118140960795 + 4569966 * 2 ^ 59
def prefixEnd_4569966 : Nat := 4983230072969 + 3 ^ 40 * 4569966 * 2
def baseEnd_4569966 : Nat := 2346589132704972220708115

theorem tailTrace_4569966 : CollatzResearch.WordTrace tailWord_4569966 prefixEnd_4569966 2346589132704972220708115 := by
  unfold tailWord_4569966
  simp only [CollatzResearch.WordTrace]
  refine ⟨20835044170225143112510219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 111120235574534096600054501 20835044170225143112510219)
  ·
    refine ⟨31252566255337714668765329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20835044170225143112510219 31252566255337714668765329)
    ·
      refine ⟨23439424691503286001573997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31252566255337714668765329 23439424691503286001573997)
      ·
        refine ⟨8789784259313732250590249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23439424691503286001573997 8789784259313732250590249)
        ·
          refine ⟨6592338194485299187942687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8789784259313732250590249 6592338194485299187942687)
          ·
            refine ⟨9888507291727948781914031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6592338194485299187942687 9888507291727948781914031)
            ·
              refine ⟨14832760937591923172871047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9888507291727948781914031 14832760937591923172871047)
              ·
                refine ⟨22249141406387884759306571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14832760937591923172871047 22249141406387884759306571)
                ·
                  refine ⟨33373712109581827138959857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22249141406387884759306571 33373712109581827138959857)
                  ·
                    refine ⟨25030284082186370354219893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 33373712109581827138959857 25030284082186370354219893)
                    ·
                      refine ⟨2346589132704972220708115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25030284082186370354219893 2346589132704972220708115)
                      ·
                        rfl

theorem cell23_4569966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 1, 1, 1, 1, 2, 5].length) (baseStart_4569966 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4569966 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4569966 prefixEnd_4569966 := by exact prefixLift 4569966
  have htrace : WordTrace (prefixWord ++ tailWord_4569966) baseStart_4569966 baseEnd_4569966 := by
    simpa [prefixWord, tailWord_4569966, baseEnd_4569966] using wordTrace_append hprefix tailTrace_4569966
  have hstable : (prefixWord ++ tailWord_4569966).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4569966).length < 2 ^ (prefixWord ++ tailWord_4569966).sum := by decide
  have hdescent : baseEnd_4569966 < baseStart_4569966 := by decide
  rcases family_descends (prefixWord ++ tailWord_4569966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4570046 : List Nat := [4, 2, 1, 1, 1, 2, 2, 4, 1, 5]
def baseStart_4570046 : Nat := 118140960795 + 4570046 * 2 ^ 59
def prefixEnd_4570046 : Nat := 4983230072969 + 3 ^ 40 * 4570046 * 2
def baseEnd_4570046 : Nat := 782210070385777302569249

theorem tailTrace_4570046 : CollatzResearch.WordTrace tailWord_4570046 prefixEnd_4570046 782210070385777302569249 := by
  unfold tailWord_4570046
  simp only [CollatzResearch.WordTrace]
  refine ⟨20835408900188914820374249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 111122180801007545708662661 20835408900188914820374249)
  ·
    refine ⟨15626556675141686115280687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20835408900188914820374249 15626556675141686115280687)
    ·
      refine ⟨23439835012712529172921031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15626556675141686115280687 23439835012712529172921031)
      ·
        refine ⟨35159752519068793759381547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23439835012712529172921031 35159752519068793759381547)
        ·
          refine ⟨52739628778603190639072321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35159752519068793759381547 52739628778603190639072321)
          ·
            refine ⟨39554721583952392979304241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52739628778603190639072321 39554721583952392979304241)
            ·
              refine ⟨29666041187964294734478181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39554721583952392979304241 29666041187964294734478181)
              ·
                refine ⟨5562382722743305262714659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 29666041187964294734478181 5562382722743305262714659)
                ·
                  refine ⟨8343574084114957894071989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5562382722743305262714659 8343574084114957894071989)
                  ·
                    refine ⟨782210070385777302569249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8343574084114957894071989 782210070385777302569249)
                    ·
                      rfl

theorem cell23_4570046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 2, 4, 1, 5].length) (baseStart_4570046 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4570046 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4570046 prefixEnd_4570046 := by exact prefixLift 4570046
  have htrace : WordTrace (prefixWord ++ tailWord_4570046) baseStart_4570046 baseEnd_4570046 := by
    simpa [prefixWord, tailWord_4570046, baseEnd_4570046] using wordTrace_append hprefix tailTrace_4570046
  have hstable : (prefixWord ++ tailWord_4570046).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4570046).length < 2 ^ (prefixWord ++ tailWord_4570046).sum := by decide
  have hdescent : baseEnd_4570046 < baseStart_4570046 := by decide
  rcases family_descends (prefixWord ++ tailWord_4570046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4570059 : List Nat := [1, 1, 1, 1, 3, 5, 2, 2, 1, 6]
def baseStart_4570059 : Nat := 118140960795 + 4570059 * 2 ^ 59
def prefixEnd_4570059 : Nat := 4983230072969 + 3 ^ 40 * 4570059 * 2
def baseEnd_4570059 : Nat := 782212295468613452281729

theorem tailTrace_4570059 : CollatzResearch.WordTrace tailWord_4570059 prefixEnd_4570059 782212295468613452281729 := by
  unfold tailWord_4570059
  simp only [CollatzResearch.WordTrace]
  refine ⟨166683745350464221783217231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111122496900309481188811487 166683745350464221783217231)
  ·
    refine ⟨250025618025696332674825847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 166683745350464221783217231 250025618025696332674825847)
    ·
      refine ⟨375038427038544499012238771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 250025618025696332674825847 375038427038544499012238771)
      ·
        refine ⟨562557640557816748518358157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 375038427038544499012238771 562557640557816748518358157)
        ·
          refine ⟨210959115209181280694384309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 562557640557816748518358157 210959115209181280694384309)
          ·
            refine ⟨19777417050860745065098529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 210959115209181280694384309 19777417050860745065098529)
            ·
              refine ⟨14833062788145558798823897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19777417050860745065098529 14833062788145558798823897)
              ·
                refine ⟨11124797091109169099117923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14833062788145558798823897 11124797091109169099117923)
                ·
                  refine ⟨16687195636663753648676885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11124797091109169099117923 16687195636663753648676885)
                  ·
                    refine ⟨782212295468613452281729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16687195636663753648676885 782212295468613452281729)
                    ·
                      rfl

theorem cell23_4570059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 2, 2, 1, 6].length) (baseStart_4570059 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4570059 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4570059 prefixEnd_4570059 := by exact prefixLift 4570059
  have htrace : WordTrace (prefixWord ++ tailWord_4570059) baseStart_4570059 baseEnd_4570059 := by
    simpa [prefixWord, tailWord_4570059, baseEnd_4570059] using wordTrace_append hprefix tailTrace_4570059
  have hstable : (prefixWord ++ tailWord_4570059).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4570059).length < 2 ^ (prefixWord ++ tailWord_4570059).sum := by decide
  have hdescent : baseEnd_4570059 < baseStart_4570059 := by decide
  rcases family_descends (prefixWord ++ tailWord_4570059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4570060 : List Nat := [2, 2, 1, 4, 1, 1, 4, 3, 1, 1, 3]
def baseStart_4570060 : Nat := 118140960795 + 4570060 * 2 ^ 59
def prefixEnd_4570060 : Nat := 4983230072969 + 3 ^ 40 * 4570060 * 2
def baseEnd_4570060 : Nat := 2346637399886494852932683

theorem tailTrace_4570060 : CollatzResearch.WordTrace tailWord_4570060 prefixEnd_4570060 2346637399886494852932683 := by
  unfold tailWord_4570060
  simp only [CollatzResearch.WordTrace]
  refine ⟨83341890911730299477001817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111122521215640399302669089 83341890911730299477001817)
  ·
    refine ⟨62506418183797724607751363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83341890911730299477001817 62506418183797724607751363)
    ·
      refine ⟨93759627275696586911627045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62506418183797724607751363 93759627275696586911627045)
      ·
        refine ⟨17579930114193110045930071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 93759627275696586911627045 17579930114193110045930071)
        ·
          refine ⟨26369895171289665068895107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17579930114193110045930071 26369895171289665068895107)
          ·
            refine ⟨39554842756934497603342661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26369895171289665068895107 39554842756934497603342661)
            ·
              refine ⟨7416533016925218300626749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 39554842756934497603342661 7416533016925218300626749)
              ·
                refine ⟨2781199881346956862735031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7416533016925218300626749 2781199881346956862735031)
                ·
                  refine ⟨4171799822020435294102547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2781199881346956862735031 4171799822020435294102547)
                  ·
                    refine ⟨6257699733030652941153821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4171799822020435294102547 6257699733030652941153821)
                    ·
                      refine ⟨2346637399886494852932683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6257699733030652941153821 2346637399886494852932683)
                      ·
                        rfl

theorem cell23_4570060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 4, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 4, 3, 1, 1, 3].length) (baseStart_4570060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4570060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4570060 prefixEnd_4570060 := by exact prefixLift 4570060
  have htrace : WordTrace (prefixWord ++ tailWord_4570060) baseStart_4570060 baseEnd_4570060 := by
    simpa [prefixWord, tailWord_4570060, baseEnd_4570060] using wordTrace_append hprefix tailTrace_4570060
  have hstable : (prefixWord ++ tailWord_4570060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4570060).length < 2 ^ (prefixWord ++ tailWord_4570060).sum := by decide
  have hdescent : baseEnd_4570060 < baseStart_4570060 := by decide
  rcases family_descends (prefixWord ++ tailWord_4570060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4570063 : List Nat := [1, 1, 2, 1, 1, 8, 2, 1, 1, 5]
def baseStart_4570063 : Nat := 118140960795 + 4570063 * 2 ^ 59
def prefixEnd_4570063 : Nat := 4983230072969 + 3 ^ 40 * 4570063 * 2
def baseEnd_4570063 : Nat := 782212980109486113731723

theorem tailTrace_4570063 : CollatzResearch.WordTrace tailWord_4570063 prefixEnd_4570063 782212980109486113731723 := by
  unfold tailWord_4570063
  simp only [CollatzResearch.WordTrace]
  refine ⟨166683891242449730466362843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111122594161633153644241895 166683891242449730466362843)
  ·
    refine ⟨250025836863674595699544265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 166683891242449730466362843 250025836863674595699544265)
    ·
      refine ⟨187519377647755946774658199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 250025836863674595699544265 187519377647755946774658199)
      ·
        refine ⟨281279066471633920161987299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 187519377647755946774658199 281279066471633920161987299)
        ·
          refine ⟨421918599707450880242980949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 281279066471633920161987299 421918599707450880242980949)
          ·
            refine ⟨4944358590321690002847433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 421918599707450880242980949 4944358590321690002847433)
            ·
              refine ⟨3708268942741267502135575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4944358590321690002847433 3708268942741267502135575)
              ·
                refine ⟨5562403414111901253203363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3708268942741267502135575 5562403414111901253203363)
                ·
                  refine ⟨8343605121167851879805045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5562403414111901253203363 8343605121167851879805045)
                  ·
                    refine ⟨782212980109486113731723, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8343605121167851879805045 782212980109486113731723)
                    ·
                      rfl

theorem cell23_4570063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 8, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 8, 2, 1, 1, 5].length) (baseStart_4570063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4570063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4570063 prefixEnd_4570063 := by exact prefixLift 4570063
  have htrace : WordTrace (prefixWord ++ tailWord_4570063) baseStart_4570063 baseEnd_4570063 := by
    simpa [prefixWord, tailWord_4570063, baseEnd_4570063] using wordTrace_append hprefix tailTrace_4570063
  have hstable : (prefixWord ++ tailWord_4570063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4570063).length < 2 ^ (prefixWord ++ tailWord_4570063).sum := by decide
  have hdescent : baseEnd_4570063 < baseStart_4570063 := by decide
  rcases family_descends (prefixWord ++ tailWord_4570063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4570133 : List Nat := [1, 3, 2, 1, 4, 1, 2, 1, 4, 1, 3]
def baseStart_4570133 : Nat := 118140960795 + 4570133 * 2 ^ 59
def prefixEnd_4570133 : Nat := 4983230072969 + 3 ^ 40 * 4570133 * 2
def baseEnd_4570133 : Nat := 2346674883974273067319847

theorem tailTrace_4570133 : CollatzResearch.WordTrace tailWord_4570133 prefixEnd_4570133 2346674883974273067319847 := by
  unfold tailWord_4570133
  simp only [CollatzResearch.WordTrace]
  refine ⟨166686444352196132421411053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111124296234797421614274035 166686444352196132421411053)
  ·
    refine ⟨62507416632073549658029145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 166686444352196132421411053 62507416632073549658029145)
    ·
      refine ⟨46880562474055162243521859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62507416632073549658029145 46880562474055162243521859)
      ·
        refine ⟨70320843711082743365282789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46880562474055162243521859 70320843711082743365282789)
        ·
          refine ⟨13185158195828014380990523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 70320843711082743365282789 13185158195828014380990523)
          ·
            refine ⟨19777737293742021571485785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13185158195828014380990523 19777737293742021571485785)
            ·
              refine ⟨14833302970306516178614339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19777737293742021571485785 14833302970306516178614339)
              ·
                refine ⟨22249954455459774267921509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14833302970306516178614339 22249954455459774267921509)
                ·
                  refine ⟨4171866460398707675235283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22249954455459774267921509 4171866460398707675235283)
                  ·
                    refine ⟨6257799690598061512852925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4171866460398707675235283 6257799690598061512852925)
                    ·
                      refine ⟨2346674883974273067319847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6257799690598061512852925 2346674883974273067319847)
                      ·
                        rfl

theorem cell23_4570133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 2, 1, 4, 1, 3].length) (baseStart_4570133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4570133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4570133 prefixEnd_4570133 := by exact prefixLift 4570133
  have htrace : WordTrace (prefixWord ++ tailWord_4570133) baseStart_4570133 baseEnd_4570133 := by
    simpa [prefixWord, tailWord_4570133, baseEnd_4570133] using wordTrace_append hprefix tailTrace_4570133
  have hstable : (prefixWord ++ tailWord_4570133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4570133).length < 2 ^ (prefixWord ++ tailWord_4570133).sum := by decide
  have hdescent : baseEnd_4570133 < baseStart_4570133 := by decide
  rcases family_descends (prefixWord ++ tailWord_4570133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4570144 : List Nat := [2, 1, 1, 7, 2, 1, 2, 1, 2, 4]
def baseStart_4570144 : Nat := 118140960795 + 4570144 * 2 ^ 59
def prefixEnd_4570144 : Nat := 4983230072969 + 3 ^ 40 * 4570144 * 2
def baseEnd_4570144 : Nat := 782226844087157508094099

theorem tailTrace_4570144 : CollatzResearch.WordTrace tailWord_4570144 prefixEnd_4570144 782226844087157508094099 := by
  unfold tailWord_4570144
  simp only [CollatzResearch.WordTrace]
  refine ⟨83343422777578140650030743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111124563703437520866707657 83343422777578140650030743)
  ·
    refine ⟨125015134166367210975046115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83343422777578140650030743 125015134166367210975046115)
    ·
      refine ⟨187522701249550816462569173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125015134166367210975046115 187522701249550816462569173)
      ·
        refine ⟨4395063310536347260841465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 187522701249550816462569173 4395063310536347260841465)
        ·
          refine ⟨3296297482902260445631099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4395063310536347260841465 3296297482902260445631099)
          ·
            refine ⟨4944446224353390668446649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3296297482902260445631099 4944446224353390668446649)
            ·
              refine ⟨3708334668265043001334987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4944446224353390668446649 3708334668265043001334987)
              ·
                refine ⟨5562502002397564502002481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3708334668265043001334987 5562502002397564502002481)
                ·
                  refine ⟨4171876501798173376501861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5562502002397564502002481 4171876501798173376501861)
                  ·
                    refine ⟨782226844087157508094099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4171876501798173376501861 782226844087157508094099)
                    ·
                      rfl

theorem cell23_4570144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 2, 1, 2, 1, 2, 4].length) (baseStart_4570144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4570144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4570144 prefixEnd_4570144 := by exact prefixLift 4570144
  have htrace : WordTrace (prefixWord ++ tailWord_4570144) baseStart_4570144 baseEnd_4570144 := by
    simpa [prefixWord, tailWord_4570144, baseEnd_4570144] using wordTrace_append hprefix tailTrace_4570144
  have hstable : (prefixWord ++ tailWord_4570144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4570144).length < 2 ^ (prefixWord ++ tailWord_4570144).sum := by decide
  have hdescent : baseEnd_4570144 < baseStart_4570144 := by decide
  rcases family_descends (prefixWord ++ tailWord_4570144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4570149 : List Nat := [1, 3, 1, 2, 2, 2, 2, 1, 1, 8]
def baseStart_4570149 : Nat := 118140960795 + 4570149 * 2 ^ 59
def prefixEnd_4570149 : Nat := 4983230072969 + 3 ^ 40 * 4570149 * 2
def baseEnd_4570149 : Nat := 782227699888248334906591

theorem tailTrace_4570149 : CollatzResearch.WordTrace tailWord_4570149 prefixEnd_4570149 782227699888248334906591 := by
  unfold tailWord_4570149
  simp only [CollatzResearch.WordTrace]
  refine ⟨166687027920138167153993501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111124685280092111435995667 166687027920138167153993501)
  ·
    refine ⟨62507635470051812682747563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 166687027920138167153993501 62507635470051812682747563)
    ·
      refine ⟨93761453205077719024121345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62507635470051812682747563 93761453205077719024121345)
      ·
        refine ⟨70321089903808289268091009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 93761453205077719024121345 70321089903808289268091009)
        ·
          refine ⟨52740817427856216951068257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 70321089903808289268091009 52740817427856216951068257)
          ·
            refine ⟨39555613070892162713301193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52740817427856216951068257 39555613070892162713301193)
            ·
              refine ⟨29666709803169122034975895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39555613070892162713301193 29666709803169122034975895)
              ·
                refine ⟨44500064704753683052463843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29666709803169122034975895 44500064704753683052463843)
                ·
                  refine ⟨66750097057130524578695765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 44500064704753683052463843 66750097057130524578695765)
                  ·
                    refine ⟨782227699888248334906591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 66750097057130524578695765 782227699888248334906591)
                    ·
                      rfl

theorem cell23_4570149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 2, 1, 1, 8].length) (baseStart_4570149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4570149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4570149 prefixEnd_4570149 := by exact prefixLift 4570149
  have htrace : WordTrace (prefixWord ++ tailWord_4570149) baseStart_4570149 baseEnd_4570149 := by
    simpa [prefixWord, tailWord_4570149, baseEnd_4570149] using wordTrace_append hprefix tailTrace_4570149
  have hstable : (prefixWord ++ tailWord_4570149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4570149).length < 2 ^ (prefixWord ++ tailWord_4570149).sum := by decide
  have hdescent : baseEnd_4570149 < baseStart_4570149 := by decide
  rcases family_descends (prefixWord ++ tailWord_4570149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4570173 : List Nat := [1, 4, 1, 3, 1, 2, 1, 1, 3, 4, 2]
def baseStart_4570173 : Nat := 118140960795 + 4570173 * 2 ^ 59
def prefixEnd_4570173 : Nat := 4983230072969 + 3 ^ 40 * 4570173 * 2
def baseEnd_4570173 : Nat := 2346695423200452910819663

theorem tailTrace_4570173 : CollatzResearch.WordTrace tailWord_4570173 prefixEnd_4570173 2346695423200452910819663 := by
  unfold tailWord_4570173
  simp only [CollatzResearch.WordTrace]
  refine ⟨166687903272051219252867173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111125268848034146168578115 166687903272051219252867173)
  ·
    refine ⟨31253981863509603609912595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 166687903272051219252867173 31253981863509603609912595)
    ·
      refine ⟨46880972795264405414868893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31253981863509603609912595 46880972795264405414868893)
      ·
        refine ⟨17580364798224152030575835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46880972795264405414868893 17580364798224152030575835)
        ·
          refine ⟨26370547197336228045863753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17580364798224152030575835 26370547197336228045863753)
          ·
            refine ⟨19777910398002171034397815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26370547197336228045863753 19777910398002171034397815)
            ·
              refine ⟨29666865597003256551596723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19777910398002171034397815 29666865597003256551596723)
              ·
                refine ⟨44500298395504884827395085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29666865597003256551596723 44500298395504884827395085)
                ·
                  refine ⟨16687611898314331810273157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 44500298395504884827395085 16687611898314331810273157)
                  ·
                    refine ⟨3128927230933937214426217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16687611898314331810273157 3128927230933937214426217)
                    ·
                      refine ⟨2346695423200452910819663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3128927230933937214426217 2346695423200452910819663)
                      ·
                        rfl

theorem cell23_4570173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 1, 1, 3, 4, 2].length) (baseStart_4570173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4570173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4570173 prefixEnd_4570173 := by exact prefixLift 4570173
  have htrace : WordTrace (prefixWord ++ tailWord_4570173) baseStart_4570173 baseEnd_4570173 := by
    simpa [prefixWord, tailWord_4570173, baseEnd_4570173] using wordTrace_append hprefix tailTrace_4570173
  have hstable : (prefixWord ++ tailWord_4570173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4570173).length < 2 ^ (prefixWord ++ tailWord_4570173).sum := by decide
  have hdescent : baseEnd_4570173 < baseStart_4570173 := by decide
  rcases family_descends (prefixWord ++ tailWord_4570173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4570199 : List Nat := [1, 1, 3, 2, 2, 1, 1, 1, 2, 1, 8]
def baseStart_4570199 : Nat := 118140960795 + 4570199 * 2 ^ 59
def prefixEnd_4570199 : Nat := 4983230072969 + 3 ^ 40 * 4570199 * 2
def baseEnd_4570199 : Nat := 2346708773697469809094543

theorem tailTrace_4570199 : CollatzResearch.WordTrace tailWord_4570199 prefixEnd_4570199 2346708773697469809094543 := by
  unfold tailWord_4570199
  simp only [CollatzResearch.WordTrace]
  refine ⟨166688851569957025693313651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111125901046638017128875767 166688851569957025693313651)
  ·
    refine ⟨250033277354935538539970477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 166688851569957025693313651 250033277354935538539970477)
    ·
      refine ⟨93762479008100826952488929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 250033277354935538539970477 93762479008100826952488929)
      ·
        refine ⟨70321859256075620214366697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 93762479008100826952488929 70321859256075620214366697)
        ·
          refine ⟨52741394442056715160775023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 70321859256075620214366697 52741394442056715160775023)
          ·
            refine ⟨79112091663085072741162535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52741394442056715160775023 79112091663085072741162535)
            ·
              refine ⟨118668137494627609111743803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 79112091663085072741162535 118668137494627609111743803)
              ·
                refine ⟨178002206241941413667615705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 118668137494627609111743803 178002206241941413667615705)
                ·
                  refine ⟨133501654681456060250711779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 178002206241941413667615705 133501654681456060250711779)
                  ·
                    refine ⟨200252482022184090376067669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 133501654681456060250711779 200252482022184090376067669)
                    ·
                      refine ⟨2346708773697469809094543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 200252482022184090376067669 2346708773697469809094543)
                      ·
                        rfl

theorem cell23_4570199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 1, 2, 1, 8].length) (baseStart_4570199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4570199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4570199 prefixEnd_4570199 := by exact prefixLift 4570199
  have htrace : WordTrace (prefixWord ++ tailWord_4570199) baseStart_4570199 baseEnd_4570199 := by
    simpa [prefixWord, tailWord_4570199, baseEnd_4570199] using wordTrace_append hprefix tailTrace_4570199
  have hstable : (prefixWord ++ tailWord_4570199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4570199).length < 2 ^ (prefixWord ++ tailWord_4570199).sum := by decide
  have hdescent : baseEnd_4570199 < baseStart_4570199 := by decide
  rcases family_descends (prefixWord ++ tailWord_4570199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4570219 : List Nat := [1, 1, 1, 1, 2, 2, 1, 1, 2, 6, 5]
def baseStart_4570219 : Nat := 118140960795 + 4570219 * 2 ^ 59
def prefixEnd_4570219 : Nat := 4983230072969 + 3 ^ 40 * 4570219 * 2
def baseEnd_4570219 : Nat := 2346719043310559730844451

theorem tailTrace_4570219 : CollatzResearch.WordTrace tailWord_4570219 prefixEnd_4570219 2346719043310559730844451 := by
  unfold tailWord_4570219
  simp only [CollatzResearch.WordTrace]
  refine ⟨166689581029884569109041711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111126387353256379406027807 166689581029884569109041711)
  ·
    refine ⟨250034371544826853663562567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 166689581029884569109041711 250034371544826853663562567)
    ·
      refine ⟨375051557317240280495343851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 250034371544826853663562567 375051557317240280495343851)
      ·
        refine ⟨562577335975860420743015777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 375051557317240280495343851 562577335975860420743015777)
        ·
          refine ⟨421933001981895315557261833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 562577335975860420743015777 421933001981895315557261833)
          ·
            refine ⟨316449751486421486667946375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 421933001981895315557261833 316449751486421486667946375)
            ·
              refine ⟨474674627229632230001919563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 316449751486421486667946375 474674627229632230001919563)
              ·
                refine ⟨712011940844448345002879345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 474674627229632230001919563 712011940844448345002879345)
                ·
                  refine ⟨534008955633336258752159509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 712011940844448345002879345 534008955633336258752159509)
                  ·
                    refine ⟨25031669795312637129007477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 534008955633336258752159509 25031669795312637129007477)
                    ·
                      refine ⟨2346719043310559730844451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25031669795312637129007477 2346719043310559730844451)
                      ·
                        rfl

theorem cell23_4570219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 1, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 1, 2, 6, 5].length) (baseStart_4570219 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4570219 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4570219 prefixEnd_4570219 := by exact prefixLift 4570219
  have htrace : WordTrace (prefixWord ++ tailWord_4570219) baseStart_4570219 baseEnd_4570219 := by
    simpa [prefixWord, tailWord_4570219, baseEnd_4570219] using wordTrace_append hprefix tailTrace_4570219
  have hstable : (prefixWord ++ tailWord_4570219).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4570219).length < 2 ^ (prefixWord ++ tailWord_4570219).sum := by decide
  have hdescent : baseEnd_4570219 < baseStart_4570219 := by decide
  rcases family_descends (prefixWord ++ tailWord_4570219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4570226 : List Nat := [3, 2, 1, 2, 2, 1, 3, 1, 1, 7]
def baseStart_4570226 : Nat := 118140960795 + 4570226 * 2 ^ 59
def prefixEnd_4570226 : Nat := 4983230072969 + 3 ^ 40 * 4570226 * 2
def baseEnd_4570226 : Nat := 782240879225047067818973

theorem tailTrace_4570226 : CollatzResearch.WordTrace tailWord_4570226 prefixEnd_4570226 782240879225047067818973 := by
  unfold tailWord_4570226
  simp only [CollatzResearch.WordTrace]
  refine ⟨41672459085214802326136633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 111126557560572806203031021 41672459085214802326136633)
  ·
    refine ⟨31254344313911101744602475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41672459085214802326136633 31254344313911101744602475)
    ·
      refine ⟨46881516470866652616903713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31254344313911101744602475 46881516470866652616903713)
      ·
        refine ⟨35161137353149989462677785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46881516470866652616903713 35161137353149989462677785)
        ·
          refine ⟨26370853014862492097008339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35161137353149989462677785 26370853014862492097008339)
          ·
            refine ⟨39556279522293738145512509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26370853014862492097008339 39556279522293738145512509)
            ·
              refine ⟨14833604820860151804567191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 39556279522293738145512509 14833604820860151804567191)
              ·
                refine ⟨22250407231290227706850787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14833604820860151804567191 22250407231290227706850787)
                ·
                  refine ⟨33375610846935341560276181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22250407231290227706850787 33375610846935341560276181)
                  ·
                    refine ⟨782240879225047067818973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 33375610846935341560276181 782240879225047067818973)
                    ·
                      rfl

theorem cell23_4570226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 3, 1, 1, 7].length) (baseStart_4570226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4570226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4570226 prefixEnd_4570226 := by exact prefixLift 4570226
  have htrace : WordTrace (prefixWord ++ tailWord_4570226) baseStart_4570226 baseEnd_4570226 := by
    simpa [prefixWord, tailWord_4570226, baseEnd_4570226] using wordTrace_append hprefix tailTrace_4570226
  have hstable : (prefixWord ++ tailWord_4570226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4570226).length < 2 ^ (prefixWord ++ tailWord_4570226).sum := by decide
  have hdescent : baseEnd_4570226 < baseStart_4570226 := by decide
  rcases family_descends (prefixWord ++ tailWord_4570226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4570230 : List Nat := [5, 1, 1, 2, 1, 1, 4, 3, 5]
def baseStart_4570230 : Nat := 118140960795 + 4570230 * 2 ^ 59
def prefixEnd_4570230 : Nat := 4983230072969 + 3 ^ 40 * 4570230 * 2
def baseEnd_4570230 : Nat := 260747187955306576422989

theorem tailTrace_4570230 : CollatzResearch.WordTrace tailWord_4570230 prefixEnd_4570230 260747187955306576422989 := by
  unfold tailWord_4570230
  simp only [CollatzResearch.WordTrace]
  refine ⟨10418123889552794874230759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 111126654821896478658461429 10418123889552794874230759)
  ·
    refine ⟨15627185834329192311346139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10418123889552794874230759 15627185834329192311346139)
    ·
      refine ⟨23440778751493788467019209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15627185834329192311346139 23440778751493788467019209)
      ·
        refine ⟨17580584063620341350264407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23440778751493788467019209 17580584063620341350264407)
        ·
          refine ⟨26370876095430512025396611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17580584063620341350264407 26370876095430512025396611)
          ·
            refine ⟨39556314143145768038094917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26370876095430512025396611 39556314143145768038094917)
            ·
              refine ⟨7416808901839831507142797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 39556314143145768038094917 7416808901839831507142797)
              ·
                refine ⟨2781303338189936815178549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7416808901839831507142797 2781303338189936815178549)
                ·
                  refine ⟨260747187955306576422989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2781303338189936815178549 260747187955306576422989)
                  ·
                    rfl

theorem cell23_4570230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 4, 3, 5].length) (baseStart_4570230 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4570230 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4570230 prefixEnd_4570230 := by exact prefixLift 4570230
  have htrace : WordTrace (prefixWord ++ tailWord_4570230) baseStart_4570230 baseEnd_4570230 := by
    simpa [prefixWord, tailWord_4570230, baseEnd_4570230] using wordTrace_append hprefix tailTrace_4570230
  have hstable : (prefixWord ++ tailWord_4570230).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4570230).length < 2 ^ (prefixWord ++ tailWord_4570230).sum := by decide
  have hdescent : baseEnd_4570230 < baseStart_4570230 := by decide
  rcases family_descends (prefixWord ++ tailWord_4570230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4570239 : List Nat := [1, 1, 2, 2, 1, 1, 1, 1, 3, 10]
def baseStart_4570239 : Nat := 118140960795 + 4570239 * 2 ^ 59
def prefixEnd_4570239 : Nat := 4983230072969 + 3 ^ 40 * 4570239 * 2
def baseEnd_4570239 : Nat := 782243104307883217531453

theorem tailTrace_4570239 : CollatzResearch.WordTrace tailWord_4570239 prefixEnd_4570239 782243104307883217531453 := by
  unfold tailWord_4570239
  simp only [CollatzResearch.WordTrace]
  refine ⟨166690310489812112524769771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111126873659874741683179847 166690310489812112524769771)
  ·
    refine ⟨250035465734718168787154657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 166690310489812112524769771 250035465734718168787154657)
    ·
      refine ⟨187526599301038626590365993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 250035465734718168787154657 187526599301038626590365993)
      ·
        refine ⟨140644949475778969942774495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 187526599301038626590365993 140644949475778969942774495)
        ·
          refine ⟨210967424213668454914161743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 140644949475778969942774495 210967424213668454914161743)
          ·
            refine ⟨316451136320502682371242615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 210967424213668454914161743 316451136320502682371242615)
            ·
              refine ⟨474676704480754023556863923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 316451136320502682371242615 474676704480754023556863923)
              ·
                refine ⟨712015056721131035335295885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 474676704480754023556863923 712015056721131035335295885)
                ·
                  refine ⟨267005646270424138250735957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 712015056721131035335295885 267005646270424138250735957)
                  ·
                    refine ⟨782243104307883217531453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 267005646270424138250735957 782243104307883217531453)
                    ·
                      rfl

theorem cell23_4570239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 1, 3, 10].length) (baseStart_4570239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4570239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4570239 prefixEnd_4570239 := by exact prefixLift 4570239
  have htrace : WordTrace (prefixWord ++ tailWord_4570239) baseStart_4570239 baseEnd_4570239 := by
    simpa [prefixWord, tailWord_4570239, baseEnd_4570239] using wordTrace_append hprefix tailTrace_4570239
  have hstable : (prefixWord ++ tailWord_4570239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4570239).length < 2 ^ (prefixWord ++ tailWord_4570239).sum := by decide
  have hdescent : baseEnd_4570239 < baseStart_4570239 := by decide
  rcases family_descends (prefixWord ++ tailWord_4570239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4570273 : List Nat := [1, 2, 3, 3, 1, 1, 1, 4, 3, 4]
def baseStart_4570273 : Nat := 118140960795 + 4570273 * 2 ^ 59
def prefixEnd_4570273 : Nat := 4983230072969 + 3 ^ 40 * 4570273 * 2
def baseEnd_4570273 : Nat := 782248923755300839856401

theorem tailTrace_4570273 : CollatzResearch.WordTrace tailWord_4570273 prefixEnd_4570273 782248923755300839856401 := by
  unfold tailWord_4570273
  simp only [CollatzResearch.WordTrace]
  refine ⟨166691550571688936331507473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111127700381125957554338315 166691550571688936331507473)
  ·
    refine ⟨125018662928766702248630605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 166691550571688936331507473 125018662928766702248630605)
    ·
      refine ⟨46881998598287513343236477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 125018662928766702248630605 46881998598287513343236477)
      ·
        refine ⟨17580749474357817503713679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46881998598287513343236477 17580749474357817503713679)
        ·
          refine ⟨26371124211536726255570519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17580749474357817503713679 26371124211536726255570519)
          ·
            refine ⟨39556686317305089383355779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26371124211536726255570519 39556686317305089383355779)
            ·
              refine ⟨59335029475957634075033669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39556686317305089383355779 59335029475957634075033669)
              ·
                refine ⟨11125318026742056389068813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 59335029475957634075033669 11125318026742056389068813)
                ·
                  refine ⟨4171994260028271145900805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11125318026742056389068813 4171994260028271145900805)
                  ·
                    refine ⟨782248923755300839856401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4171994260028271145900805 782248923755300839856401)
                    ·
                      rfl

theorem cell23_4570273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 1, 4, 3, 4].length) (baseStart_4570273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4570273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4570273 prefixEnd_4570273 := by exact prefixLift 4570273
  have htrace : WordTrace (prefixWord ++ tailWord_4570273) baseStart_4570273 baseEnd_4570273 := by
    simpa [prefixWord, tailWord_4570273, baseEnd_4570273] using wordTrace_append hprefix tailTrace_4570273
  have hstable : (prefixWord ++ tailWord_4570273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4570273).length < 2 ^ (prefixWord ++ tailWord_4570273).sum := by decide
  have hdescent : baseEnd_4570273 < baseStart_4570273 := by decide
  rcases family_descends (prefixWord ++ tailWord_4570273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4570300 : List Nat := [2, 2, 2, 3, 2, 2, 1, 2, 2, 2, 3]
def baseStart_4570300 : Nat := 118140960795 + 4570300 * 2 ^ 59
def prefixEnd_4570300 : Nat := 4983230072969 + 3 ^ 40 * 4570300 * 2
def baseEnd_4570300 : Nat := 2346760635243573913931579

theorem tailTrace_4570300 : CollatzResearch.WordTrace tailWord_4570300 prefixEnd_4570300 2346760635243573913931579 := by
  unfold tailWord_4570300
  simp only [CollatzResearch.WordTrace]
  refine ⟨83346267671295559971370177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111128356895060746628493569 83346267671295559971370177)
  ·
    refine ⟨62509700753471669978527633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83346267671295559971370177 62509700753471669978527633)
    ·
      refine ⟨46882275565103752483895725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62509700753471669978527633 46882275565103752483895725)
      ·
        refine ⟨17580853336913907181460897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46882275565103752483895725 17580853336913907181460897)
        ·
          refine ⟨13185640002685430386095673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17580853336913907181460897 13185640002685430386095673)
          ·
            refine ⟨9889230002014072789571755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13185640002685430386095673 9889230002014072789571755)
            ·
              refine ⟨14833845003021109184357633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9889230002014072789571755 14833845003021109184357633)
              ·
                refine ⟨11125383752265831888268225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14833845003021109184357633 11125383752265831888268225)
                ·
                  refine ⟨8344037814199373916201169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11125383752265831888268225 8344037814199373916201169)
                  ·
                    refine ⟨6258028360649530437150877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8344037814199373916201169 6258028360649530437150877)
                    ·
                      refine ⟨2346760635243573913931579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6258028360649530437150877 2346760635243573913931579)
                      ·
                        rfl

theorem cell23_4570300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 2, 1, 2, 2, 2, 3].length) (baseStart_4570300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4570300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4570300 prefixEnd_4570300 := by exact prefixLift 4570300
  have htrace : WordTrace (prefixWord ++ tailWord_4570300) baseStart_4570300 baseEnd_4570300 := by
    simpa [prefixWord, tailWord_4570300, baseEnd_4570300] using wordTrace_append hprefix tailTrace_4570300
  have hstable : (prefixWord ++ tailWord_4570300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4570300).length < 2 ^ (prefixWord ++ tailWord_4570300).sum := by decide
  have hdescent : baseEnd_4570300 < baseStart_4570300 := by decide
  rcases family_descends (prefixWord ++ tailWord_4570300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4570340 : List Nat := [2, 3, 1, 1, 1, 2, 3, 3, 2, 3, 2]
def baseStart_4570340 : Nat := 118140960795 + 4570340 * 2 ^ 59
def prefixEnd_4570340 : Nat := 4983230072969 + 3 ^ 40 * 4570340 * 2
def baseEnd_4570340 : Nat := 2346781174469753757431395

theorem tailTrace_4570340 : CollatzResearch.WordTrace tailWord_4570340 prefixEnd_4570340 2346781174469753757431395 := by
  unfold tailWord_4570340
  simp only [CollatzResearch.WordTrace]
  refine ⟨83346997131223103387098237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111129329508297471182797649 83346997131223103387098237)
  ·
    refine ⟨31255123924208663770161839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 83346997131223103387098237 31255123924208663770161839)
    ·
      refine ⟨46882685886312995655242759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31255123924208663770161839 46882685886312995655242759)
      ·
        refine ⟨70324028829469493482864139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46882685886312995655242759 70324028829469493482864139)
        ·
          refine ⟨105486043244204240224296209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70324028829469493482864139 105486043244204240224296209)
          ·
            refine ⟨79114532433153180168222157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 105486043244204240224296209 79114532433153180168222157)
            ·
              refine ⟨29667949662432442563083309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 79114532433153180168222157 29667949662432442563083309)
              ·
                refine ⟨11125481123412165961156241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29667949662432442563083309 11125481123412165961156241)
                ·
                  refine ⟨8344110842559124470867181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11125481123412165961156241 8344110842559124470867181)
                  ·
                    refine ⟨3129041565959671676575193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8344110842559124470867181 3129041565959671676575193)
                    ·
                      refine ⟨2346781174469753757431395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3129041565959671676575193 2346781174469753757431395)
                      ·
                        rfl

theorem cell23_4570340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 3, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 3, 3, 2, 3, 2].length) (baseStart_4570340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4570340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4570340 prefixEnd_4570340 := by exact prefixLift 4570340
  have htrace : WordTrace (prefixWord ++ tailWord_4570340) baseStart_4570340 baseEnd_4570340 := by
    simpa [prefixWord, tailWord_4570340, baseEnd_4570340] using wordTrace_append hprefix tailTrace_4570340
  have hstable : (prefixWord ++ tailWord_4570340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4570340).length < 2 ^ (prefixWord ++ tailWord_4570340).sum := by decide
  have hdescent : baseEnd_4570340 < baseStart_4570340 := by decide
  rcases family_descends (prefixWord ++ tailWord_4570340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4570364 : List Nat := [2, 2, 2, 1, 5, 1, 1, 4, 1, 1, 3]
def baseStart_4570364 : Nat := 118140960795 + 4570364 * 2 ^ 59
def prefixEnd_4570364 : Nat := 4983230072969 + 3 ^ 40 * 4570364 * 2
def baseEnd_4570364 : Nat := 2346793498005461663531285

theorem tailTrace_4570364 : CollatzResearch.WordTrace tailWord_4570364 prefixEnd_4570364 2346793498005461663531285 := by
  unfold tailWord_4570364
  simp only [CollatzResearch.WordTrace]
  refine ⟨83347434807179629436535073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111129913076239505915380097 83347434807179629436535073)
  ·
    refine ⟨62510576105384722077401305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83347434807179629436535073 62510576105384722077401305)
    ·
      refine ⟨46882932079038541558050979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62510576105384722077401305 46882932079038541558050979)
      ·
        refine ⟨70324398118557812337076469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46882932079038541558050979 70324398118557812337076469)
        ·
          refine ⟨6592912323614794906600919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 70324398118557812337076469 6592912323614794906600919)
          ·
            refine ⟨9889368485422192359901379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6592912323614794906600919 9889368485422192359901379)
            ·
              refine ⟨14834052728133288539852069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9889368485422192359901379 14834052728133288539852069)
              ·
                refine ⟨2781384886524991601222263, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14834052728133288539852069 2781384886524991601222263)
                ·
                  refine ⟨4172077329787487401833395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2781384886524991601222263 4172077329787487401833395)
                  ·
                    refine ⟨6258115994681231102750093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4172077329787487401833395 6258115994681231102750093)
                    ·
                      refine ⟨2346793498005461663531285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6258115994681231102750093 2346793498005461663531285)
                      ·
                        rfl

theorem cell23_4570364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 1, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 1, 1, 4, 1, 1, 3].length) (baseStart_4570364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4570364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4570364 prefixEnd_4570364 := by exact prefixLift 4570364
  have htrace : WordTrace (prefixWord ++ tailWord_4570364) baseStart_4570364 baseEnd_4570364 := by
    simpa [prefixWord, tailWord_4570364, baseEnd_4570364] using wordTrace_append hprefix tailTrace_4570364
  have hstable : (prefixWord ++ tailWord_4570364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4570364).length < 2 ^ (prefixWord ++ tailWord_4570364).sum := by decide
  have hdescent : baseEnd_4570364 < baseStart_4570364 := by decide
  rcases family_descends (prefixWord ++ tailWord_4570364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4570373 : List Nat := [1, 3, 1, 1, 2, 1, 3, 1, 5, 2, 3]
def baseStart_4570373 : Nat := 118140960795 + 4570373 * 2 ^ 59
def prefixEnd_4570373 : Nat := 4983230072969 + 3 ^ 40 * 4570373 * 2
def baseEnd_4570373 : Nat := 2346798119331352128318743

theorem tailTrace_4570373 : CollatzResearch.WordTrace tailWord_4570373 prefixEnd_4570373 2346798119331352128318743 := by
  unfold tailWord_4570373
  simp only [CollatzResearch.WordTrace]
  refine ⟨166695197871326653410147773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111130131914217768940098515 166695197871326653410147773)
  ·
    refine ⟨62510699201747495028805415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 166695197871326653410147773 62510699201747495028805415)
    ·
      refine ⟨93766048802621242543208123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62510699201747495028805415 93766048802621242543208123)
      ·
        refine ⟨140649073203931863814812185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93766048802621242543208123 140649073203931863814812185)
        ·
          refine ⟨105486804902948897861109139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 140649073203931863814812185 105486804902948897861109139)
          ·
            refine ⟨158230207354423346791663709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 105486804902948897861109139 158230207354423346791663709)
            ·
              refine ⟨59336327757908755046873891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 158230207354423346791663709 59336327757908755046873891)
              ·
                refine ⟨89004491636863132570310837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 59336327757908755046873891 89004491636863132570310837)
                ·
                  refine ⟨8344171090955918678466641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 89004491636863132570310837 8344171090955918678466641)
                  ·
                    refine ⟨6258128318216939008849981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8344171090955918678466641 6258128318216939008849981)
                    ·
                      refine ⟨2346798119331352128318743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6258128318216939008849981 2346798119331352128318743)
                      ·
                        rfl

theorem cell23_4570373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 3, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 3, 1, 5, 2, 3].length) (baseStart_4570373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4570373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4570373 prefixEnd_4570373 := by exact prefixLift 4570373
  have htrace : WordTrace (prefixWord ++ tailWord_4570373) baseStart_4570373 baseEnd_4570373 := by
    simpa [prefixWord, tailWord_4570373, baseEnd_4570373] using wordTrace_append hprefix tailTrace_4570373
  have hstable : (prefixWord ++ tailWord_4570373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4570373).length < 2 ^ (prefixWord ++ tailWord_4570373).sum := by decide
  have hdescent : baseEnd_4570373 < baseStart_4570373 := by decide
  rcases family_descends (prefixWord ++ tailWord_4570373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4570380 : List Nat := [2, 2, 1, 2, 2, 3, 2, 3, 2, 4]
def baseStart_4570380 : Nat := 118140960795 + 4570380 * 2 ^ 59
def prefixEnd_4570380 : Nat := 4983230072969 + 3 ^ 40 * 4570380 * 2
def baseEnd_4570380 : Nat := 782267237898644533643737

theorem tailTrace_4570380 : CollatzResearch.WordTrace tailWord_4570380 prefixEnd_4570380 782267237898644533643737 := by
  unfold tailWord_4570380
  simp only [CollatzResearch.WordTrace]
  refine ⟨83347726591150646802826297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111130302121534195737101729 83347726591150646802826297)
  ·
    refine ⟨62510794943362985102119723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83347726591150646802826297 62510794943362985102119723)
    ·
      refine ⟨93766192415044477653179585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62510794943362985102119723 93766192415044477653179585)
      ·
        refine ⟨70324644311283358239884689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 93766192415044477653179585 70324644311283358239884689)
        ·
          refine ⟨52743483233462518679913517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 70324644311283358239884689 52743483233462518679913517)
          ·
            refine ⟨19778806212548444504967569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 52743483233462518679913517 19778806212548444504967569)
            ·
              refine ⟨14834104659411333378725677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19778806212548444504967569 14834104659411333378725677)
              ·
                refine ⟨5562789247279250017022129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14834104659411333378725677 5562789247279250017022129)
                ·
                  refine ⟨4172091935459437512766597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5562789247279250017022129 4172091935459437512766597)
                  ·
                    refine ⟨782267237898644533643737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4172091935459437512766597 782267237898644533643737)
                    ·
                      rfl

theorem cell23_4570380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 2, 3, 2, 4].length) (baseStart_4570380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4570380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4570380 prefixEnd_4570380 := by exact prefixLift 4570380
  have htrace : WordTrace (prefixWord ++ tailWord_4570380) baseStart_4570380 baseEnd_4570380 := by
    simpa [prefixWord, tailWord_4570380, baseEnd_4570380] using wordTrace_append hprefix tailTrace_4570380
  have hstable : (prefixWord ++ tailWord_4570380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4570380).length < 2 ^ (prefixWord ++ tailWord_4570380).sum := by decide
  have hdescent : baseEnd_4570380 < baseStart_4570380 := by decide
  rcases family_descends (prefixWord ++ tailWord_4570380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4570398 : List Nat := [4, 3, 2, 1, 2, 1, 2, 3, 1, 1, 3]
def baseStart_4570398 : Nat := 118140960795 + 4570398 * 2 ^ 59
def prefixEnd_4570398 : Nat := 4983230072969 + 3 ^ 40 * 4570398 * 2
def baseEnd_4570398 : Nat := 2346810956347714530506129

theorem tailTrace_4570398 : CollatzResearch.WordTrace tailWord_4570398 prefixEnd_4570398 2346810956347714530506129 := by
  unfold tailWord_4570398
  simp only [CollatzResearch.WordTrace]
  refine ⟨20837013712029510334975981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 111130739797490721786538565 20837013712029510334975981)
  ·
    refine ⟨7813880142011066375615993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20837013712029510334975981 7813880142011066375615993)
    ·
      refine ⟨5860410106508299781711995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7813880142011066375615993 5860410106508299781711995)
      ·
        refine ⟨8790615159762449672567993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5860410106508299781711995 8790615159762449672567993)
        ·
          refine ⟨6592961369821837254425995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8790615159762449672567993 6592961369821837254425995)
          ·
            refine ⟨9889442054732755881638993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6592961369821837254425995 9889442054732755881638993)
            ·
              refine ⟨7417081541049566911229245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9889442054732755881638993 7417081541049566911229245)
              ·
                refine ⟨2781405577893587591710967, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7417081541049566911229245 2781405577893587591710967)
                ·
                  refine ⟨4172108366840381387566451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2781405577893587591710967 4172108366840381387566451)
                  ·
                    refine ⟨6258162550260572081349677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4172108366840381387566451 6258162550260572081349677)
                    ·
                      refine ⟨2346810956347714530506129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6258162550260572081349677 2346810956347714530506129)
                      ·
                        rfl

theorem cell23_4570398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 1, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 1, 2, 3, 1, 1, 3].length) (baseStart_4570398 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4570398 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4570398 prefixEnd_4570398 := by exact prefixLift 4570398
  have htrace : WordTrace (prefixWord ++ tailWord_4570398) baseStart_4570398 baseEnd_4570398 := by
    simpa [prefixWord, tailWord_4570398, baseEnd_4570398] using wordTrace_append hprefix tailTrace_4570398
  have hstable : (prefixWord ++ tailWord_4570398).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4570398).length < 2 ^ (prefixWord ++ tailWord_4570398).sum := by decide
  have hdescent : baseEnd_4570398 < baseStart_4570398 := by decide
  rcases family_descends (prefixWord ++ tailWord_4570398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4570463 : List Nat := [1, 1, 2, 3, 1, 2, 1, 2, 1, 6, 3]
def baseStart_4570463 : Nat := 118140960795 + 4570463 * 2 ^ 59
def prefixEnd_4570463 : Nat := 4983230072969 + 3 ^ 40 * 4570463 * 2
def baseEnd_4570463 : Nat := 2346844332590256776193329

theorem tailTrace_4570463 : CollatzResearch.WordTrace tailWord_4570463 prefixEnd_4570463 2346844332590256776193329 := by
  unfold tailWord_4570463
  simp only [CollatzResearch.WordTrace]
  refine ⟨166698480441000598780924043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111132320294000399187282695 166698480441000598780924043)
  ·
    refine ⟨250047720661500898171386065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 166698480441000598780924043 250047720661500898171386065)
    ·
      refine ⟨187535790496125673628539549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 250047720661500898171386065 187535790496125673628539549)
      ·
        refine ⟨70325921436047127610702331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 187535790496125673628539549 70325921436047127610702331)
        ·
          refine ⟨105488882154070691416053497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70325921436047127610702331 105488882154070691416053497)
          ·
            refine ⟨79116661615553018562040123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 105488882154070691416053497 79116661615553018562040123)
            ·
              refine ⟨118674992423329527843060185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 79116661615553018562040123 118674992423329527843060185)
              ·
                refine ⟨89006244317497145882295139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 118674992423329527843060185 89006244317497145882295139)
                ·
                  refine ⟨133509366476245718823442709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 89006244317497145882295139 133509366476245718823442709)
                  ·
                    refine ⟨6258251553574018069848877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 133509366476245718823442709 6258251553574018069848877)
                    ·
                      refine ⟨2346844332590256776193329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6258251553574018069848877 2346844332590256776193329)
                      ·
                        rfl

theorem cell23_4570463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 2, 1, 6, 3].length) (baseStart_4570463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4570463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4570463 prefixEnd_4570463 := by exact prefixLift 4570463
  have htrace : WordTrace (prefixWord ++ tailWord_4570463) baseStart_4570463 baseEnd_4570463 := by
    simpa [prefixWord, tailWord_4570463, baseEnd_4570463] using wordTrace_append hprefix tailTrace_4570463
  have hstable : (prefixWord ++ tailWord_4570463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4570463).length < 2 ^ (prefixWord ++ tailWord_4570463).sum := by decide
  have hdescent : baseEnd_4570463 < baseStart_4570463 := by decide
  rcases family_descends (prefixWord ++ tailWord_4570463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4570473 : List Nat := [1, 2, 1, 1, 1, 3, 2, 4, 2, 2, 4]
def baseStart_4570473 : Nat := 118140960795 + 4570473 * 2 ^ 59
def prefixEnd_4570473 : Nat := 4983230072969 + 3 ^ 40 * 4570473 * 2
def baseEnd_4570473 : Nat := 2346849467396801737068283

theorem tailTrace_4570473 : CollatzResearch.WordTrace tailWord_4570473 prefixEnd_4570473 2346849467396801737068283 := by
  unfold tailWord_4570473
  simp only [CollatzResearch.WordTrace]
  refine ⟨166698845170964370488788073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111132563447309580325858715 166698845170964370488788073)
  ·
    refine ⟨125024133878223277866591055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 166698845170964370488788073 125024133878223277866591055)
    ·
      refine ⟨187536200817334916799886583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125024133878223277866591055 187536200817334916799886583)
      ·
        refine ⟨281304301226002375199829875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 187536200817334916799886583 281304301226002375199829875)
        ·
          refine ⟨421956451839003562799744813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 281304301226002375199829875 421956451839003562799744813)
          ·
            refine ⟨158233669439626336049904305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 421956451839003562799744813 158233669439626336049904305)
            ·
              refine ⟨118675252079719752037428229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 158233669439626336049904305 118675252079719752037428229)
              ·
                refine ⟨22251609764947453507017793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 118675252079719752037428229 22251609764947453507017793)
                ·
                  refine ⟨16688707323710590130263345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22251609764947453507017793 16688707323710590130263345)
                  ·
                    refine ⟨12516530492782942597697509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16688707323710590130263345 12516530492782942597697509)
                    ·
                      refine ⟨2346849467396801737068283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12516530492782942597697509 2346849467396801737068283)
                      ·
                        rfl

theorem cell23_4570473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 4, 2, 2, 4].length) (baseStart_4570473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4570473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4570473 prefixEnd_4570473 := by exact prefixLift 4570473
  have htrace : WordTrace (prefixWord ++ tailWord_4570473) baseStart_4570473 baseEnd_4570473 := by
    simpa [prefixWord, tailWord_4570473, baseEnd_4570473] using wordTrace_append hprefix tailTrace_4570473
  have hstable : (prefixWord ++ tailWord_4570473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4570473).length < 2 ^ (prefixWord ++ tailWord_4570473).sum := by decide
  have hdescent : baseEnd_4570473 < baseStart_4570473 := by decide
  rcases family_descends (prefixWord ++ tailWord_4570473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4570498 : List Nat := [3, 4, 2, 1, 1, 3, 1, 2, 1, 3, 2]
def baseStart_4570498 : Nat := 118140960795 + 4570498 * 2 ^ 59
def prefixEnd_4570498 : Nat := 4983230072969 + 3 ^ 40 * 4570498 * 2
def baseEnd_4570498 : Nat := 2346862304413164139255669

theorem tailTrace_4570498 : CollatzResearch.WordTrace tailWord_4570498 prefixEnd_4570498 2346862304413164139255669 := by
  unfold tailWord_4570498
  simp only [CollatzResearch.WordTrace]
  refine ⟨41674939248968449939612037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 111133171330582533172298765 41674939248968449939612037)
  ·
    refine ⟨7814051109181584363677257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 41674939248968449939612037 7814051109181584363677257)
    ·
      refine ⟨5860538331886188272757943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7814051109181584363677257 5860538331886188272757943)
      ·
        refine ⟨8790807497829282409136915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5860538331886188272757943 8790807497829282409136915)
        ·
          refine ⟨13186211246743923613705373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8790807497829282409136915 13186211246743923613705373)
          ·
            refine ⟨4944829217528971355139515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13186211246743923613705373 4944829217528971355139515)
            ·
              refine ⟨7417243826293457032709273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4944829217528971355139515 7417243826293457032709273)
              ·
                refine ⟨5562932869720092774531955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7417243826293457032709273 5562932869720092774531955)
                ·
                  refine ⟨8344399304580139161797933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5562932869720092774531955 8344399304580139161797933)
                  ·
                    refine ⟨3129149739217552185674225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8344399304580139161797933 3129149739217552185674225)
                    ·
                      refine ⟨2346862304413164139255669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3129149739217552185674225 2346862304413164139255669)
                      ·
                        rfl

theorem cell23_4570498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 3, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 3, 1, 2, 1, 3, 2].length) (baseStart_4570498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4570498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4570498 prefixEnd_4570498 := by exact prefixLift 4570498
  have htrace : WordTrace (prefixWord ++ tailWord_4570498) baseStart_4570498 baseEnd_4570498 := by
    simpa [prefixWord, tailWord_4570498, baseEnd_4570498] using wordTrace_append hprefix tailTrace_4570498
  have hstable : (prefixWord ++ tailWord_4570498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4570498).length < 2 ^ (prefixWord ++ tailWord_4570498).sum := by decide
  have hdescent : baseEnd_4570498 < baseStart_4570498 := by decide
  rcases family_descends (prefixWord ++ tailWord_4570498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4570513 : List Nat := [1, 2, 2, 1, 1, 1, 2, 2, 6, 5]
def baseStart_4570513 : Nat := 118140960795 + 4570513 * 2 ^ 59
def prefixEnd_4570513 : Nat := 4983230072969 + 3 ^ 40 * 4570513 * 2
def baseEnd_4570513 : Nat := 782290002207660526856033

theorem tailTrace_4570513 : CollatzResearch.WordTrace tailWord_4570513 prefixEnd_4570513 782290002207660526856033 := by
  unfold tailWord_4570513
  simp only [CollatzResearch.WordTrace]
  refine ⟨166700304090819457320244193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111133536060546304880162795 166700304090819457320244193)
  ·
    refine ⟨125025228068114592990183145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 166700304090819457320244193 125025228068114592990183145)
    ·
      refine ⟨93768921051085944742637359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 125025228068114592990183145 93768921051085944742637359)
      ·
        refine ⟨140653381576628917113956039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93768921051085944742637359 140653381576628917113956039)
        ·
          refine ⟨210980072364943375670934059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 140653381576628917113956039 210980072364943375670934059)
          ·
            refine ⟨316470108547415063506401089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 210980072364943375670934059 316470108547415063506401089)
            ·
              refine ⟨237352581410561297629800817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 316470108547415063506401089 237352581410561297629800817)
              ·
                refine ⟨178014436057920973222350613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 237352581410561297629800817 178014436057920973222350613)
                ·
                  refine ⟨8344426690215045619797685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 178014436057920973222350613 8344426690215045619797685)
                  ·
                    refine ⟨782290002207660526856033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8344426690215045619797685 782290002207660526856033)
                    ·
                      rfl

theorem cell23_4570513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 5].length) (baseStart_4570513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4570513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4570513 prefixEnd_4570513 := by exact prefixLift 4570513
  have htrace : WordTrace (prefixWord ++ tailWord_4570513) baseStart_4570513 baseEnd_4570513 := by
    simpa [prefixWord, tailWord_4570513, baseEnd_4570513] using wordTrace_append hprefix tailTrace_4570513
  have hstable : (prefixWord ++ tailWord_4570513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4570513).length < 2 ^ (prefixWord ++ tailWord_4570513).sum := by decide
  have hdescent : baseEnd_4570513 < baseStart_4570513 := by decide
  rcases family_descends (prefixWord ++ tailWord_4570513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4570560 : List Nat := [2, 1, 1, 2, 3, 1, 3, 1, 5, 4]
def baseStart_4570560 : Nat := 118140960795 + 4570560 * 2 ^ 59
def prefixEnd_4570560 : Nat := 4983230072969 + 3 ^ 40 * 4570560 * 2
def baseEnd_4570560 : Nat := 782298046737914298893461

theorem tailTrace_4570560 : CollatzResearch.WordTrace tailWord_4570560 prefixEnd_4570560 782298046737914298893461 := by
  unfold tailWord_4570560
  simp only [CollatzResearch.WordTrace]
  refine ⟨83351009160824592173602567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111134678881099456231470089 83351009160824592173602567)
  ·
    refine ⟨125026513741236888260403851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83351009160824592173602567 125026513741236888260403851)
    ·
      refine ⟨187539770611855332390605777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125026513741236888260403851 187539770611855332390605777)
      ·
        refine ⟨140654827958891499292954333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 187539770611855332390605777 140654827958891499292954333)
        ·
          refine ⟨52745560484584312234857875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 140654827958891499292954333 52745560484584312234857875)
          ·
            refine ⟨79118340726876468352286813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52745560484584312234857875 79118340726876468352286813)
            ·
              refine ⟨29669377772578675632107555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 79118340726876468352286813 29669377772578675632107555)
              ·
                refine ⟨44504066658868013448161333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29669377772578675632107555 44504066658868013448161333)
                ·
                  refine ⟨4172256249268876260765125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 44504066658868013448161333 4172256249268876260765125)
                  ·
                    refine ⟨782298046737914298893461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4172256249268876260765125 782298046737914298893461)
                    ·
                      rfl

theorem cell23_4570560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 3, 1, 5, 4].length) (baseStart_4570560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4570560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4570560 prefixEnd_4570560 := by exact prefixLift 4570560
  have htrace : WordTrace (prefixWord ++ tailWord_4570560) baseStart_4570560 baseEnd_4570560 := by
    simpa [prefixWord, tailWord_4570560, baseEnd_4570560] using wordTrace_append hprefix tailTrace_4570560
  have hstable : (prefixWord ++ tailWord_4570560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4570560).length < 2 ^ (prefixWord ++ tailWord_4570560).sum := by decide
  have hdescent : baseEnd_4570560 < baseStart_4570560 := by decide
  rcases family_descends (prefixWord ++ tailWord_4570560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4570564 : List Nat := [2, 3, 3, 2, 1, 3, 1, 1, 2, 5]
def baseStart_4570564 : Nat := 118140960795 + 4570564 * 2 ^ 59
def prefixEnd_4570564 : Nat := 4983230072969 + 3 ^ 40 * 4570564 * 2
def baseEnd_4570564 : Nat := 782298731378786960343455

theorem tailTrace_4570564 : CollatzResearch.WordTrace tailWord_4570564 prefixEnd_4570564 782298731378786960343455 := by
  unfold tailWord_4570564
  simp only [CollatzResearch.WordTrace]
  refine ⟨83351082106817346515175373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111134776142423128686900497 83351082106817346515175373)
  ·
    refine ⟨31256655790056504943190765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 83351082106817346515175373 31256655790056504943190765)
    ·
      refine ⟨11721245921271189353696537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31256655790056504943190765 11721245921271189353696537)
      ·
        refine ⟨8790934440953392015272403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11721245921271189353696537 8790934440953392015272403)
        ·
          refine ⟨13186401661430088022908605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8790934440953392015272403 13186401661430088022908605)
          ·
            refine ⟨4944900623036283008590727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13186401661430088022908605 4944900623036283008590727)
            ·
              refine ⟨7417350934554424512886091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4944900623036283008590727 7417350934554424512886091)
              ·
                refine ⟨11126026401831636769329137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7417350934554424512886091 11126026401831636769329137)
                ·
                  refine ⟨8344519801373727576996853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11126026401831636769329137 8344519801373727576996853)
                  ·
                    refine ⟨782298731378786960343455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8344519801373727576996853 782298731378786960343455)
                    ·
                      rfl

theorem cell23_4570564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 3, 1, 1, 2, 5].length) (baseStart_4570564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4570564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4570564 prefixEnd_4570564 := by exact prefixLift 4570564
  have htrace : WordTrace (prefixWord ++ tailWord_4570564) baseStart_4570564 baseEnd_4570564 := by
    simpa [prefixWord, tailWord_4570564, baseEnd_4570564] using wordTrace_append hprefix tailTrace_4570564
  have hstable : (prefixWord ++ tailWord_4570564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4570564).length < 2 ^ (prefixWord ++ tailWord_4570564).sum := by decide
  have hdescent : baseEnd_4570564 < baseStart_4570564 := by decide
  rcases family_descends (prefixWord ++ tailWord_4570564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4570603 : List Nat := [1, 1, 1, 1, 2, 3, 2, 1, 2, 9]
def baseStart_4570603 : Nat := 118140960795 + 4570603 * 2 ^ 59
def prefixEnd_4570603 : Nat := 4983230072969 + 3 ^ 40 * 4570603 * 2
def baseEnd_4570603 : Nat := 782305406627295409480895

theorem tailTrace_4570603 : CollatzResearch.WordTrace tailWord_4570603 prefixEnd_4570603 782305406627295409480895 := by
  unfold tailWord_4570603
  simp only [CollatzResearch.WordTrace]
  refine ⟨166703586660493402691020463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111135724440328935127346975 166703586660493402691020463)
  ·
    refine ⟨250055379990740104036530695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 166703586660493402691020463 250055379990740104036530695)
    ·
      refine ⟨375083069986110156054796043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 250055379990740104036530695 375083069986110156054796043)
      ·
        refine ⟨562624604979165234082194065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 375083069986110156054796043 562624604979165234082194065)
        ·
          refine ⟨421968453734373925561645549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 562624604979165234082194065 421968453734373925561645549)
          ·
            refine ⟨158238170150390222085617081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 421968453734373925561645549 158238170150390222085617081)
            ·
              refine ⟨118678627612792666564212811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 158238170150390222085617081 118678627612792666564212811)
              ·
                refine ⟨178017941419188999846319217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 118678627612792666564212811 178017941419188999846319217)
                ·
                  refine ⟨133513456064391749884739413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 178017941419188999846319217 133513456064391749884739413)
                  ·
                    refine ⟨782305406627295409480895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 133513456064391749884739413 782305406627295409480895)
                    ·
                      rfl

theorem cell23_4570603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 1, 2, 9].length) (baseStart_4570603 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4570603 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4570603 prefixEnd_4570603 := by exact prefixLift 4570603
  have htrace : WordTrace (prefixWord ++ tailWord_4570603) baseStart_4570603 baseEnd_4570603 := by
    simpa [prefixWord, tailWord_4570603, baseEnd_4570603] using wordTrace_append hprefix tailTrace_4570603
  have hstable : (prefixWord ++ tailWord_4570603).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4570603).length < 2 ^ (prefixWord ++ tailWord_4570603).sum := by decide
  have hdescent : baseEnd_4570603 < baseStart_4570603 := by decide
  rcases family_descends (prefixWord ++ tailWord_4570603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4570620 : List Nat := [2, 2, 2, 1, 2, 1, 2, 3, 3, 5]
def baseStart_4570620 : Nat := 118140960795 + 4570620 * 2 ^ 59
def prefixEnd_4570620 : Nat := 4983230072969 + 3 ^ 40 * 4570620 * 2
def baseEnd_4570620 : Nat := 782308316351004220643369

theorem tailTrace_4570620 : CollatzResearch.WordTrace tailWord_4570620 prefixEnd_4570620 782308316351004220643369 := by
  unfold tailWord_4570620
  simp only [CollatzResearch.WordTrace]
  refine ⟨83352103350715907297194657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111136137800954543062926209 83352103350715907297194657)
  ·
    refine ⟨62514077513036930472895993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83352103350715907297194657 62514077513036930472895993)
    ·
      refine ⟨46885558134777697854671995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62514077513036930472895993 46885558134777697854671995)
      ·
        refine ⟨70328337202166546782007993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46885558134777697854671995 70328337202166546782007993)
        ·
          refine ⟨52746252901624910086505995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 70328337202166546782007993 52746252901624910086505995)
          ·
            refine ⟨79119379352437365129758993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52746252901624910086505995 79119379352437365129758993)
            ·
              refine ⟨59339534514328023847319245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 79119379352437365129758993 59339534514328023847319245)
              ·
                refine ⟨22252325442873008942744717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 59339534514328023847319245 22252325442873008942744717)
                ·
                  refine ⟨8344622041077378353529269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22252325442873008942744717 8344622041077378353529269)
                  ·
                    refine ⟨782308316351004220643369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8344622041077378353529269 782308316351004220643369)
                    ·
                      rfl

theorem cell23_4570620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 2, 3, 3, 5].length) (baseStart_4570620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4570620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4570620 prefixEnd_4570620 := by exact prefixLift 4570620
  have htrace : WordTrace (prefixWord ++ tailWord_4570620) baseStart_4570620 baseEnd_4570620 := by
    simpa [prefixWord, tailWord_4570620, baseEnd_4570620] using wordTrace_append hprefix tailTrace_4570620
  have hstable : (prefixWord ++ tailWord_4570620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4570620).length < 2 ^ (prefixWord ++ tailWord_4570620).sum := by decide
  have hdescent : baseEnd_4570620 < baseStart_4570620 := by decide
  rcases family_descends (prefixWord ++ tailWord_4570620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4570628 : List Nat := [2, 3, 2, 3, 2, 2, 1, 3, 1, 4]
def baseStart_4570628 : Nat := 118140960795 + 4570628 * 2 ^ 59
def prefixEnd_4570628 : Nat := 4983230072969 + 3 ^ 40 * 4570628 * 2
def baseEnd_4570628 : Nat := 782309685632749543543357

theorem tailTrace_4570628 : CollatzResearch.WordTrace tailWord_4570628 prefixEnd_4570628 782309685632749543543357 := by
  unfold tailWord_4570628
  simp only [CollatzResearch.WordTrace]
  refine ⟨83352249242701415980340269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111136332323601887973787025 83352249242701415980340269)
  ·
    refine ⟨31257093466013030992627601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 83352249242701415980340269 31257093466013030992627601)
    ·
      refine ⟨23442820099509773244470701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31257093466013030992627601 23442820099509773244470701)
      ·
        refine ⟨8791057537316164966676513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23442820099509773244470701 8791057537316164966676513)
        ·
          refine ⟨6593293152987123725007385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8791057537316164966676513 6593293152987123725007385)
          ·
            refine ⟨4944969864740342793755539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6593293152987123725007385 4944969864740342793755539)
            ·
              refine ⟨7417454797110514190633309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4944969864740342793755539 7417454797110514190633309)
              ·
                refine ⟨2781545548916442821487491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7417454797110514190633309 2781545548916442821487491)
                ·
                  refine ⟨4172318323374664232231237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2781545548916442821487491 4172318323374664232231237)
                  ·
                    refine ⟨782309685632749543543357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4172318323374664232231237 782309685632749543543357)
                    ·
                      rfl

theorem cell23_4570628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 2, 1, 3, 1, 4].length) (baseStart_4570628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4570628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4570628 prefixEnd_4570628 := by exact prefixLift 4570628
  have htrace : WordTrace (prefixWord ++ tailWord_4570628) baseStart_4570628 baseEnd_4570628 := by
    simpa [prefixWord, tailWord_4570628, baseEnd_4570628] using wordTrace_append hprefix tailTrace_4570628
  have hstable : (prefixWord ++ tailWord_4570628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4570628).length < 2 ^ (prefixWord ++ tailWord_4570628).sum := by decide
  have hdescent : baseEnd_4570628 < baseStart_4570628 := by decide
  rcases family_descends (prefixWord ++ tailWord_4570628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4570674 : List Nat := [3, 2, 1, 1, 2, 1, 1, 3, 5, 2, 2]
def baseStart_4570674 : Nat := 118140960795 + 4570674 * 2 ^ 59
def prefixEnd_4570674 : Nat := 4983230072969 + 3 ^ 40 * 4570674 * 2
def baseEnd_4570674 : Nat := 2346952677008355450654859

theorem tailTrace_4570674 : CollatzResearch.WordTrace tailWord_4570674 prefixEnd_4570674 2346952677008355450654859 := by
  unfold tailWord_4570674
  simp only [CollatzResearch.WordTrace]
  refine ⟨41676544060809045454213769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 111137450828824121211236717 41676544060809045454213769)
  ·
    refine ⟨31257408045606784090660327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41676544060809045454213769 31257408045606784090660327)
    ·
      refine ⟨46886112068410176135990491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31257408045606784090660327 46886112068410176135990491)
      ·
        refine ⟨70329168102615264203985737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46886112068410176135990491 70329168102615264203985737)
        ·
          refine ⟨52746876076961448152989303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 70329168102615264203985737 52746876076961448152989303)
          ·
            refine ⟨79120314115442172229483955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52746876076961448152989303 79120314115442172229483955)
            ·
              refine ⟨118680471173163258344225933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 79120314115442172229483955 118680471173163258344225933)
              ·
                refine ⟨44505176689936221879084725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 118680471173163258344225933 44505176689936221879084725)
                ·
                  refine ⟨4172360314681520801164193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 44505176689936221879084725 4172360314681520801164193)
                  ·
                    refine ⟨3129270236011140600873145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4172360314681520801164193 3129270236011140600873145)
                    ·
                      refine ⟨2346952677008355450654859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3129270236011140600873145 2346952677008355450654859)
                      ·
                        rfl

theorem cell23_4570674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 3, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 3, 5, 2, 2].length) (baseStart_4570674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4570674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4570674 prefixEnd_4570674 := by exact prefixLift 4570674
  have htrace : WordTrace (prefixWord ++ tailWord_4570674) baseStart_4570674 baseEnd_4570674 := by
    simpa [prefixWord, tailWord_4570674, baseEnd_4570674] using wordTrace_append hprefix tailTrace_4570674
  have hstable : (prefixWord ++ tailWord_4570674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4570674).length < 2 ^ (prefixWord ++ tailWord_4570674).sum := by decide
  have hdescent : baseEnd_4570674 < baseStart_4570674 := by decide
  rcases family_descends (prefixWord ++ tailWord_4570674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4570678 : List Nat := [5, 1, 2, 1, 3, 1, 2, 1, 2, 3, 2]
def baseStart_4570678 : Nat := 118140960795 + 4570678 * 2 ^ 59
def prefixEnd_4570678 : Nat := 4983230072969 + 3 ^ 40 * 4570678 * 2
def baseEnd_4570678 : Nat := 2346954730930973435004841

theorem tailTrace_4570678 : CollatzResearch.WordTrace tailWord_4570678 prefixEnd_4570678 2346954730930973435004841 := by
  unfold tailWord_4570678
  simp only [CollatzResearch.WordTrace]
  refine ⟨10419145133451355656250043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 111137548090147793666667125 10419145133451355656250043)
  ·
    refine ⟨15628717700177033484375065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10419145133451355656250043 15628717700177033484375065)
    ·
      refine ⟨11721538275132775113281299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15628717700177033484375065 11721538275132775113281299)
      ·
        refine ⟨17582307412699162669921949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11721538275132775113281299 17582307412699162669921949)
        ·
          refine ⟨6593365279762186001220731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17582307412699162669921949 6593365279762186001220731)
          ·
            refine ⟨9890047919643279001831097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6593365279762186001220731 9890047919643279001831097)
            ·
              refine ⟨7417535939732459251373323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9890047919643279001831097 7417535939732459251373323)
              ·
                refine ⟨11126303909598688877059985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7417535939732459251373323 11126303909598688877059985)
                ·
                  refine ⟨8344727932199016657794989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11126303909598688877059985 8344727932199016657794989)
                  ·
                    refine ⟨3129272974574631246673121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8344727932199016657794989 3129272974574631246673121)
                    ·
                      refine ⟨2346954730930973435004841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3129272974574631246673121 2346954730930973435004841)
                      ·
                        rfl

theorem cell23_4570678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 1, 2, 1, 2, 3, 2].length) (baseStart_4570678 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4570678 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4570678 prefixEnd_4570678 := by exact prefixLift 4570678
  have htrace : WordTrace (prefixWord ++ tailWord_4570678) baseStart_4570678 baseEnd_4570678 := by
    simpa [prefixWord, tailWord_4570678, baseEnd_4570678] using wordTrace_append hprefix tailTrace_4570678
  have hstable : (prefixWord ++ tailWord_4570678).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4570678).length < 2 ^ (prefixWord ++ tailWord_4570678).sum := by decide
  have hdescent : baseEnd_4570678 < baseStart_4570678 := by decide
  rcases family_descends (prefixWord ++ tailWord_4570678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4570680 : List Nat := [2, 1, 2, 1, 4, 2, 2, 9]
def baseStart_4570680 : Nat := 118140960795 + 4570680 * 2 ^ 59
def prefixEnd_4570680 : Nat := 4983230072969 + 3 ^ 40 * 4570680 * 2
def baseEnd_4570680 : Nat := 86924287329343793599253

theorem tailTrace_4570680 : CollatzResearch.WordTrace tailWord_4570680 prefixEnd_4570680 86924287329343793599253 := by
  unfold tailWord_4570680
  simp only [CollatzResearch.WordTrace]
  refine ⟨83353197540607222420786747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111137596720809629894382329 83353197540607222420786747)
  ·
    refine ⟨125029796310910833631180121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83353197540607222420786747 125029796310910833631180121)
    ·
      refine ⟨93772347233183125223385091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 125029796310910833631180121 93772347233183125223385091)
      ·
        refine ⟨140658520849774687835077637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93772347233183125223385091 140658520849774687835077637)
        ·
          refine ⟨26373472659332753969077057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 140658520849774687835077637 26373472659332753969077057)
          ·
            refine ⟨19780104494499565476807793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26373472659332753969077057 19780104494499565476807793)
            ·
              refine ⟨14835078370874674107605845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19780104494499565476807793 14835078370874674107605845)
              ·
                refine ⟨86924287329343793599253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 14835078370874674107605845 86924287329343793599253)
                ·
                  rfl

theorem cell23_4570680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 2, 9].length) (baseStart_4570680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4570680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4570680 prefixEnd_4570680 := by exact prefixLift 4570680
  have htrace : WordTrace (prefixWord ++ tailWord_4570680) baseStart_4570680 baseEnd_4570680 := by
    simpa [prefixWord, tailWord_4570680, baseEnd_4570680] using wordTrace_append hprefix tailTrace_4570680
  have hstable : (prefixWord ++ tailWord_4570680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4570680).length < 2 ^ (prefixWord ++ tailWord_4570680).sum := by decide
  have hdescent : baseEnd_4570680 < baseStart_4570680 := by decide
  rcases family_descends (prefixWord ++ tailWord_4570680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4570687 : List Nat := [1, 1, 2, 2, 3, 4, 1, 2, 1, 2, 4]
def baseStart_4570687 : Nat := 118140960795 + 4570687 * 2 ^ 59
def prefixEnd_4570687 : Nat := 4983230072969 + 3 ^ 40 * 4570687 * 2
def baseEnd_4570687 : Nat := 2346959352256863899792299

theorem tailTrace_4570687 : CollatzResearch.WordTrace tailWord_4570687 prefixEnd_4570687 2346959352256863899792299 := by
  unfold tailWord_4570687
  simp only [CollatzResearch.WordTrace]
  refine ⟨166706650392189085037078315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111137766928126056691385543 166706650392189085037078315)
  ·
    refine ⟨250059975588283627555617473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 166706650392189085037078315 250059975588283627555617473)
    ·
      refine ⟨187544981691212720666713105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 250059975588283627555617473 187544981691212720666713105)
      ·
        refine ⟨140658736268409540500034829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 187544981691212720666713105 140658736268409540500034829)
        ·
          refine ⟨52747026100653577687513061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 140658736268409540500034829 52747026100653577687513061)
          ·
            refine ⟨9890067393872545816408699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 52747026100653577687513061 9890067393872545816408699)
            ·
              refine ⟨14835101090808818724613049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9890067393872545816408699 14835101090808818724613049)
              ·
                refine ⟨11126325818106614043459787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14835101090808818724613049 11126325818106614043459787)
                ·
                  refine ⟨16689488727159921065189681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11126325818106614043459787 16689488727159921065189681)
                  ·
                    refine ⟨12517116545369940798892261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16689488727159921065189681 12517116545369940798892261)
                    ·
                      refine ⟨2346959352256863899792299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12517116545369940798892261 2346959352256863899792299)
                      ·
                        rfl

theorem cell23_4570687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 4, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 4, 1, 2, 1, 2, 4].length) (baseStart_4570687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4570687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4570687 prefixEnd_4570687 := by exact prefixLift 4570687
  have htrace : WordTrace (prefixWord ++ tailWord_4570687) baseStart_4570687 baseEnd_4570687 := by
    simpa [prefixWord, tailWord_4570687, baseEnd_4570687] using wordTrace_append hprefix tailTrace_4570687
  have hstable : (prefixWord ++ tailWord_4570687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4570687).length < 2 ^ (prefixWord ++ tailWord_4570687).sum := by decide
  have hdescent : baseEnd_4570687 < baseStart_4570687 := by decide
  rcases family_descends (prefixWord ++ tailWord_4570687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4570708 : List Nat := [2, 4, 1, 1, 1, 2, 3, 4, 1, 2, 2]
def baseStart_4570708 : Nat := 118140960795 + 4570708 * 2 ^ 59
def prefixEnd_4570708 : Nat := 4983230072969 + 3 ^ 40 * 4570708 * 2
def baseEnd_4570708 : Nat := 2346970135350608317629703

theorem tailTrace_4570708 : CollatzResearch.WordTrace tailWord_4570708 prefixEnd_4570708 2346970135350608317629703 := by
  unfold tailWord_4570708
  simp only [CollatzResearch.WordTrace]
  refine ⟨83353708162556502811796389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111138277550075337082395185 83353708162556502811796389)
  ·
    refine ⟨15628820280479344277211823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 83353708162556502811796389 15628820280479344277211823)
    ·
      refine ⟨23443230420719016415817735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15628820280479344277211823 23443230420719016415817735)
      ·
        refine ⟨35164845631078524623726603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23443230420719016415817735 35164845631078524623726603)
        ·
          refine ⟨52747268446617786935589905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35164845631078524623726603 52747268446617786935589905)
          ·
            refine ⟨39560451334963340201692429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52747268446617786935589905 39560451334963340201692429)
            ·
              refine ⟨14835169250611252575634661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 39560451334963340201692429 14835169250611252575634661)
              ·
                refine ⟨2781594234489609857931499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14835169250611252575634661 2781594234489609857931499)
                ·
                  refine ⟨4172391351734414786897249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2781594234489609857931499 4172391351734414786897249)
                  ·
                    refine ⟨3129293513800811090172937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4172391351734414786897249 3129293513800811090172937)
                    ·
                      refine ⟨2346970135350608317629703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3129293513800811090172937 2346970135350608317629703)
                      ·
                        rfl

theorem cell23_4570708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 3, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 3, 4, 1, 2, 2].length) (baseStart_4570708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4570708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4570708 prefixEnd_4570708 := by exact prefixLift 4570708
  have htrace : WordTrace (prefixWord ++ tailWord_4570708) baseStart_4570708 baseEnd_4570708 := by
    simpa [prefixWord, tailWord_4570708, baseEnd_4570708] using wordTrace_append hprefix tailTrace_4570708
  have hstable : (prefixWord ++ tailWord_4570708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4570708).length < 2 ^ (prefixWord ++ tailWord_4570708).sum := by decide
  have hdescent : baseEnd_4570708 < baseStart_4570708 := by decide
  rcases family_descends (prefixWord ++ tailWord_4570708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4570720 : List Nat := [2, 1, 1, 3, 2, 1, 1, 2, 1, 4, 5]
def baseStart_4570720 : Nat := 118140960795 + 4570720 * 2 ^ 59
def prefixEnd_4570720 : Nat := 4983230072969 + 3 ^ 40 * 4570720 * 2
def baseEnd_4570720 : Nat := 2346976297118462270679647

theorem tailTrace_4570720 : CollatzResearch.WordTrace tailWord_4570720 prefixEnd_4570720 2346976297118462270679647 := by
  unfold tailWord_4570720
  simp only [CollatzResearch.WordTrace]
  refine ⟨83353927000534765836514807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111138569334046354448686409 83353927000534765836514807)
  ·
    refine ⟨125030890500802148754772211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83353927000534765836514807 125030890500802148754772211)
    ·
      refine ⟨187546335751203223132158317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125030890500802148754772211 187546335751203223132158317)
      ·
        refine ⟨70329875906701208674559369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 187546335751203223132158317 70329875906701208674559369)
        ·
          refine ⟨52747406930025906505919527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 70329875906701208674559369 52747406930025906505919527)
          ·
            refine ⟨79121110395038859758879291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52747406930025906505919527 79121110395038859758879291)
            ·
              refine ⟨118681665592558289638318937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 79121110395038859758879291 118681665592558289638318937)
              ·
                refine ⟨89011249194418717228739203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 118681665592558289638318937 89011249194418717228739203)
                ·
                  refine ⟨133516873791628075843108805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 89011249194418717228739203 133516873791628075843108805)
                  ·
                    refine ⟨25034413835930264220582901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 133516873791628075843108805 25034413835930264220582901)
                    ·
                      refine ⟨2346976297118462270679647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25034413835930264220582901 2346976297118462270679647)
                      ·
                        rfl

theorem cell23_4570720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 2, 1, 4, 5].length) (baseStart_4570720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4570720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4570720 prefixEnd_4570720 := by exact prefixLift 4570720
  have htrace : WordTrace (prefixWord ++ tailWord_4570720) baseStart_4570720 baseEnd_4570720 := by
    simpa [prefixWord, tailWord_4570720, baseEnd_4570720] using wordTrace_append hprefix tailTrace_4570720
  have hstable : (prefixWord ++ tailWord_4570720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4570720).length < 2 ^ (prefixWord ++ tailWord_4570720).sum := by decide
  have hdescent : baseEnd_4570720 < baseStart_4570720 := by decide
  rcases family_descends (prefixWord ++ tailWord_4570720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4570724 : List Nat := [2, 3, 1, 1, 2, 4, 2, 1, 1, 3, 3]
def baseStart_4570724 : Nat := 118140960795 + 4570724 * 2 ^ 59
def prefixEnd_4570724 : Nat := 4983230072969 + 3 ^ 40 * 4570724 * 2
def baseEnd_4570724 : Nat := 2346978351041080255029629

theorem tailTrace_4570724 : CollatzResearch.WordTrace tailWord_4570724 prefixEnd_4570724 2346978351041080255029629 := by
  unfold tailWord_4570724
  simp only [CollatzResearch.WordTrace]
  refine ⟨83353999946527520178087613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111138666595370026904116817 83353999946527520178087613)
  ·
    refine ⟨31257749979947820066782855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 83353999946527520178087613 31257749979947820066782855)
    ·
      refine ⟨46886624969921730100174283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31257749979947820066782855 46886624969921730100174283)
      ·
        refine ⟨70329937454882595150261425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46886624969921730100174283 70329937454882595150261425)
        ·
          refine ⟨52747453091161946362696069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 70329937454882595150261425 52747453091161946362696069)
          ·
            refine ⟨9890147454592864943005513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 52747453091161946362696069 9890147454592864943005513)
            ·
              refine ⟨7417610590944648707254135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9890147454592864943005513 7417610590944648707254135)
              ·
                refine ⟨11126415886416973060881203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7417610590944648707254135 11126415886416973060881203)
                ·
                  refine ⟨16689623829625459591321805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11126415886416973060881203 16689623829625459591321805)
                  ·
                    refine ⟨6258608936109547346745677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16689623829625459591321805 6258608936109547346745677)
                    ·
                      refine ⟨2346978351041080255029629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6258608936109547346745677 2346978351041080255029629)
                      ·
                        rfl

theorem cell23_4570724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 4, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 4, 2, 1, 1, 3, 3].length) (baseStart_4570724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4570724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4570724 prefixEnd_4570724 := by exact prefixLift 4570724
  have htrace : WordTrace (prefixWord ++ tailWord_4570724) baseStart_4570724 baseEnd_4570724 := by
    simpa [prefixWord, tailWord_4570724, baseEnd_4570724] using wordTrace_append hprefix tailTrace_4570724
  have hstable : (prefixWord ++ tailWord_4570724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4570724).length < 2 ^ (prefixWord ++ tailWord_4570724).sum := by decide
  have hdescent : baseEnd_4570724 < baseStart_4570724 := by decide
  rcases family_descends (prefixWord ++ tailWord_4570724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4570824 : List Nat := [2, 1, 3, 1, 2, 2, 2, 1, 2, 5, 2]
def baseStart_4570824 : Nat := 118140960795 + 4570824 * 2 ^ 59
def prefixEnd_4570824 : Nat := 4983230072969 + 3 ^ 40 * 4570824 * 2
def baseEnd_4570824 : Nat := 2347029699106529863779169

theorem tailTrace_4570824 : CollatzResearch.WordTrace tailWord_4570824 prefixEnd_4570824 2347029699106529863779169 := by
  unfold tailWord_4570824
  simp only [CollatzResearch.WordTrace]
  refine ⟨83355823596346378717407763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111141098128461838289877017 83355823596346378717407763)
  ·
    refine ⟨125033735394519568076111645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83355823596346378717407763 125033735394519568076111645)
    ·
      refine ⟨46887650772944838028541867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 125033735394519568076111645 46887650772944838028541867)
      ·
        refine ⟨70331476159417257042812801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46887650772944838028541867 70331476159417257042812801)
        ·
          refine ⟨52748607119562942782109601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 70331476159417257042812801 52748607119562942782109601)
          ·
            refine ⟨39561455339672207086582201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52748607119562942782109601 39561455339672207086582201)
            ·
              refine ⟨29671091504754155314936651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39561455339672207086582201 29671091504754155314936651)
              ·
                refine ⟨44506637257131232972404977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29671091504754155314936651 44506637257131232972404977)
                ·
                  refine ⟨33379977942848424729303733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 44506637257131232972404977 33379977942848424729303733)
                  ·
                    refine ⟨3129372932142039818372225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 33379977942848424729303733 3129372932142039818372225)
                    ·
                      refine ⟨2347029699106529863779169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3129372932142039818372225 2347029699106529863779169)
                      ·
                        rfl

theorem cell23_4570824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 2, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 2, 1, 2, 5, 2].length) (baseStart_4570824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4570824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4570824 prefixEnd_4570824 := by exact prefixLift 4570824
  have htrace : WordTrace (prefixWord ++ tailWord_4570824) baseStart_4570824 baseEnd_4570824 := by
    simpa [prefixWord, tailWord_4570824, baseEnd_4570824] using wordTrace_append hprefix tailTrace_4570824
  have hstable : (prefixWord ++ tailWord_4570824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4570824).length < 2 ^ (prefixWord ++ tailWord_4570824).sum := by decide
  have hdescent : baseEnd_4570824 < baseStart_4570824 := by decide
  rcases family_descends (prefixWord ++ tailWord_4570824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4570851 : List Nat := [1, 1, 1, 7, 2, 1, 2, 1, 2, 5]
def baseStart_4570851 : Nat := 118140960795 + 4570851 * 2 ^ 59
def prefixEnd_4570851 : Nat := 4983230072969 + 3 ^ 40 * 4570851 * 2
def baseEnd_4570851 : Nat := 782347854361400419380515

theorem tailTrace_4570851 : CollatzResearch.WordTrace tailWord_4570851 prefixEnd_4570851 782347854361400419380515 := by
  unfold tailWord_4570851
  simp only [CollatzResearch.WordTrace]
  refine ⟨166712631963594941046048407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111141754642396627364032271 166712631963594941046048407)
  ·
    refine ⟨250068947945392411569072611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 166712631963594941046048407 250068947945392411569072611)
    ·
      refine ⟨375103421918088617353608917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 250068947945392411569072611 375103421918088617353608917)
      ·
        refine ⟨8791486451205201969225209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 375103421918088617353608917 8791486451205201969225209)
        ·
          refine ⟨6593614838403901476918907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8791486451205201969225209 6593614838403901476918907)
          ·
            refine ⟨9890422257605852215378361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6593614838403901476918907 9890422257605852215378361)
            ·
              refine ⟨7417816693204389161533771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9890422257605852215378361 7417816693204389161533771)
              ·
                refine ⟨11126725039806583742300657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7417816693204389161533771 11126725039806583742300657)
                ·
                  refine ⟨8345043779854937806725493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11126725039806583742300657 8345043779854937806725493)
                  ·
                    refine ⟨782347854361400419380515, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8345043779854937806725493 782347854361400419380515)
                    ·
                      rfl

theorem cell23_4570851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 1, 2, 1, 2, 5].length) (baseStart_4570851 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4570851 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4570851 prefixEnd_4570851 := by exact prefixLift 4570851
  have htrace : WordTrace (prefixWord ++ tailWord_4570851) baseStart_4570851 baseEnd_4570851 := by
    simpa [prefixWord, tailWord_4570851, baseEnd_4570851] using wordTrace_append hprefix tailTrace_4570851
  have hstable : (prefixWord ++ tailWord_4570851).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4570851).length < 2 ^ (prefixWord ++ tailWord_4570851).sum := by decide
  have hdescent : baseEnd_4570851 < baseStart_4570851 := by decide
  rcases family_descends (prefixWord ++ tailWord_4570851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4570868 : List Nat := [2, 6, 1, 1, 1, 1, 2, 2, 2, 5]
def baseStart_4570868 : Nat := 118140960795 + 4570868 * 2 ^ 59
def prefixEnd_4570868 : Nat := 4983230072969 + 3 ^ 40 * 4570868 * 2
def baseEnd_4570868 : Nat := 782350764085109230542989

theorem tailTrace_4570868 : CollatzResearch.WordTrace tailWord_4570868 prefixEnd_4570868 782350764085109230542989 := by
  unfold tailWord_4570868
  simp only [CollatzResearch.WordTrace]
  refine ⟨83356626002266676474708629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111142168003022235299611505 83356626002266676474708629)
  ·
    refine ⟨3907341843856250459751967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 83356626002266676474708629 3907341843856250459751967)
    ·
      refine ⟨5861012765784375689627951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3907341843856250459751967 5861012765784375689627951)
      ·
        refine ⟨8791519148676563534441927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5861012765784375689627951 8791519148676563534441927)
        ·
          refine ⟨13187278723014845301662891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8791519148676563534441927 13187278723014845301662891)
          ·
            refine ⟨19780918084522267952494337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13187278723014845301662891 19780918084522267952494337)
            ·
              refine ⟨14835688563391700964370753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19780918084522267952494337 14835688563391700964370753)
              ·
                refine ⟨11126766422543775723278065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14835688563391700964370753 11126766422543775723278065)
                ·
                  refine ⟨8345074816907831792458549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11126766422543775723278065 8345074816907831792458549)
                  ·
                    refine ⟨782350764085109230542989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8345074816907831792458549 782350764085109230542989)
                    ·
                      rfl

theorem cell23_4570868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 2, 2, 2, 5].length) (baseStart_4570868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4570868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4570868 prefixEnd_4570868 := by exact prefixLift 4570868
  have htrace : WordTrace (prefixWord ++ tailWord_4570868) baseStart_4570868 baseEnd_4570868 := by
    simpa [prefixWord, tailWord_4570868, baseEnd_4570868] using wordTrace_append hprefix tailTrace_4570868
  have hstable : (prefixWord ++ tailWord_4570868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4570868).length < 2 ^ (prefixWord ++ tailWord_4570868).sum := by decide
  have hdescent : baseEnd_4570868 < baseStart_4570868 := by decide
  rcases family_descends (prefixWord ++ tailWord_4570868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4570894 : List Nat := [4, 1, 1, 2, 1, 1, 4, 3, 6]
def baseStart_4570894 : Nat := 118140960795 + 4570894 * 2 ^ 59
def prefixEnd_4570894 : Nat := 4983230072969 + 3 ^ 40 * 4570894 * 2
def baseEnd_4570894 : Nat := 260785071416927176655983

theorem tailTrace_4570894 : CollatzResearch.WordTrace tailWord_4570894 prefixEnd_4570894 260785071416927176655983 := by
  unfold tailWord_4570894
  simp only [CollatzResearch.WordTrace]
  refine ⟨20839275037804894923732967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 111142800201626106259909157 20839275037804894923732967)
  ·
    refine ⟨31258912556707342385599451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20839275037804894923732967 31258912556707342385599451)
    ·
      refine ⟨46888368835061013578399177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31258912556707342385599451 46888368835061013578399177)
      ·
        refine ⟨35166276626295760183799383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46888368835061013578399177 35166276626295760183799383)
        ·
          refine ⟨52749414939443640275699075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35166276626295760183799383 52749414939443640275699075)
          ·
            refine ⟨79124122409165460413548613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52749414939443640275699075 79124122409165460413548613)
            ·
              refine ⟨14835772951718523827540365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 79124122409165460413548613 14835772951718523827540365)
              ·
                refine ⟨5563414856894446435327637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14835772951718523827540365 5563414856894446435327637)
                ·
                  refine ⟨260785071416927176655983, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5563414856894446435327637 260785071416927176655983)
                  ·
                    rfl

theorem cell23_4570894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 4, 3, 6].length) (baseStart_4570894 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4570894 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4570894 prefixEnd_4570894 := by exact prefixLift 4570894
  have htrace : WordTrace (prefixWord ++ tailWord_4570894) baseStart_4570894 baseEnd_4570894 := by
    simpa [prefixWord, tailWord_4570894, baseEnd_4570894] using wordTrace_append hprefix tailTrace_4570894
  have hstable : (prefixWord ++ tailWord_4570894).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4570894).length < 2 ^ (prefixWord ++ tailWord_4570894).sum := by decide
  have hdescent : baseEnd_4570894 < baseStart_4570894 := by decide
  rcases family_descends (prefixWord ++ tailWord_4570894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4570898 : List Nat := [3, 2, 4, 1, 1, 2, 1, 2, 3, 4]
def baseStart_4570898 : Nat := 118140960795 + 4570898 * 2 ^ 59
def prefixEnd_4570898 : Nat := 4983230072969 + 3 ^ 40 * 4570898 * 2
def baseEnd_4570898 : Nat := 782355898891654191417943

theorem tailTrace_4570898 : CollatzResearch.WordTrace tailWord_4570898 prefixEnd_4570898 782355898891654191417943 := by
  unfold tailWord_4570898
  simp only [CollatzResearch.WordTrace]
  refine ⟨41678586548606167018252337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 111142897462949778715339565 41678586548606167018252337)
  ·
    refine ⟨31258939911454625263689253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41678586548606167018252337 31258939911454625263689253)
    ·
      refine ⟨5861051233397742236941735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 31258939911454625263689253 5861051233397742236941735)
      ·
        refine ⟨8791576850096613355412603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5861051233397742236941735 8791576850096613355412603)
        ·
          refine ⟨13187365275144920033118905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8791576850096613355412603 13187365275144920033118905)
          ·
            refine ⟨9890523956358690024839179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13187365275144920033118905 9890523956358690024839179)
            ·
              refine ⟨14835785934538035037258769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9890523956358690024839179 14835785934538035037258769)
              ·
                refine ⟨11126839450903526277944077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14835785934538035037258769 11126839450903526277944077)
                ·
                  refine ⟨4172564794088822354229029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11126839450903526277944077 4172564794088822354229029)
                  ·
                    refine ⟨782355898891654191417943, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4172564794088822354229029 782355898891654191417943)
                    ·
                      rfl

theorem cell23_4570898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 2, 1, 2, 3, 4].length) (baseStart_4570898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4570898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4570898 prefixEnd_4570898 := by exact prefixLift 4570898
  have htrace : WordTrace (prefixWord ++ tailWord_4570898) baseStart_4570898 baseEnd_4570898 := by
    simpa [prefixWord, tailWord_4570898, baseEnd_4570898] using wordTrace_append hprefix tailTrace_4570898
  have hstable : (prefixWord ++ tailWord_4570898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4570898).length < 2 ^ (prefixWord ++ tailWord_4570898).sum := by decide
  have hdescent : baseEnd_4570898 < baseStart_4570898 := by decide
  rcases family_descends (prefixWord ++ tailWord_4570898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4570938 : List Nat := [3, 1, 1, 1, 5, 2, 2, 1, 3, 1, 3]
def baseStart_4570938 : Nat := 118140960795 + 4570938 * 2 ^ 59
def prefixEnd_4570938 : Nat := 4983230072969 + 3 ^ 40 * 4570938 * 2
def baseEnd_4570938 : Nat := 2347088235901142417753645

theorem tailTrace_4570938 : CollatzResearch.WordTrace tailWord_4570938 prefixEnd_4570938 2347088235901142417753645 := by
  unfold tailWord_4570938
  simp only [CollatzResearch.WordTrace]
  refine ⟨41678951278569938726116367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 111143870076186503269643645 41678951278569938726116367)
  ·
    refine ⟨62518426917854908089174551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41678951278569938726116367 62518426917854908089174551)
    ·
      refine ⟨93777640376782362133761827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62518426917854908089174551 93777640376782362133761827)
      ·
        refine ⟨140666460565173543200642741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93777640376782362133761827 140666460565173543200642741)
        ·
          refine ⟨13187480677985019675060257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 140666460565173543200642741 13187480677985019675060257)
          ·
            refine ⟨9890610508488764756295193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13187480677985019675060257 9890610508488764756295193)
            ·
              refine ⟨7417957881366573567221395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9890610508488764756295193 7417957881366573567221395)
              ·
                refine ⟨11126936822049860350832093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7417957881366573567221395 11126936822049860350832093)
                ·
                  refine ⟨4172601308268697631562035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11126936822049860350832093 4172601308268697631562035)
                  ·
                    refine ⟨6258901962403046447343053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4172601308268697631562035 6258901962403046447343053)
                    ·
                      refine ⟨2347088235901142417753645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6258901962403046447343053 2347088235901142417753645)
                      ·
                        rfl

theorem cell23_4570938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 2, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 2, 2, 1, 3, 1, 3].length) (baseStart_4570938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4570938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4570938 prefixEnd_4570938 := by exact prefixLift 4570938
  have htrace : WordTrace (prefixWord ++ tailWord_4570938) baseStart_4570938 baseEnd_4570938 := by
    simpa [prefixWord, tailWord_4570938, baseEnd_4570938] using wordTrace_append hprefix tailTrace_4570938
  have hstable : (prefixWord ++ tailWord_4570938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4570938).length < 2 ^ (prefixWord ++ tailWord_4570938).sum := by decide
  have hdescent : baseEnd_4570938 < baseStart_4570938 := by decide
  rcases family_descends (prefixWord ++ tailWord_4570938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4570961 : List Nat := [1, 2, 2, 1, 5, 1, 1, 4, 1, 1, 4]
def baseStart_4570961 : Nat := 118140960795 + 4570961 * 2 ^ 59
def prefixEnd_4570961 : Nat := 4983230072969 + 3 ^ 40 * 4570961 * 2
def baseEnd_4570961 : Nat := 2347100045956195827766039

theorem tailTrace_4570961 : CollatzResearch.WordTrace tailWord_4570961 prefixEnd_4570961 2347100045956195827766039 := by
  unfold tailWord_4570961
  simp only [CollatzResearch.WordTrace]
  refine ⟨166716643993196429832552737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111144429328797619888368491 166716643993196429832552737)
  ·
    refine ⟨125037482994897322374414553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 166716643993196429832552737 125037482994897322374414553)
    ·
      refine ⟨93778112246172991780810915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 125037482994897322374414553 93778112246172991780810915)
      ·
        refine ⟨140667168369259487671216373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93778112246172991780810915 140667168369259487671216373)
        ·
          refine ⟨13187547034618076969176535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 140667168369259487671216373 13187547034618076969176535)
          ·
            refine ⟨19781320551927115453764803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13187547034618076969176535 19781320551927115453764803)
            ·
              refine ⟨29671980827890673180647205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19781320551927115453764803 29671980827890673180647205)
              ·
                refine ⟨5563496405229501221371351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 29671980827890673180647205 5563496405229501221371351)
                ·
                  refine ⟨8345244607844251832057027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5563496405229501221371351 8345244607844251832057027)
                  ·
                    refine ⟨12517866911766377748085541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8345244607844251832057027 12517866911766377748085541)
                    ·
                      refine ⟨2347100045956195827766039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12517866911766377748085541 2347100045956195827766039)
                      ·
                        rfl

theorem cell23_4570961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 1, 4, 1, 1, 4].length) (baseStart_4570961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4570961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4570961 prefixEnd_4570961 := by exact prefixLift 4570961
  have htrace : WordTrace (prefixWord ++ tailWord_4570961) baseStart_4570961 baseEnd_4570961 := by
    simpa [prefixWord, tailWord_4570961, baseEnd_4570961] using wordTrace_append hprefix tailTrace_4570961
  have hstable : (prefixWord ++ tailWord_4570961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4570961).length < 2 ^ (prefixWord ++ tailWord_4570961).sum := by decide
  have hdescent : baseEnd_4570961 < baseStart_4570961 := by decide
  rcases family_descends (prefixWord ++ tailWord_4570961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4570978 : List Nat := [3, 3, 2, 1, 2, 1, 2, 3, 1, 1, 4]
def baseStart_4570978 : Nat := 118140960795 + 4570978 * 2 ^ 59
def prefixEnd_4570978 : Nat := 4983230072969 + 3 ^ 40 * 4570978 * 2
def baseEnd_4570978 : Nat := 2347108775127322261253461

theorem tailTrace_4570978 : CollatzResearch.WordTrace tailWord_4570978 prefixEnd_4570978 2347108775127322261253461 := by
  unfold tailWord_4570978
  simp only [CollatzResearch.WordTrace]
  refine ⟨41679316008533710433980397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 111144842689423227823947725 41679316008533710433980397)
  ·
    refine ⟨15629743503200141412742649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41679316008533710433980397 15629743503200141412742649)
    ·
      refine ⟨11722307627400106059556987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15629743503200141412742649 11722307627400106059556987)
      ·
        refine ⟨17583461441100159089335481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11722307627400106059556987 17583461441100159089335481)
        ·
          refine ⟨13187596080825119317001611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17583461441100159089335481 13187596080825119317001611)
          ·
            refine ⟨19781394121237678975502417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13187596080825119317001611 19781394121237678975502417)
            ·
              refine ⟨14836045590928259231626813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19781394121237678975502417 14836045590928259231626813)
              ·
                refine ⟨5563517096598097211860055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14836045590928259231626813 5563517096598097211860055)
                ·
                  refine ⟨8345275644897145817790083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5563517096598097211860055 8345275644897145817790083)
                  ·
                    refine ⟨12517913467345718726685125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8345275644897145817790083 12517913467345718726685125)
                    ·
                      refine ⟨2347108775127322261253461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12517913467345718726685125 2347108775127322261253461)
                      ·
                        rfl

theorem cell23_4570978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 2, 3, 1, 1, 4].length) (baseStart_4570978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4570978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4570978 prefixEnd_4570978 := by exact prefixLift 4570978
  have htrace : WordTrace (prefixWord ++ tailWord_4570978) baseStart_4570978 baseEnd_4570978 := by
    simpa [prefixWord, tailWord_4570978, baseEnd_4570978] using wordTrace_append hprefix tailTrace_4570978
  have hstable : (prefixWord ++ tailWord_4570978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4570978).length < 2 ^ (prefixWord ++ tailWord_4570978).sum := by decide
  have hdescent : baseEnd_4570978 < baseStart_4570978 := by decide
  rcases family_descends (prefixWord ++ tailWord_4570978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4571015 : List Nat := [1, 1, 4, 2, 4, 2, 1, 2, 1, 2, 3]
def baseStart_4571015 : Nat := 118140960795 + 4571015 * 2 ^ 59
def prefixEnd_4571015 : Nat := 4983230072969 + 3 ^ 40 * 4571015 * 2
def baseEnd_4571015 : Nat := 2347127773911538616490791

theorem tailTrace_4571015 : CollatzResearch.WordTrace tailWord_4571015 prefixEnd_4571015 2347127773911538616490791 := by
  unfold tailWord_4571015
  simp only [CollatzResearch.WordTrace]
  refine ⟨166718613535000797055018499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111145742356667198036678999 166718613535000797055018499)
  ·
    refine ⟨250077920302501195582527749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 166718613535000797055018499 250077920302501195582527749)
    ·
      refine ⟨46889610056718974171723953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 250077920302501195582527749 46889610056718974171723953)
      ·
        refine ⟨35167207542539230628792965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46889610056718974171723953 35167207542539230628792965)
        ·
          refine ⟨6593851414226105742898681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 35167207542539230628792965 6593851414226105742898681)
          ·
            refine ⟨4945388560669579307174011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6593851414226105742898681 4945388560669579307174011)
            ·
              refine ⟨7418082841004368960761017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4945388560669579307174011 7418082841004368960761017)
              ·
                refine ⟨5563562130753276720570763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7418082841004368960761017 5563562130753276720570763)
                ·
                  refine ⟨8345343196129915080856145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5563562130753276720570763 8345343196129915080856145)
                  ·
                    refine ⟨6259007397097436310642109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8345343196129915080856145 6259007397097436310642109)
                    ·
                      refine ⟨2347127773911538616490791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6259007397097436310642109 2347127773911538616490791)
                      ·
                        rfl

theorem cell23_4571015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 2, 1, 2, 1, 2, 3].length) (baseStart_4571015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4571015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4571015 prefixEnd_4571015 := by exact prefixLift 4571015
  have htrace : WordTrace (prefixWord ++ tailWord_4571015) baseStart_4571015 baseEnd_4571015 := by
    simpa [prefixWord, tailWord_4571015, baseEnd_4571015] using wordTrace_append hprefix tailTrace_4571015
  have hstable : (prefixWord ++ tailWord_4571015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4571015).length < 2 ^ (prefixWord ++ tailWord_4571015).sum := by decide
  have hdescent : baseEnd_4571015 < baseStart_4571015 := by decide
  rcases family_descends (prefixWord ++ tailWord_4571015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4571028 : List Nat := [2, 4, 2, 1, 1, 3, 1, 2, 1, 3, 3]
def baseStart_4571028 : Nat := 118140960795 + 4571028 * 2 ^ 59
def prefixEnd_4571028 : Nat := 4983230072969 + 3 ^ 40 * 4571028 * 2
def baseEnd_4571028 : Nat := 2347134449160047065628231

theorem tailTrace_4571028 : CollatzResearch.WordTrace tailWord_4571028 prefixEnd_4571028 2347134449160047065628231 := by
  unfold tailWord_4571028
  simp only [CollatzResearch.WordTrace]
  refine ⟨83359543841976850137620869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111146058455969133516827825 83359543841976850137620869)
  ·
    refine ⟨15629914470370659400803913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 83359543841976850137620869 15629914470370659400803913)
    ·
      refine ⟨11722435852777994550602935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15629914470370659400803913 11722435852777994550602935)
      ·
        refine ⟨17583653779166991825904403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11722435852777994550602935 17583653779166991825904403)
        ·
          refine ⟨26375480668750487738856605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17583653779166991825904403 26375480668750487738856605)
          ·
            refine ⟨9890805250781432902071227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26375480668750487738856605 9890805250781432902071227)
            ·
              refine ⟨14836207876172149353106841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9890805250781432902071227 14836207876172149353106841)
              ·
                refine ⟨11127155907129112014830131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14836207876172149353106841 11127155907129112014830131)
                ·
                  refine ⟨16690733860693668022245197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11127155907129112014830131 16690733860693668022245197)
                  ·
                    refine ⟨6259025197760125508341949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16690733860693668022245197 6259025197760125508341949)
                    ·
                      refine ⟨2347134449160047065628231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6259025197760125508341949 2347134449160047065628231)
                      ·
                        rfl

theorem cell23_4571028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 3, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 3, 1, 2, 1, 3, 3].length) (baseStart_4571028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4571028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4571028 prefixEnd_4571028 := by exact prefixLift 4571028
  have htrace : WordTrace (prefixWord ++ tailWord_4571028) baseStart_4571028 baseEnd_4571028 := by
    simpa [prefixWord, tailWord_4571028, baseEnd_4571028] using wordTrace_append hprefix tailTrace_4571028
  have hstable : (prefixWord ++ tailWord_4571028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4571028).length < 2 ^ (prefixWord ++ tailWord_4571028).sum := by decide
  have hdescent : baseEnd_4571028 < baseStart_4571028 := by decide
  rcases family_descends (prefixWord ++ tailWord_4571028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4571032 : List Nat := [2, 1, 2, 6, 1, 1, 3, 1, 1, 2, 3]
def baseStart_4571032 : Nat := 118140960795 + 4571032 * 2 ^ 59
def prefixEnd_4571032 : Nat := 4983230072969 + 3 ^ 40 * 4571032 * 2
def baseEnd_4571032 : Nat := 2347136503082665049978213

theorem tailTrace_4571032 : CollatzResearch.WordTrace tailWord_4571032 prefixEnd_4571032 2347136503082665049978213 := by
  unfold tailWord_4571032
  simp only [CollatzResearch.WordTrace]
  refine ⟨83359616787969604479193675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111146155717292805972258233 83359616787969604479193675)
  ·
    refine ⟨125039425181954406718790513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83359616787969604479193675 125039425181954406718790513)
    ·
      refine ⟨93779568886465805039092885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 125039425181954406718790513 93779568886465805039092885)
      ·
        refine ⟨4395917291553084611207479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 93779568886465805039092885 4395917291553084611207479)
        ·
          refine ⟨6593875937329626916811219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4395917291553084611207479 6593875937329626916811219)
          ·
            refine ⟨9890813905994440375216829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6593875937329626916811219 9890813905994440375216829)
            ·
              refine ⟨3709055214747915140706311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9890813905994440375216829 3709055214747915140706311)
              ·
                refine ⟨5563582822121872711059467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3709055214747915140706311 5563582822121872711059467)
                ·
                  refine ⟨8345374233182809066589201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5563582822121872711059467 8345374233182809066589201)
                  ·
                    refine ⟨6259030674887106799941901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8345374233182809066589201 6259030674887106799941901)
                    ·
                      refine ⟨2347136503082665049978213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6259030674887106799941901 2347136503082665049978213)
                      ·
                        rfl

theorem cell23_4571032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 1, 3, 1, 1, 2, 3].length) (baseStart_4571032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4571032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4571032 prefixEnd_4571032 := by exact prefixLift 4571032
  have htrace : WordTrace (prefixWord ++ tailWord_4571032) baseStart_4571032 baseEnd_4571032 := by
    simpa [prefixWord, tailWord_4571032, baseEnd_4571032] using wordTrace_append hprefix tailTrace_4571032
  have hstable : (prefixWord ++ tailWord_4571032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4571032).length < 2 ^ (prefixWord ++ tailWord_4571032).sum := by decide
  have hdescent : baseEnd_4571032 < baseStart_4571032 := by decide
  rcases family_descends (prefixWord ++ tailWord_4571032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4571061 : List Nat := [1, 3, 3, 2, 1, 3, 1, 1, 2, 6]
def baseStart_4571061 : Nat := 118140960795 + 4571061 * 2 ^ 59
def prefixEnd_4571061 : Nat := 4983230072969 + 3 ^ 40 * 4571061 * 2
def baseEnd_4571061 : Nat := 782383798007215145505193

theorem tailTrace_4571061 : CollatzResearch.WordTrace tailWord_4571061 prefixEnd_4571061 782383798007215145505193 := by
  unfold tailWord_4571061
  simp only [CollatzResearch.WordTrace]
  refine ⟨166720291292834146911193037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111146860861889431274128691 166720291292834146911193037)
  ·
    refine ⟨62520109234812805091697389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 166720291292834146911193037 62520109234812805091697389)
    ·
      refine ⟨23445040963054801909386521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 62520109234812805091697389 23445040963054801909386521)
      ·
        refine ⟨17583780722291101432039891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23445040963054801909386521 17583780722291101432039891)
        ·
          refine ⟨26375671083436652148059837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17583780722291101432039891 26375671083436652148059837)
          ·
            refine ⟨9890876656288744555522439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26375671083436652148059837 9890876656288744555522439)
            ·
              refine ⟨14836314984433116833283659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9890876656288744555522439 14836314984433116833283659)
              ·
                refine ⟨22254472476649675249925489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14836314984433116833283659 22254472476649675249925489)
                ·
                  refine ⟨16690854357487256437444117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22254472476649675249925489 16690854357487256437444117)
                  ·
                    refine ⟨782383798007215145505193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16690854357487256437444117 782383798007215145505193)
                    ·
                      rfl

theorem cell23_4571061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 3, 1, 1, 2, 6].length) (baseStart_4571061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4571061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4571061 prefixEnd_4571061 := by exact prefixLift 4571061
  have htrace : WordTrace (prefixWord ++ tailWord_4571061) baseStart_4571061 baseEnd_4571061 := by
    simpa [prefixWord, tailWord_4571061, baseEnd_4571061] using wordTrace_append hprefix tailTrace_4571061
  have hstable : (prefixWord ++ tailWord_4571061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4571061).length < 2 ^ (prefixWord ++ tailWord_4571061).sum := by decide
  have hdescent : baseEnd_4571061 < baseStart_4571061 := by decide
  rcases family_descends (prefixWord ++ tailWord_4571061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4571118 : List Nat := [4, 1, 2, 1, 3, 1, 2, 1, 2, 3, 3]
def baseStart_4571118 : Nat := 118140960795 + 4571118 * 2 ^ 59
def prefixEnd_4571118 : Nat := 4983230072969 + 3 ^ 40 * 4571118 * 2
def baseEnd_4571118 : Nat := 2347180662418951713502817

theorem tailTrace_4571118 : CollatzResearch.WordTrace tailWord_4571118 prefixEnd_4571118 2347180662418951713502817 := by
  unfold tailWord_4571118
  simp only [CollatzResearch.WordTrace]
  refine ⟨20840296281703455705752251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 111148246835751763764012005 20840296281703455705752251)
  ·
    refine ⟨31260444422555183558628377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20840296281703455705752251 31260444422555183558628377)
    ·
      refine ⟨23445333316916387668971283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31260444422555183558628377 23445333316916387668971283)
      ·
        refine ⟨35167999975374581503456925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23445333316916387668971283 35167999975374581503456925)
        ·
          refine ⟨13187999990765468063796347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35167999975374581503456925 13187999990765468063796347)
          ·
            refine ⟨19781999986148202095694521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13187999990765468063796347 19781999986148202095694521)
            ·
              refine ⟨14836499989611151571770891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19781999986148202095694521 14836499989611151571770891)
              ·
                refine ⟨22254749984416727357656337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14836499989611151571770891 22254749984416727357656337)
                ·
                  refine ⟨16691062488312545518242253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22254749984416727357656337 16691062488312545518242253)
                  ·
                    refine ⟨6259148433117204569340845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16691062488312545518242253 6259148433117204569340845)
                    ·
                      refine ⟨2347180662418951713502817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6259148433117204569340845 2347180662418951713502817)
                      ·
                        rfl

theorem cell23_4571118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 2, 1, 2, 3, 3].length) (baseStart_4571118 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4571118 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4571118 prefixEnd_4571118 := by exact prefixLift 4571118
  have htrace : WordTrace (prefixWord ++ tailWord_4571118) baseStart_4571118 baseEnd_4571118 := by
    simpa [prefixWord, tailWord_4571118, baseEnd_4571118] using wordTrace_append hprefix tailTrace_4571118
  have hstable : (prefixWord ++ tailWord_4571118).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4571118).length < 2 ^ (prefixWord ++ tailWord_4571118).sum := by decide
  have hdescent : baseEnd_4571118 < baseStart_4571118 := by decide
  rcases family_descends (prefixWord ++ tailWord_4571118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4571141 : List Nat := [1, 3, 1, 1, 2, 4, 2, 1, 1, 3, 4]
def baseStart_4571141 : Nat := 118140960795 + 4571141 * 2 ^ 59
def prefixEnd_4571141 : Nat := 4983230072969 + 3 ^ 40 * 4571141 * 2
def baseEnd_4571141 : Nat := 2347192472474005123515211

theorem tailTrace_4571141 : CollatzResearch.WordTrace tailWord_4571141 prefixEnd_4571141 2347192472474005123515211 := by
  unfold tailWord_4571141
  simp only [CollatzResearch.WordTrace]
  refine ⟨166723209132544320574105277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111148806088362880382736851 166723209132544320574105277)
  ·
    refine ⟨62521203424704120215289479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 166723209132544320574105277 62521203424704120215289479)
    ·
      refine ⟨93781805137056180322934219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62521203424704120215289479 93781805137056180322934219)
      ·
        refine ⟨140672707705584270484401329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93781805137056180322934219 140672707705584270484401329)
        ·
          refine ⟨105504530779188202863300997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 140672707705584270484401329 105504530779188202863300997)
          ·
            refine ⟨19782099521097788036868937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 105504530779188202863300997 19782099521097788036868937)
            ·
              refine ⟨14836574640823341027651703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19782099521097788036868937 14836574640823341027651703)
              ·
                refine ⟨22254861961235011541477555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14836574640823341027651703 22254861961235011541477555)
                ·
                  refine ⟨33382292941852517312216333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22254861961235011541477555 33382292941852517312216333)
                  ·
                    refine ⟨12518359853194693992081125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 33382292941852517312216333 12518359853194693992081125)
                    ·
                      refine ⟨2347192472474005123515211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12518359853194693992081125 2347192472474005123515211)
                      ·
                        rfl

theorem cell23_4571141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 2, 1, 1, 3, 4].length) (baseStart_4571141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4571141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4571141 prefixEnd_4571141 := by exact prefixLift 4571141
  have htrace : WordTrace (prefixWord ++ tailWord_4571141) baseStart_4571141 baseEnd_4571141 := by
    simpa [prefixWord, tailWord_4571141, baseEnd_4571141] using wordTrace_append hprefix tailTrace_4571141
  have hstable : (prefixWord ++ tailWord_4571141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4571141).length < 2 ^ (prefixWord ++ tailWord_4571141).sum := by decide
  have hdescent : baseEnd_4571141 < baseStart_4571141 := by decide
  rcases family_descends (prefixWord ++ tailWord_4571141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4571191 : List Nat := [1, 1, 3, 1, 2, 2, 2, 1, 2, 5, 3]
def baseStart_4571191 : Nat := 118140960795 + 4571191 * 2 ^ 59
def prefixEnd_4571191 : Nat := 4983230072969 + 3 ^ 40 * 4571191 * 2
def baseEnd_4571191 : Nat := 2347218146506729927889981

theorem tailTrace_4571191 : CollatzResearch.WordTrace tailWord_4571191 prefixEnd_4571191 2347218146506729927889981 := by
  unfold tailWord_4571191
  simp only [CollatzResearch.WordTrace]
  refine ⟨166725032782363179113425427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111150021854908786075616951 166725032782363179113425427)
  ·
    refine ⟨250087549173544768670138141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 166725032782363179113425427 250087549173544768670138141)
    ·
      refine ⟨93782830940079288251301803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 250087549173544768670138141 93782830940079288251301803)
      ·
        refine ⟨140674246410118932376952705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93782830940079288251301803 140674246410118932376952705)
        ·
          refine ⟨105505684807589199282714529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 140674246410118932376952705 105505684807589199282714529)
          ·
            refine ⟨79129263605691899462035897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 105505684807589199282714529 79129263605691899462035897)
            ·
              refine ⟨59346947704268924596526923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 79129263605691899462035897 59346947704268924596526923)
              ·
                refine ⟨89020421556403386894790385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 59346947704268924596526923 89020421556403386894790385)
                ·
                  refine ⟨66765316167302540171092789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 89020421556403386894790385 66765316167302540171092789)
                  ·
                    refine ⟨6259248390684613141039949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 66765316167302540171092789 6259248390684613141039949)
                    ·
                      refine ⟨2347218146506729927889981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6259248390684613141039949 2347218146506729927889981)
                      ·
                        rfl

theorem cell23_4571191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 2, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 2, 1, 2, 5, 3].length) (baseStart_4571191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4571191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4571191 prefixEnd_4571191 := by exact prefixLift 4571191
  have htrace : WordTrace (prefixWord ++ tailWord_4571191) baseStart_4571191 baseEnd_4571191 := by
    simpa [prefixWord, tailWord_4571191, baseEnd_4571191] using wordTrace_append hprefix tailTrace_4571191
  have hstable : (prefixWord ++ tailWord_4571191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4571191).length < 2 ^ (prefixWord ++ tailWord_4571191).sum := by decide
  have hdescent : baseEnd_4571191 < baseStart_4571191 := by decide
  rcases family_descends (prefixWord ++ tailWord_4571191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4571208 : List Nat := [2, 1, 3, 1, 1, 1, 2, 1, 7, 1, 3]
def baseStart_4571208 : Nat := 118140960795 + 4571208 * 2 ^ 59
def prefixEnd_4571208 : Nat := 4983230072969 + 3 ^ 40 * 4571208 * 2
def baseEnd_4571208 : Nat := 2347226875677856361377403

theorem tailTrace_4571208 : CollatzResearch.WordTrace tailWord_4571208 prefixEnd_4571208 2347226875677856361377403 := by
  unfold tailWord_4571208
  simp only [CollatzResearch.WordTrace]
  refine ⟨83362826411650795508397139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111150435215534394011196185 83362826411650795508397139)
  ·
    refine ⟨125044239617476193262595709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83362826411650795508397139 125044239617476193262595709)
    ·
      refine ⟨46891589856553572473473391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 125044239617476193262595709 46891589856553572473473391)
      ·
        refine ⟨70337384784830358710210087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46891589856553572473473391 70337384784830358710210087)
        ·
          refine ⟨105506077177245538065315131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70337384784830358710210087 105506077177245538065315131)
          ·
            refine ⟨158259115765868307097972697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 105506077177245538065315131 158259115765868307097972697)
            ·
              refine ⟨118694336824401230323479523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 158259115765868307097972697 118694336824401230323479523)
              ·
                refine ⟨178041505236601845485219285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 118694336824401230323479523 178041505236601845485219285)
                ·
                  refine ⟨4172847778982855753559827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 178041505236601845485219285 4172847778982855753559827)
                  ·
                    refine ⟨6259271668474283630339741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4172847778982855753559827 6259271668474283630339741)
                    ·
                      refine ⟨2347226875677856361377403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6259271668474283630339741 2347226875677856361377403)
                      ·
                        rfl

theorem cell23_4571208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 1, 7, 1, 3].length) (baseStart_4571208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4571208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4571208 prefixEnd_4571208 := by exact prefixLift 4571208
  have htrace : WordTrace (prefixWord ++ tailWord_4571208) baseStart_4571208 baseEnd_4571208 := by
    simpa [prefixWord, tailWord_4571208, baseEnd_4571208] using wordTrace_append hprefix tailTrace_4571208
  have hstable : (prefixWord ++ tailWord_4571208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4571208).length < 2 ^ (prefixWord ++ tailWord_4571208).sum := by decide
  have hdescent : baseEnd_4571208 < baseStart_4571208 := by decide
  rcases family_descends (prefixWord ++ tailWord_4571208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4571228 : List Nat := [2, 2, 4, 1, 1, 2, 1, 2, 3, 5]
def baseStart_4571228 : Nat := 118140960795 + 4571228 * 2 ^ 59
def prefixEnd_4571228 : Nat := 4983230072969 + 3 ^ 40 * 4571228 * 2
def baseEnd_4571228 : Nat := 782412381763648761042437

theorem tailTrace_4571228 : CollatzResearch.WordTrace tailWord_4571228 prefixEnd_4571228 782412381763648761042437 := by
  unfold tailWord_4571228
  simp only [CollatzResearch.WordTrace]
  refine ⟨83363191141614567216261169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111150921522152756288348225 83363191141614567216261169)
  ·
    refine ⟨62522393356210925412195877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83363191141614567216261169 62522393356210925412195877)
    ·
      refine ⟨11722948754289548514786727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 62522393356210925412195877 11722948754289548514786727)
      ·
        refine ⟨17584423131434322772180091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11722948754289548514786727 17584423131434322772180091)
        ·
          refine ⟨26376634697151484158270137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17584423131434322772180091 26376634697151484158270137)
          ·
            refine ⟨19782476022863613118702603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26376634697151484158270137 19782476022863613118702603)
            ·
              refine ⟨29673714034295419678053905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19782476022863613118702603 29673714034295419678053905)
              ·
                refine ⟨22255285525721564758540429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29673714034295419678053905 22255285525721564758540429)
                ·
                  refine ⟨8345732072145586784452661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22255285525721564758540429 8345732072145586784452661)
                  ·
                    refine ⟨782412381763648761042437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8345732072145586784452661 782412381763648761042437)
                    ·
                      rfl

theorem cell23_4571228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 1, 2, 3, 5].length) (baseStart_4571228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4571228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4571228 prefixEnd_4571228 := by exact prefixLift 4571228
  have htrace : WordTrace (prefixWord ++ tailWord_4571228) baseStart_4571228 baseEnd_4571228 := by
    simpa [prefixWord, tailWord_4571228, baseEnd_4571228] using wordTrace_append hprefix tailTrace_4571228
  have hstable : (prefixWord ++ tailWord_4571228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4571228).length < 2 ^ (prefixWord ++ tailWord_4571228).sum := by decide
  have hdescent : baseEnd_4571228 < baseStart_4571228 := by decide
  rcases family_descends (prefixWord ++ tailWord_4571228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4571242 : List Nat := [3, 1, 3, 2, 3, 1, 1, 2, 3, 1, 3]
def baseStart_4571242 : Nat := 118140960795 + 4571242 * 2 ^ 59
def prefixEnd_4571242 : Nat := 4983230072969 + 3 ^ 40 * 4571242 * 2
def baseEnd_4571242 : Nat := 2347244334020109228352247

theorem tailTrace_4571242 : CollatzResearch.WordTrace tailWord_4571242 prefixEnd_4571242 2347244334020109228352247 := by
  unfold tailWord_4571242
  simp only [CollatzResearch.WordTrace]
  refine ⟨41681723226294603705882995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 111151261936785609882354653 41681723226294603705882995)
  ·
    refine ⟨62522584839441905558824493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41681723226294603705882995 62522584839441905558824493)
    ·
      refine ⟨23445969314790714584559185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 62522584839441905558824493 23445969314790714584559185)
      ·
        refine ⟨17584476986093035938419389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23445969314790714584559185 17584476986093035938419389)
        ·
          refine ⟨6594178869784888476907271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17584476986093035938419389 6594178869784888476907271)
          ·
            refine ⟨9891268304677332715360907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6594178869784888476907271 9891268304677332715360907)
            ·
              refine ⟨14836902457015999073041361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9891268304677332715360907 14836902457015999073041361)
              ·
                refine ⟨11127676842761999304781021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14836902457015999073041361 11127676842761999304781021)
                ·
                  refine ⟨4172878816035749739292883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11127676842761999304781021 4172878816035749739292883)
                  ·
                    refine ⟨6259318224053624608939325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4172878816035749739292883 6259318224053624608939325)
                    ·
                      refine ⟨2347244334020109228352247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6259318224053624608939325 2347244334020109228352247)
                      ·
                        rfl

theorem cell23_4571242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 1, 1, 2, 3, 1, 3].length) (baseStart_4571242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4571242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4571242 prefixEnd_4571242 := by exact prefixLift 4571242
  have htrace : WordTrace (prefixWord ++ tailWord_4571242) baseStart_4571242 baseEnd_4571242 := by
    simpa [prefixWord, tailWord_4571242, baseEnd_4571242] using wordTrace_append hprefix tailTrace_4571242
  have hstable : (prefixWord ++ tailWord_4571242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4571242).length < 2 ^ (prefixWord ++ tailWord_4571242).sum := by decide
  have hdescent : baseEnd_4571242 < baseStart_4571242 := by decide
  rcases family_descends (prefixWord ++ tailWord_4571242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4571248 : List Nat := [2, 1, 1, 1, 5, 2, 2, 1, 3, 1, 4]
def baseStart_4571248 : Nat := 118140960795 + 4571248 * 2 ^ 59
def prefixEnd_4571248 : Nat := 4983230072969 + 3 ^ 40 * 4571248 * 2
def baseEnd_4571248 : Nat := 2347247414904036204877219

theorem tailTrace_4571248 : CollatzResearch.WordTrace tailWord_4571248 prefixEnd_4571248 2347247414904036204877219 := by
  unfold tailWord_4571248
  simp only [CollatzResearch.WordTrace]
  refine ⟨83363555871578338924125199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111151407828771118565500265 83363555871578338924125199)
  ·
    refine ⟨125045333807367508386187799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83363555871578338924125199 125045333807367508386187799)
    ·
      refine ⟨187568000711051262579281699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125045333807367508386187799 187568000711051262579281699)
      ·
        refine ⟨281352001066576893868922549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 187568000711051262579281699 281352001066576893868922549)
        ·
          refine ⟨26376750099991583800211489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 281352001066576893868922549 26376750099991583800211489)
          ·
            refine ⟨19782562574993687850158617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26376750099991583800211489 19782562574993687850158617)
            ·
              refine ⟨14836921931245265887618963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19782562574993687850158617 14836921931245265887618963)
              ·
                refine ⟨22255382896867898831428445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14836921931245265887618963 22255382896867898831428445)
                ·
                  refine ⟨8345768586325462061785667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22255382896867898831428445 8345768586325462061785667)
                  ·
                    refine ⟨12518652879488193092678501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8345768586325462061785667 12518652879488193092678501)
                    ·
                      refine ⟨2347247414904036204877219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12518652879488193092678501 2347247414904036204877219)
                      ·
                        rfl

theorem cell23_4571248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 2, 1, 3, 1, 4].length) (baseStart_4571248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4571248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4571248 prefixEnd_4571248 := by exact prefixLift 4571248
  have htrace : WordTrace (prefixWord ++ tailWord_4571248) baseStart_4571248 baseEnd_4571248 := by
    simpa [prefixWord, tailWord_4571248, baseEnd_4571248] using wordTrace_append hprefix tailTrace_4571248
  have hstable : (prefixWord ++ tailWord_4571248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4571248).length < 2 ^ (prefixWord ++ tailWord_4571248).sum := by decide
  have hdescent : baseEnd_4571248 < baseStart_4571248 := by decide
  rcases family_descends (prefixWord ++ tailWord_4571248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4571268 : List Nat := [2, 3, 2, 1, 2, 1, 2, 3, 1, 1, 5]
def baseStart_4571268 : Nat := 118140960795 + 4571268 * 2 ^ 59
def prefixEnd_4571268 : Nat := 4983230072969 + 3 ^ 40 * 4571268 * 2
def baseEnd_4571268 : Nat := 2347257684517126126627127

theorem tailTrace_4571268 : CollatzResearch.WordTrace tailWord_4571268 prefixEnd_4571268 2347257684517126126627127 := by
  unfold tailWord_4571268
  simp only [CollatzResearch.WordTrace]
  refine ⟨83363920601542110631989229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111151894135389480842652305 83363920601542110631989229)
  ·
    refine ⟨31261470225578291486995961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 83363920601542110631989229 31261470225578291486995961)
    ·
      refine ⟨23446102669183718615246971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31261470225578291486995961 23446102669183718615246971)
      ·
        refine ⟨35169154003775577922870457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23446102669183718615246971 35169154003775577922870457)
        ·
          refine ⟨26376865502831683442152843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35169154003775577922870457 26376865502831683442152843)
          ·
            refine ⟨39565298254247525163229265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26376865502831683442152843 39565298254247525163229265)
            ·
              refine ⟨29673973690685643872421949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39565298254247525163229265 29673973690685643872421949)
              ·
                refine ⟨11127740134007116452158231, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29673973690685643872421949 11127740134007116452158231)
                ·
                  refine ⟨16691610201010674678237347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11127740134007116452158231 16691610201010674678237347)
                  ·
                    refine ⟨25037415301516012017356021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16691610201010674678237347 25037415301516012017356021)
                    ·
                      refine ⟨2347257684517126126627127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25037415301516012017356021 2347257684517126126627127)
                      ·
                        rfl

theorem cell23_4571268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 2, 3, 1, 1, 5].length) (baseStart_4571268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4571268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4571268 prefixEnd_4571268 := by exact prefixLift 4571268
  have htrace : WordTrace (prefixWord ++ tailWord_4571268) baseStart_4571268 baseEnd_4571268 := by
    simpa [prefixWord, tailWord_4571268, baseEnd_4571268] using wordTrace_append hprefix tailTrace_4571268
  have hstable : (prefixWord ++ tailWord_4571268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4571268).length < 2 ^ (prefixWord ++ tailWord_4571268).sum := by decide
  have hdescent : baseEnd_4571268 < baseStart_4571268 := by decide
  rcases family_descends (prefixWord ++ tailWord_4571268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4571292 : List Nat := [2, 2, 3, 2, 1, 1, 5, 1, 2, 4]
def baseStart_4571292 : Nat := 118140960795 + 4571292 * 2 ^ 59
def prefixEnd_4571292 : Nat := 4983230072969 + 3 ^ 40 * 4571292 * 2
def baseEnd_4571292 : Nat := 782423336017611344242339

theorem tailTrace_4571292 : CollatzResearch.WordTrace tailWord_4571292 prefixEnd_4571292 782423336017611344242339 := by
  unfold tailWord_4571292
  simp only [CollatzResearch.WordTrace]
  refine ⟨83364358277498636681426065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111152477703331515575234753 83364358277498636681426065)
  ·
    refine ⟨62523268708123977511069549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83364358277498636681426065 62523268708123977511069549)
    ·
      refine ⟨23446225765546491566651081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 62523268708123977511069549 23446225765546491566651081)
      ·
        refine ⟨17584669324159868674988311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23446225765546491566651081 17584669324159868674988311)
        ·
          refine ⟨26377003986239803012482467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17584669324159868674988311 26377003986239803012482467)
          ·
            refine ⟨39565505979359704518723701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26377003986239803012482467 39565505979359704518723701)
            ·
              refine ⟨3709266185564972298630347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 39565505979359704518723701 3709266185564972298630347)
              ·
                refine ⟨5563899278347458447945521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3709266185564972298630347 5563899278347458447945521)
                ·
                  refine ⟨4172924458760593835959141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5563899278347458447945521 4172924458760593835959141)
                  ·
                    refine ⟨782423336017611344242339, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4172924458760593835959141 782423336017611344242339)
                    ·
                      rfl

theorem cell23_4571292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 5, 1, 2, 4].length) (baseStart_4571292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4571292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4571292 prefixEnd_4571292 := by exact prefixLift 4571292
  have htrace : WordTrace (prefixWord ++ tailWord_4571292) baseStart_4571292 baseEnd_4571292 := by
    simpa [prefixWord, tailWord_4571292, baseEnd_4571292] using wordTrace_append hprefix tailTrace_4571292
  have hstable : (prefixWord ++ tailWord_4571292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4571292).length < 2 ^ (prefixWord ++ tailWord_4571292).sum := by decide
  have hdescent : baseEnd_4571292 < baseStart_4571292 := by decide
  rcases family_descends (prefixWord ++ tailWord_4571292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4571295 : List Nat := [1, 1, 2, 6, 1, 1, 3, 1, 1, 2, 4]
def baseStart_4571295 : Nat := 118140960795 + 4571295 * 2 ^ 59
def prefixEnd_4571295 : Nat := 4983230072969 + 3 ^ 40 * 4571295 * 2
def baseEnd_4571295 : Nat := 2347271548494797520989503

theorem tailTrace_4571295 : CollatzResearch.WordTrace tailWord_4571295 prefixEnd_4571295 2347271548494797520989503 := by
  unfold tailWord_4571295
  simp only [CollatzResearch.WordTrace]
  refine ⟨166728825973986404875211339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111152550649324269916807559 166728825973986404875211339)
  ·
    refine ⟨250093238960979607312817009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 166728825973986404875211339 250093238960979607312817009)
    ·
      refine ⟨187569929220734705484612757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 250093238960979607312817009 187569929220734705484612757)
      ·
        refine ⟨8792340432221939319591223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 187569929220734705484612757 8792340432221939319591223)
        ·
          refine ⟨13188510648332908979386835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8792340432221939319591223 13188510648332908979386835)
          ·
            refine ⟨19782765972499363469080253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13188510648332908979386835 19782765972499363469080253)
            ·
              refine ⟨7418537239687261300905095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19782765972499363469080253 7418537239687261300905095)
              ·
                refine ⟨11127805859530891951357643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7418537239687261300905095 11127805859530891951357643)
                ·
                  refine ⟨16691708789296337927036465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11127805859530891951357643 16691708789296337927036465)
                  ·
                    refine ⟨12518781591972253445277349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16691708789296337927036465 12518781591972253445277349)
                    ·
                      refine ⟨2347271548494797520989503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12518781591972253445277349 2347271548494797520989503)
                      ·
                        rfl

theorem cell23_4571295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 3, 1, 1, 2, 4].length) (baseStart_4571295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4571295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4571295 prefixEnd_4571295 := by exact prefixLift 4571295
  have htrace : WordTrace (prefixWord ++ tailWord_4571295) baseStart_4571295 baseEnd_4571295 := by
    simpa [prefixWord, tailWord_4571295, baseEnd_4571295] using wordTrace_append hprefix tailTrace_4571295
  have hstable : (prefixWord ++ tailWord_4571295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4571295).length < 2 ^ (prefixWord ++ tailWord_4571295).sum := by decide
  have hdescent : baseEnd_4571295 < baseStart_4571295 := by decide
  rcases family_descends (prefixWord ++ tailWord_4571295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4571310 : List Nat := [4, 1, 4, 2, 2, 1, 1, 3, 1, 1, 3]
def baseStart_4571310 : Nat := 118140960795 + 4571310 * 2 ^ 59
def prefixEnd_4571310 : Nat := 4983230072969 + 3 ^ 40 * 4571310 * 2
def baseEnd_4571310 : Nat := 2347279250704614962301935

theorem tailTrace_4571310 : CollatzResearch.WordTrace tailWord_4571310 prefixEnd_4571310 2347279250704614962301935 := by
  unfold tailWord_4571310
  simp only [CollatzResearch.WordTrace]
  refine ⟨20841171633616507804625923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 111152915379288041624671589 20841171633616507804625923)
  ·
    refine ⟨31261757450424761706938885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20841171633616507804625923 31261757450424761706938885)
    ·
      refine ⟨5861579521954642820051041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 31261757450424761706938885 5861579521954642820051041)
      ·
        refine ⟨4396184641465982115038281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5861579521954642820051041 4396184641465982115038281)
        ·
          refine ⟨3297138481099486586278711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4396184641465982115038281 3297138481099486586278711)
          ·
            refine ⟨4945707721649229879418067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3297138481099486586278711 4945707721649229879418067)
            ·
              refine ⟨7418561582473844819127101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4945707721649229879418067 7418561582473844819127101)
              ·
                refine ⟨2781960593427691807172663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7418561582473844819127101 2781960593427691807172663)
                ·
                  refine ⟨4172940890141537710758995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2781960593427691807172663 4172940890141537710758995)
                  ·
                    refine ⟨6259411335212306566138493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4172940890141537710758995 6259411335212306566138493)
                    ·
                      refine ⟨2347279250704614962301935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6259411335212306566138493 2347279250704614962301935)
                      ·
                        rfl

theorem cell23_4571310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 2, 1, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 2, 1, 1, 3, 1, 1, 3].length) (baseStart_4571310 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4571310 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4571310 prefixEnd_4571310 := by exact prefixLift 4571310
  have htrace : WordTrace (prefixWord ++ tailWord_4571310) baseStart_4571310 baseEnd_4571310 := by
    simpa [prefixWord, tailWord_4571310, baseEnd_4571310] using wordTrace_append hprefix tailTrace_4571310
  have hstable : (prefixWord ++ tailWord_4571310).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4571310).length < 2 ^ (prefixWord ++ tailWord_4571310).sum := by decide
  have hdescent : baseEnd_4571310 < baseStart_4571310 := by decide
  rcases family_descends (prefixWord ++ tailWord_4571310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4571325 : List Nat := [1, 4, 1, 2, 1, 1, 1, 2, 5, 3, 2]
def baseStart_4571325 : Nat := 118140960795 + 4571325 * 2 ^ 59
def prefixEnd_4571325 : Nat := 4983230072969 + 3 ^ 40 * 4571325 * 2
def baseEnd_4571325 : Nat := 2347286952914432403614365

theorem tailTrace_4571325 : CollatzResearch.WordTrace tailWord_4571325 prefixEnd_4571325 2347286952914432403614365 := by
  unfold tailWord_4571325
  simp only [CollatzResearch.WordTrace]
  refine ⟨166729920163877719998803429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111153280109251813332535619 166729920163877719998803429)
  ·
    refine ⟨31261860030727072499775643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 166729920163877719998803429 31261860030727072499775643)
    ·
      refine ⟨46892790046090608749663465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31261860030727072499775643 46892790046090608749663465)
      ·
        refine ⟨35169592534567956562247599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46892790046090608749663465 35169592534567956562247599)
        ·
          refine ⟨52754388801851934843371399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35169592534567956562247599 52754388801851934843371399)
          ·
            refine ⟨79131583202777902265057099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52754388801851934843371399 79131583202777902265057099)
            ·
              refine ⟨118697374804166853397585649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 79131583202777902265057099 118697374804166853397585649)
              ·
                refine ⟨89023031103125140048189237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 118697374804166853397585649 89023031103125140048189237)
                ·
                  refine ⟨8345909165917981879517741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 89023031103125140048189237 8345909165917981879517741)
                  ·
                    refine ⟨3129715937219243204819153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8345909165917981879517741 3129715937219243204819153)
                    ·
                      refine ⟨2347286952914432403614365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3129715937219243204819153 2347286952914432403614365)
                      ·
                        rfl

theorem cell23_4571325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 2, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 2, 5, 3, 2].length) (baseStart_4571325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4571325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4571325 prefixEnd_4571325 := by exact prefixLift 4571325
  have htrace : WordTrace (prefixWord ++ tailWord_4571325) baseStart_4571325 baseEnd_4571325 := by
    simpa [prefixWord, tailWord_4571325, baseEnd_4571325] using wordTrace_append hprefix tailTrace_4571325
  have hstable : (prefixWord ++ tailWord_4571325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4571325).length < 2 ^ (prefixWord ++ tailWord_4571325).sum := by decide
  have hdescent : baseEnd_4571325 < baseStart_4571325 := by decide
  rcases family_descends (prefixWord ++ tailWord_4571325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4571332 : List Nat := [2, 3, 3, 1, 2, 1, 2, 1, 4, 1, 3]
def baseStart_4571332 : Nat := 118140960795 + 4571332 * 2 ^ 59
def prefixEnd_4571332 : Nat := 4983230072969 + 3 ^ 40 * 4571332 * 2
def baseEnd_4571332 : Nat := 2347290547279013876226833

theorem tailTrace_4571332 : CollatzResearch.WordTrace tailWord_4571332 prefixEnd_4571332 2347290547279013876226833 := by
  unfold tailWord_4571332
  simp only [CollatzResearch.WordTrace]
  refine ⟨83365087737426180097154125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111153450316568240129538833 83365087737426180097154125)
  ·
    refine ⟨31261907901534817536432797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 83365087737426180097154125 31261907901534817536432797)
    ·
      refine ⟨11723215463075556576162299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31261907901534817536432797 11723215463075556576162299)
      ·
        refine ⟨17584823194613334864243449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11723215463075556576162299 17584823194613334864243449)
        ·
          refine ⟨13188617395960001148182587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17584823194613334864243449 13188617395960001148182587)
          ·
            refine ⟨19782926093940001722273881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13188617395960001148182587 19782926093940001722273881)
            ·
              refine ⟨14837194570455001291705411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19782926093940001722273881 14837194570455001291705411)
              ·
                refine ⟨22255791855682501937558117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14837194570455001291705411 22255791855682501937558117)
                ·
                  refine ⟨4172960972940469113292147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22255791855682501937558117 4172960972940469113292147)
                  ·
                    refine ⟨6259441459410703669938221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4172960972940469113292147 6259441459410703669938221)
                    ·
                      refine ⟨2347290547279013876226833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6259441459410703669938221 2347290547279013876226833)
                      ·
                        rfl

theorem cell23_4571332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 2, 1, 4, 1, 3].length) (baseStart_4571332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4571332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4571332 prefixEnd_4571332 := by exact prefixLift 4571332
  have htrace : WordTrace (prefixWord ++ tailWord_4571332) baseStart_4571332 baseEnd_4571332 := by
    simpa [prefixWord, tailWord_4571332, baseEnd_4571332] using wordTrace_append hprefix tailTrace_4571332
  have hstable : (prefixWord ++ tailWord_4571332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4571332).length < 2 ^ (prefixWord ++ tailWord_4571332).sum := by decide
  have hdescent : baseEnd_4571332 < baseStart_4571332 := by decide
  rcases family_descends (prefixWord ++ tailWord_4571332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4571338 : List Nat := [3, 1, 2, 1, 3, 1, 2, 1, 2, 3, 4]
def baseStart_4571338 : Nat := 118140960795 + 4571338 * 2 ^ 59
def prefixEnd_4571338 : Nat := 4983230072969 + 3 ^ 40 * 4571338 * 2
def baseEnd_4571338 : Nat := 2347293628162940852751805

theorem tailTrace_4571338 : CollatzResearch.WordTrace tailWord_4571338 prefixEnd_4571338 2347293628162940852751805 := by
  unfold tailWord_4571338
  simp only [CollatzResearch.WordTrace]
  refine ⟨41682598578207655804756667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 111153596208553748812684445 41682598578207655804756667)
  ·
    refine ⟨62523897867311483707135001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41682598578207655804756667 62523897867311483707135001)
    ·
      refine ⟨46892923400483612780351251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62523897867311483707135001 46892923400483612780351251)
      ·
        refine ⟨70339385100725419170526877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46892923400483612780351251 70339385100725419170526877)
        ·
          refine ⟨26377269412772032188947579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 70339385100725419170526877 26377269412772032188947579)
          ·
            refine ⟨39565904119158048283421369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26377269412772032188947579 39565904119158048283421369)
            ·
              refine ⟨29674428089368536212566027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39565904119158048283421369 29674428089368536212566027)
              ·
                refine ⟨44511642134052804318849041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29674428089368536212566027 44511642134052804318849041)
                ·
                  refine ⟨33383731600539603239136781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 44511642134052804318849041 33383731600539603239136781)
                  ·
                    refine ⟨12518899350202351214676293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 33383731600539603239136781 12518899350202351214676293)
                    ·
                      refine ⟨2347293628162940852751805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12518899350202351214676293 2347293628162940852751805)
                      ·
                        rfl

theorem cell23_4571338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 2, 1, 2, 3, 4].length) (baseStart_4571338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4571338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4571338 prefixEnd_4571338 := by exact prefixLift 4571338
  have htrace : WordTrace (prefixWord ++ tailWord_4571338) baseStart_4571338 baseEnd_4571338 := by
    simpa [prefixWord, tailWord_4571338, baseEnd_4571338] using wordTrace_append hprefix tailTrace_4571338
  have hstable : (prefixWord ++ tailWord_4571338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4571338).length < 2 ^ (prefixWord ++ tailWord_4571338).sum := by decide
  have hdescent : baseEnd_4571338 < baseStart_4571338 := by decide
  rcases family_descends (prefixWord ++ tailWord_4571338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4571349 : List Nat := [1, 3, 2, 4, 2, 1, 1, 3, 2, 1, 3]
def baseStart_4571349 : Nat := 118140960795 + 4571349 * 2 ^ 59
def prefixEnd_4571349 : Nat := 4983230072969 + 3 ^ 40 * 4571349 * 2
def baseEnd_4571349 : Nat := 2347299276450140309714255

theorem tailTrace_4571349 : CollatzResearch.WordTrace tailWord_4571349 prefixEnd_4571349 2347299276450140309714255 := by
  unfold tailWord_4571349
  simp only [CollatzResearch.WordTrace]
  refine ⟨166730795515790772097677101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111153863677193848065118067 166730795515790772097677101)
  ·
    refine ⟨62524048318421539536628913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 166730795515790772097677101 62524048318421539536628913)
    ·
      refine ⟨46893036238816154652471685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62524048318421539536628913 46893036238816154652471685)
      ·
        refine ⟨8792444294778028997338441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 46893036238816154652471685 8792444294778028997338441)
        ·
          refine ⟨6594333221083521748003831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8792444294778028997338441 6594333221083521748003831)
          ·
            refine ⟨9891499831625282622005747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6594333221083521748003831 9891499831625282622005747)
            ·
              refine ⟨14837249747437923933008621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9891499831625282622005747 14837249747437923933008621)
              ·
                refine ⟨5563968655289221474878233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14837249747437923933008621 5563968655289221474878233)
                ·
                  refine ⟨4172976491466916106158675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5563968655289221474878233 4172976491466916106158675)
                  ·
                    refine ⟨6259464737200374159238013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4172976491466916106158675 6259464737200374159238013)
                    ·
                      refine ⟨2347299276450140309714255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6259464737200374159238013 2347299276450140309714255)
                      ·
                        rfl

theorem cell23_4571349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 1, 1, 3, 2, 1, 3].length) (baseStart_4571349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4571349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4571349 prefixEnd_4571349 := by exact prefixLift 4571349
  have htrace : WordTrace (prefixWord ++ tailWord_4571349) baseStart_4571349 baseEnd_4571349 := by
    simpa [prefixWord, tailWord_4571349, baseEnd_4571349] using wordTrace_append hprefix tailTrace_4571349
  have hstable : (prefixWord ++ tailWord_4571349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4571349).length < 2 ^ (prefixWord ++ tailWord_4571349).sum := by decide
  have hdescent : baseEnd_4571349 < baseStart_4571349 := by decide
  rcases family_descends (prefixWord ++ tailWord_4571349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4571395 : List Nat := [1, 1, 1, 3, 2, 3, 3, 4, 5]
def baseStart_4571395 : Nat := 118140960795 + 4571395 * 2 ^ 59
def prefixEnd_4571395 : Nat := 4983230072969 + 3 ^ 40 * 4571395 * 2
def baseEnd_4571395 : Nat := 260813655173360792193227

theorem tailTrace_4571395 : CollatzResearch.WordTrace tailWord_4571395 prefixEnd_4571395 260813655173360792193227 := by
  unfold tailWord_4571395
  simp only [CollatzResearch.WordTrace]
  refine ⟨166732473273624121953851639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111154982182416081302567759 166732473273624121953851639)
  ·
    refine ⟨250098709910436182930777459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 166732473273624121953851639 250098709910436182930777459)
    ·
      refine ⟨375148064865654274396166189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 250098709910436182930777459 375148064865654274396166189)
      ·
        refine ⟨140680524324620352898562321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 375148064865654274396166189 140680524324620352898562321)
        ·
          refine ⟨105510393243465264673921741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 140680524324620352898562321 105510393243465264673921741)
          ·
            refine ⟨39566397466299474252720653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 105510393243465264673921741 39566397466299474252720653)
            ·
              refine ⟨14837399049862302844770245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 39566397466299474252720653 14837399049862302844770245)
              ·
                refine ⟨2782012321849181783394421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14837399049862302844770245 2782012321849181783394421)
                ·
                  refine ⟨260813655173360792193227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2782012321849181783394421 260813655173360792193227)
                  ·
                    rfl

theorem cell23_4571395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 3, 4, 5].length) (baseStart_4571395 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4571395 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4571395 prefixEnd_4571395 := by exact prefixLift 4571395
  have htrace : WordTrace (prefixWord ++ tailWord_4571395) baseStart_4571395 baseEnd_4571395 := by
    simpa [prefixWord, tailWord_4571395, baseEnd_4571395] using wordTrace_append hprefix tailTrace_4571395
  have hstable : (prefixWord ++ tailWord_4571395).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4571395).length < 2 ^ (prefixWord ++ tailWord_4571395).sum := by decide
  have hdescent : baseEnd_4571395 < baseStart_4571395 := by decide
  rcases family_descends (prefixWord ++ tailWord_4571395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4571425 : List Nat := [1, 2, 3, 2, 1, 1, 5, 1, 2, 5]
def baseStart_4571425 : Nat := 118140960795 + 4571425 * 2 ^ 59
def prefixEnd_4571425 : Nat := 4983230072969 + 3 ^ 40 * 4571425 * 2
def baseEnd_4571425 : Nat := 782446100326627337454635

theorem tailTrace_4571425 : CollatzResearch.WordTrace tailWord_4571425 prefixEnd_4571425 782446100326627337454635 := by
  unfold tailWord_4571425
  simp only [CollatzResearch.WordTrace]
  refine ⟨166733567463515437077443729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111155711642343624718295819 166733567463515437077443729)
  ·
    refine ⟨125050175597636577808082797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 166733567463515437077443729 125050175597636577808082797)
    ·
      refine ⟨46893815849113716678031049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 125050175597636577808082797 46893815849113716678031049)
      ·
        refine ⟨35170361886835287508523287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46893815849113716678031049 35170361886835287508523287)
        ·
          refine ⟨52755542830252931262784931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35170361886835287508523287 52755542830252931262784931)
          ·
            refine ⟨79133314245379396894177397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52755542830252931262784931 79133314245379396894177397)
            ·
              refine ⟨7418748210504318458829131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 79133314245379396894177397 7418748210504318458829131)
              ·
                refine ⟨11128122315756477688243697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7418748210504318458829131 11128122315756477688243697)
                ·
                  refine ⟨8346091736817358266182773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11128122315756477688243697 8346091736817358266182773)
                  ·
                    refine ⟨782446100326627337454635, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8346091736817358266182773 782446100326627337454635)
                    ·
                      rfl

theorem cell23_4571425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 5, 1, 2, 5].length) (baseStart_4571425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4571425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4571425 prefixEnd_4571425 := by exact prefixLift 4571425
  have htrace : WordTrace (prefixWord ++ tailWord_4571425) baseStart_4571425 baseEnd_4571425 := by
    simpa [prefixWord, tailWord_4571425, baseEnd_4571425] using wordTrace_append hprefix tailTrace_4571425
  have hstable : (prefixWord ++ tailWord_4571425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4571425).length < 2 ^ (prefixWord ++ tailWord_4571425).sum := by decide
  have hdescent : baseEnd_4571425 < baseStart_4571425 := by decide
  rcases family_descends (prefixWord ++ tailWord_4571425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4571445 : List Nat := [1, 3, 3, 1, 2, 1, 2, 1, 4, 1, 4]
def baseStart_4571445 : Nat := 118140960795 + 4571445 * 2 ^ 59
def prefixEnd_4571445 : Nat := 4983230072969 + 3 ^ 40 * 4571445 * 2
def baseEnd_4571445 : Nat := 2347348570592971934113813

theorem tailTrace_4571445 : CollatzResearch.WordTrace tailWord_4571445 prefixEnd_4571445 2347348570592971934113813 := by
  unfold tailWord_4571445
  simp only [CollatzResearch.WordTrace]
  refine ⟨166734296923442980493171789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111156197948961986995447859 166734296923442980493171789)
  ·
    refine ⟨62525361346291117684939421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 166734296923442980493171789 62525361346291117684939421)
    ·
      refine ⟨23447010504859169131852283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 62525361346291117684939421 23447010504859169131852283)
      ·
        refine ⟨35170515757288753697778425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23447010504859169131852283 35170515757288753697778425)
        ·
          refine ⟨26377886817966565273333819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35170515757288753697778425 26377886817966565273333819)
          ·
            refine ⟨39566830226949847910000729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26377886817966565273333819 39566830226949847910000729)
            ·
              refine ⟨29675122670212385932500547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39566830226949847910000729 29675122670212385932500547)
              ·
                refine ⟨44512684005318578898750821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29675122670212385932500547 44512684005318578898750821)
                ·
                  refine ⟨8346128250997233543515779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 44512684005318578898750821 8346128250997233543515779)
                  ·
                    refine ⟨12519192376495850315273669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8346128250997233543515779 12519192376495850315273669)
                    ·
                      refine ⟨2347348570592971934113813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12519192376495850315273669 2347348570592971934113813)
                      ·
                        rfl

theorem cell23_4571445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 2, 1, 4, 1, 4].length) (baseStart_4571445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4571445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4571445 prefixEnd_4571445 := by exact prefixLift 4571445
  have htrace : WordTrace (prefixWord ++ tailWord_4571445) baseStart_4571445 baseEnd_4571445 := by
    simpa [prefixWord, tailWord_4571445, baseEnd_4571445] using wordTrace_append hprefix tailTrace_4571445
  have hstable : (prefixWord ++ tailWord_4571445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4571445).length < 2 ^ (prefixWord ++ tailWord_4571445).sum := by decide
  have hdescent : baseEnd_4571445 < baseStart_4571445 := by decide
  rcases family_descends (prefixWord ++ tailWord_4571445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4571448 : List Nat := [2, 1, 2, 1, 3, 1, 2, 1, 2, 3, 5]
def baseStart_4571448 : Nat := 118140960795 + 4571448 * 2 ^ 59
def prefixEnd_4571448 : Nat := 4983230072969 + 3 ^ 40 * 4571448 * 2
def baseEnd_4571448 : Nat := 2347350111034935422376299

theorem tailTrace_4571448 : CollatzResearch.WordTrace tailWord_4571448 prefixEnd_4571448 2347350111034935422376299 := by
  unfold tailWord_4571448
  simp only [CollatzResearch.WordTrace]
  refine ⟨83367203171216056002765499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111156270894954741337020665 83367203171216056002765499)
  ·
    refine ⟨125050804756824084004148249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83367203171216056002765499 125050804756824084004148249)
    ·
      refine ⟨93788103567618063003111187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 125050804756824084004148249 93788103567618063003111187)
      ·
        refine ⟨140682155351427094504666781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93788103567618063003111187 140682155351427094504666781)
        ·
          refine ⟨52755808256785160439250043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 140682155351427094504666781 52755808256785160439250043)
          ·
            refine ⟨79133712385177740658875065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52755808256785160439250043 79133712385177740658875065)
            ·
              refine ⟨59350284288883305494156299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 79133712385177740658875065 59350284288883305494156299)
              ·
                refine ⟨89025426433324958241234449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 59350284288883305494156299 89025426433324958241234449)
                ·
                  refine ⟨66769069824993718680925837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 89025426433324958241234449 66769069824993718680925837)
                  ·
                    refine ⟨25038401184372644505347189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 66769069824993718680925837 25038401184372644505347189)
                    ·
                      refine ⟨2347350111034935422376299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25038401184372644505347189 2347350111034935422376299)
                      ·
                        rfl

theorem cell23_4571448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 2, 1, 2, 3, 5].length) (baseStart_4571448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4571448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4571448 prefixEnd_4571448 := by exact prefixLift 4571448
  have htrace : WordTrace (prefixWord ++ tailWord_4571448) baseStart_4571448 baseEnd_4571448 := by
    simpa [prefixWord, tailWord_4571448, baseEnd_4571448] using wordTrace_append hprefix tailTrace_4571448
  have hstable : (prefixWord ++ tailWord_4571448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4571448).length < 2 ^ (prefixWord ++ tailWord_4571448).sum := by decide
  have hdescent : baseEnd_4571448 < baseStart_4571448 := by decide
  rcases family_descends (prefixWord ++ tailWord_4571448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4571506 : List Nat := [3, 2, 1, 2, 1, 4, 3, 2, 1, 4]
def baseStart_4571506 : Nat := 118140960795 + 4571506 * 2 ^ 59
def prefixEnd_4571506 : Nat := 4983230072969 + 3 ^ 40 * 4571506 * 2
def baseEnd_4571506 : Nat := 782459964304298731817011

theorem tailTrace_4571506 : CollatzResearch.WordTrace tailWord_4571506 prefixEnd_4571506 782459964304298731817011 := by
  unfold tailWord_4571506
  simp only [CollatzResearch.WordTrace]
  refine ⟨41684130444055496977785593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 111157681184147991940761581 41684130444055496977785593)
  ·
    refine ⟨31263097833041622733339195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41684130444055496977785593 31263097833041622733339195)
    ·
      refine ⟨46894646749562434100008793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31263097833041622733339195 46894646749562434100008793)
      ·
        refine ⟨35170985062171825575006595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46894646749562434100008793 35170985062171825575006595)
        ·
          refine ⟨52756477593257738362509893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35170985062171825575006595 52756477593257738362509893)
          ·
            refine ⟨9891839548735825942970605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 52756477593257738362509893 9891839548735825942970605)
            ·
              refine ⟨3709439830775934728613977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9891839548735825942970605 3709439830775934728613977)
              ·
                refine ⟨2782079873081951046460483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3709439830775934728613977 2782079873081951046460483)
                ·
                  refine ⟨4173119809622926569690725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2782079873081951046460483 4173119809622926569690725)
                  ·
                    refine ⟨782459964304298731817011, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4173119809622926569690725 782459964304298731817011)
                    ·
                      rfl

theorem cell23_4571506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 4, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 4, 3, 2, 1, 4].length) (baseStart_4571506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4571506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4571506 prefixEnd_4571506 := by exact prefixLift 4571506
  have htrace : WordTrace (prefixWord ++ tailWord_4571506) baseStart_4571506 baseEnd_4571506 := by
    simpa [prefixWord, tailWord_4571506, baseEnd_4571506] using wordTrace_append hprefix tailTrace_4571506
  have hstable : (prefixWord ++ tailWord_4571506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4571506).length < 2 ^ (prefixWord ++ tailWord_4571506).sum := by decide
  have hdescent : baseEnd_4571506 < baseStart_4571506 := by decide
  rcases family_descends (prefixWord ++ tailWord_4571506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4571532 : List Nat := [2, 2, 1, 2, 1, 4, 3, 2, 1, 5]
def baseStart_4571532 : Nat := 118140960795 + 4571532 * 2 ^ 59
def prefixEnd_4571532 : Nat := 4983230072969 + 3 ^ 40 * 4571532 * 2
def baseEnd_4571532 : Nat := 782464414469971031241971

theorem tailTrace_4571532 : CollatzResearch.WordTrace tailWord_4571532 prefixEnd_4571532 782464414469971031241971 := by
  unfold tailWord_4571532
  simp only [CollatzResearch.WordTrace]
  refine ⟨83368735037063897175794425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111158313382751862901059233 83368735037063897175794425)
  ·
    refine ⟨62526551277797922881845819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83368735037063897175794425 62526551277797922881845819)
    ·
      refine ⟨93789826916696884322768729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62526551277797922881845819 93789826916696884322768729)
      ·
        refine ⟨70342370187522663242076547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 93789826916696884322768729 70342370187522663242076547)
        ·
          refine ⟨105513555281283994863114821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70342370187522663242076547 105513555281283994863114821)
          ·
            refine ⟨19783791615240749036834029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 105513555281283994863114821 19783791615240749036834029)
            ·
              refine ⟨7418921855715280888812761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19783791615240749036834029 7418921855715280888812761)
              ·
                refine ⟨5564191391786460666609571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7418921855715280888812761 5564191391786460666609571)
                ·
                  refine ⟨8346287087679690999914357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5564191391786460666609571 8346287087679690999914357)
                  ·
                    refine ⟨782464414469971031241971, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8346287087679690999914357 782464414469971031241971)
                    ·
                      rfl

theorem cell23_4571532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 3, 2, 1, 5].length) (baseStart_4571532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4571532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4571532 prefixEnd_4571532 := by exact prefixLift 4571532
  have htrace : WordTrace (prefixWord ++ tailWord_4571532) baseStart_4571532 baseEnd_4571532 := by
    simpa [prefixWord, tailWord_4571532, baseEnd_4571532] using wordTrace_append hprefix tailTrace_4571532
  have hstable : (prefixWord ++ tailWord_4571532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4571532).length < 2 ^ (prefixWord ++ tailWord_4571532).sum := by decide
  have hdescent : baseEnd_4571532 < baseStart_4571532 := by decide
  rcases family_descends (prefixWord ++ tailWord_4571532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4571545 : List Nat := [1, 2, 1, 2, 1, 4, 3, 2, 1, 6]
def baseStart_4571545 : Nat := 118140960795 + 4571545 * 2 ^ 59
def prefixEnd_4571545 : Nat := 4983230072969 + 3 ^ 40 * 4571545 * 2
def baseEnd_4571545 : Nat := 782466639552807180954451

theorem tailTrace_4571545 : CollatzResearch.WordTrace tailWord_4571545 prefixEnd_4571545 782466639552807180954451 := by
  unfold tailWord_4571545
  simp only [CollatzResearch.WordTrace]
  refine ⟨166737944223080697571812089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111158629482053798381208059 166737944223080697571812089)
  ·
    refine ⟨125053458167310523178859067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 166737944223080697571812089 125053458167310523178859067)
    ·
      refine ⟨187580187250965784768288601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125053458167310523178859067 187580187250965784768288601)
      ·
        refine ⟨140685140438224338576216451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 187580187250965784768288601 140685140438224338576216451)
        ·
          refine ⟨211027710657336507864324677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 140685140438224338576216451 211027710657336507864324677)
          ·
            refine ⟨39567695748250595224560877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 211027710657336507864324677 39567695748250595224560877)
            ·
              refine ⟨14837885905593973209210329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 39567695748250595224560877 14837885905593973209210329)
              ·
                refine ⟨11128414429195479906907747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14837885905593973209210329 11128414429195479906907747)
                ·
                  refine ⟨16692621643793219860361621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11128414429195479906907747 16692621643793219860361621)
                  ·
                    refine ⟨782466639552807180954451, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16692621643793219860361621 782466639552807180954451)
                    ·
                      rfl

theorem cell23_4571545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 3, 2, 1, 6].length) (baseStart_4571545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4571545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4571545 prefixEnd_4571545 := by exact prefixLift 4571545
  have htrace : WordTrace (prefixWord ++ tailWord_4571545) baseStart_4571545 baseEnd_4571545 := by
    simpa [prefixWord, tailWord_4571545, baseEnd_4571545] using wordTrace_append hprefix tailTrace_4571545
  have hstable : (prefixWord ++ tailWord_4571545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4571545).length < 2 ^ (prefixWord ++ tailWord_4571545).sum := by decide
  have hdescent : baseEnd_4571545 < baseStart_4571545 := by decide
  rcases family_descends (prefixWord ++ tailWord_4571545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
