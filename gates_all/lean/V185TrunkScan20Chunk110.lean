import V185TrunkScan20Chunk109

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental

namespace V185TrunkScan20Incremental

def tailWord_667845 : List Nat := [1, 3, 1, 1, 1, 1, 4, 1, 7]
def baseStart_667845 : Nat := 118140960795 + 667845 * 2 ^ 59
def prefixEnd_667845 : Nat := 4983230072969 + 3 ^ 40 * 667845 * 2
def baseEnd_667845 : Nat := 304822655735150921836571

theorem tailTrace_667845 : CollatzResearch.WordTrace tailWord_667845 prefixEnd_667845 304822655735150921836571 := by
  unfold tailWord_667845
  simp only [CollatzResearch.WordTrace]
  refine ⟨24358308265519098690420989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16238872177012732460280659 24358308265519098690420989)
  ·
    refine ⟨9134365599569662008907871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24358308265519098690420989 9134365599569662008907871)
    ·
      refine ⟨13701548399354493013361807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9134365599569662008907871 13701548399354493013361807)
      ·
        refine ⟨20552322599031739520042711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13701548399354493013361807 20552322599031739520042711)
        ·
          refine ⟨30828483898547609280064067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20552322599031739520042711 30828483898547609280064067)
          ·
            refine ⟨46242725847821413920096101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30828483898547609280064067 46242725847821413920096101)
            ·
              refine ⟨8670511096466515110018019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 46242725847821413920096101 8670511096466515110018019)
              ·
                refine ⟨13005766644699772665027029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8670511096466515110018019 13005766644699772665027029)
                ·
                  refine ⟨304822655735150921836571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13005766644699772665027029 304822655735150921836571)
                  ·
                    rfl

theorem cell20_667845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 4, 1, 7].length) (baseStart_667845 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_667845 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_667845 prefixEnd_667845 := by exact prefixLift 667845
  have htrace : WordTrace (prefixWord ++ tailWord_667845) baseStart_667845 baseEnd_667845 := by
    simpa [prefixWord, tailWord_667845, baseEnd_667845] using wordTrace_append hprefix tailTrace_667845
  have hstable : (prefixWord ++ tailWord_667845).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_667845).length < 2 ^ (prefixWord ++ tailWord_667845).sum := by decide
  have hdescent : baseEnd_667845 < baseStart_667845 := by decide
  rcases family_descends (prefixWord ++ tailWord_667845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_667848 : List Nat := [2, 1, 3, 1, 2, 1, 1, 7, 2]
def baseStart_667848 : Nat := 118140960795 + 667848 * 2 ^ 59
def prefixEnd_667848 : Nat := 4983230072969 + 3 ^ 40 * 667848 * 2
def baseEnd_667848 : Nat := 304824025016896244736559

theorem tailTrace_667848 : CollatzResearch.WordTrace tailWord_667848 prefixEnd_667848 304824025016896244736559 := by
  unfold tailWord_667848
  simp only [CollatzResearch.WordTrace]
  refine ⟨12179208842254115101390099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16238945123005486801853465 12179208842254115101390099)
  ·
    refine ⟨18268813263381172652085149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12179208842254115101390099 18268813263381172652085149)
    ·
      refine ⟨6850804973767939744531931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18268813263381172652085149 6850804973767939744531931)
      ·
        refine ⟨10276207460651909616797897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6850804973767939744531931 10276207460651909616797897)
        ·
          refine ⟨7707155595488932212598423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10276207460651909616797897 7707155595488932212598423)
          ·
            refine ⟨11560733393233398318897635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7707155595488932212598423 11560733393233398318897635)
            ·
              refine ⟨17341100089850097478346453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11560733393233398318897635 17341100089850097478346453)
              ·
                refine ⟨406432033355861659648745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 17341100089850097478346453 406432033355861659648745)
                ·
                  refine ⟨304824025016896244736559, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 406432033355861659648745 304824025016896244736559)
                  ·
                    rfl

theorem cell20_667848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 7, 2].length) (baseStart_667848 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_667848 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_667848 prefixEnd_667848 := by exact prefixLift 667848
  have htrace : WordTrace (prefixWord ++ tailWord_667848) baseStart_667848 baseEnd_667848 := by
    simpa [prefixWord, tailWord_667848, baseEnd_667848] using wordTrace_append hprefix tailTrace_667848
  have hstable : (prefixWord ++ tailWord_667848).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_667848).length < 2 ^ (prefixWord ++ tailWord_667848).sum := by decide
  have hdescent : baseEnd_667848 < baseStart_667848 := by decide
  rcases family_descends (prefixWord ++ tailWord_667848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_667861 : List Nat := [1, 3, 2, 4, 2, 2, 2, 2, 2]
def baseStart_667861 : Nat := 118140960795 + 667861 * 2 ^ 59
def prefixEnd_667861 : Nat := 4983230072969 + 3 ^ 40 * 667861 * 2
def baseEnd_667861 : Nat := 304829958571125977303173

theorem tailTrace_667861 : CollatzResearch.WordTrace tailWord_667861 prefixEnd_667861 304829958571125977303173 := by
  unfold tailWord_667861
  simp only [CollatzResearch.WordTrace]
  refine ⟨24358891833461133423003437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16239261222307422282002291 24358891833461133423003437)
  ·
    refine ⟨9134584437547925033626289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24358891833461133423003437 9134584437547925033626289)
    ·
      refine ⟨6850938328160943775219717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9134584437547925033626289 6850938328160943775219717)
      ·
        refine ⟨1284550936530176957853697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6850938328160943775219717 1284550936530176957853697)
        ·
          refine ⟨963413202397632718390273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1284550936530176957853697 963413202397632718390273)
          ·
            refine ⟨722559901798224538792705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 963413202397632718390273 722559901798224538792705)
            ·
              refine ⟨541919926348668404094529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 722559901798224538792705 541919926348668404094529)
              ·
                refine ⟨406439944761501303070897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 541919926348668404094529 406439944761501303070897)
                ·
                  refine ⟨304829958571125977303173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 406439944761501303070897 304829958571125977303173)
                  ·
                    rfl

theorem cell20_667861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 2, 2, 2, 2].length) (baseStart_667861 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_667861 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_667861 prefixEnd_667861 := by exact prefixLift 667861
  have htrace : WordTrace (prefixWord ++ tailWord_667861) baseStart_667861 baseEnd_667861 := by
    simpa [prefixWord, tailWord_667861, baseEnd_667861] using wordTrace_append hprefix tailTrace_667861
  have hstable : (prefixWord ++ tailWord_667861).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_667861).length < 2 ^ (prefixWord ++ tailWord_667861).sum := by decide
  have hdescent : baseEnd_667861 < baseStart_667861 := by decide
  rcases family_descends (prefixWord ++ tailWord_667861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_667865 : List Nat := [1, 2, 1, 2, 3, 1, 6, 2, 2]
def baseStart_667865 : Nat := 118140960795 + 667865 * 2 ^ 59
def prefixEnd_667865 : Nat := 4983230072969 + 3 ^ 40 * 667865 * 2
def baseEnd_667865 : Nat := 304831784280119741169823

theorem tailTrace_667865 : CollatzResearch.WordTrace tailWord_667865 prefixEnd_667865 304831784280119741169823 := by
  unfold tailWord_667865
  simp only [CollatzResearch.WordTrace]
  refine ⟨24359037725446642106149049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16239358483631094737432699 24359037725446642106149049)
  ·
    refine ⟨18269278294084981579611787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24359037725446642106149049 18269278294084981579611787)
    ·
      refine ⟨27403917441127472369417681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18269278294084981579611787 27403917441127472369417681)
      ·
        refine ⟨20552938080845604277063261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27403917441127472369417681 20552938080845604277063261)
        ·
          refine ⟨7707351780317101603898723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20552938080845604277063261 7707351780317101603898723)
          ·
            refine ⟨11561027670475652405848085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7707351780317101603898723 11561027670475652405848085)
            ·
              refine ⟨541923172053546206524129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 11561027670475652405848085 541923172053546206524129)
              ·
                refine ⟨406442379040159654893097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 541923172053546206524129 406442379040159654893097)
                ·
                  refine ⟨304831784280119741169823, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 406442379040159654893097 304831784280119741169823)
                  ·
                    rfl

theorem cell20_667865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 6, 2, 2].length) (baseStart_667865 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_667865 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_667865 prefixEnd_667865 := by exact prefixLift 667865
  have htrace : WordTrace (prefixWord ++ tailWord_667865) baseStart_667865 baseEnd_667865 := by
    simpa [prefixWord, tailWord_667865, baseEnd_667865] using wordTrace_append hprefix tailTrace_667865
  have hstable : (prefixWord ++ tailWord_667865).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_667865).length < 2 ^ (prefixWord ++ tailWord_667865).sum := by decide
  have hdescent : baseEnd_667865 < baseStart_667865 := by decide
  rcases family_descends (prefixWord ++ tailWord_667865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_667868 : List Nat := [2, 2, 5, 2, 2, 1, 1, 5]
def baseStart_667868 : Nat := 118140960795 + 667868 * 2 ^ 59
def prefixEnd_667868 : Nat := 4983230072969 + 3 ^ 40 * 667868 * 2
def baseEnd_667868 : Nat := 101611051187288354689937

theorem tailTrace_667868 : CollatzResearch.WordTrace tailWord_667868 prefixEnd_667868 101611051187288354689937 := by
  unfold tailWord_667868
  simp only [CollatzResearch.WordTrace]
  refine ⟨12179573572217886809254129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16239431429623849079005505 12179573572217886809254129)
  ·
    refine ⟨9134680179163415106940597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12179573572217886809254129 9134680179163415106940597)
    ·
      refine ⟨856376266796570166275681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 9134680179163415106940597 856376266796570166275681)
      ·
        refine ⟨642282200097427624706761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 856376266796570166275681 642282200097427624706761)
        ·
          refine ⟨481711650073070718530071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 642282200097427624706761 481711650073070718530071)
          ·
            refine ⟨722567475109606077795107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 481711650073070718530071 722567475109606077795107)
            ·
              refine ⟨1083851212664409116692661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 722567475109606077795107 1083851212664409116692661)
              ·
                refine ⟨101611051187288354689937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1083851212664409116692661 101611051187288354689937)
                ·
                  rfl

theorem cell20_667868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 2, 1, 1, 5].length) (baseStart_667868 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_667868 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_667868 prefixEnd_667868 := by exact prefixLift 667868
  have htrace : WordTrace (prefixWord ++ tailWord_667868) baseStart_667868 baseEnd_667868 := by
    simpa [prefixWord, tailWord_667868, baseEnd_667868] using wordTrace_append hprefix tailTrace_667868
  have hstable : (prefixWord ++ tailWord_667868).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_667868).length < 2 ^ (prefixWord ++ tailWord_667868).sum := by decide
  have hdescent : baseEnd_667868 < baseStart_667868 := by decide
  rcases family_descends (prefixWord ++ tailWord_667868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_667879 : List Nat := [1, 1, 5, 3, 1, 1, 2, 3, 3]
def baseStart_667879 : Nat := 118140960795 + 667879 * 2 ^ 59
def prefixEnd_667879 : Nat := 4983230072969 + 3 ^ 40 * 667879 * 2
def baseEnd_667879 : Nat := 304838174261597914703099

theorem tailTrace_667879 : CollatzResearch.WordTrace tailWord_667879 prefixEnd_667879 304838174261597914703099 := by
  unfold tailWord_667879
  simp only [CollatzResearch.WordTrace]
  refine ⟨24359548347395922497158691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16239698898263948331439127 24359548347395922497158691)
  ·
    refine ⟨36539322521093883745738037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24359548347395922497158691 36539322521093883745738037)
    ·
      refine ⟨3425561486352551601162941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 36539322521093883745738037 3425561486352551601162941)
      ·
        refine ⟨1284585557382206850436103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3425561486352551601162941 1284585557382206850436103)
        ·
          refine ⟨1926878336073310275654155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1284585557382206850436103 1926878336073310275654155)
          ·
            refine ⟨2890317504109965413481233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1926878336073310275654155 2890317504109965413481233)
            ·
              refine ⟨2167738128082474060110925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2890317504109965413481233 2167738128082474060110925)
              ·
                refine ⟨812901798030927772541597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2167738128082474060110925 812901798030927772541597)
                ·
                  refine ⟨304838174261597914703099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 812901798030927772541597 304838174261597914703099)
                  ·
                    rfl

theorem cell20_667879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 2, 3, 3].length) (baseStart_667879 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_667879 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_667879 prefixEnd_667879 := by exact prefixLift 667879
  have htrace : WordTrace (prefixWord ++ tailWord_667879) baseStart_667879 baseEnd_667879 := by
    simpa [prefixWord, tailWord_667879, baseEnd_667879] using wordTrace_append hprefix tailTrace_667879
  have hstable : (prefixWord ++ tailWord_667879).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_667879).length < 2 ^ (prefixWord ++ tailWord_667879).sum := by decide
  have hdescent : baseEnd_667879 < baseStart_667879 := by decide
  rcases family_descends (prefixWord ++ tailWord_667879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_667989 : List Nat := [1, 3, 2, 2, 5, 1, 2, 1, 3]
def baseStart_667989 : Nat := 118140960795 + 667989 * 2 ^ 59
def prefixEnd_667989 : Nat := 4983230072969 + 3 ^ 40 * 667989 * 2
def baseEnd_667989 : Nat := 304888381258926421035983

theorem tailTrace_667989 : CollatzResearch.WordTrace tailWord_667989 prefixEnd_667989 304888381258926421035983 := by
  unfold tailWord_667989
  simp only [CollatzResearch.WordTrace]
  refine ⟨24363560376997411283663021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16242373584664940855775347 24363560376997411283663021)
  ·
    refine ⟨9136335141374029231373633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24363560376997411283663021 9136335141374029231373633)
    ·
      refine ⟨6852251356030521923530225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9136335141374029231373633 6852251356030521923530225)
      ·
        refine ⟨5139188517022891442647669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6852251356030521923530225 5139188517022891442647669)
        ·
          refine ⟨481798923470896072748219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 5139188517022891442647669 481798923470896072748219)
          ·
            refine ⟨722698385206344109122329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 481798923470896072748219 722698385206344109122329)
            ·
              refine ⟨542023788904758081841747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 722698385206344109122329 542023788904758081841747)
              ·
                refine ⟨813035683357137122762621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 542023788904758081841747 813035683357137122762621)
                ·
                  refine ⟨304888381258926421035983, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 813035683357137122762621 304888381258926421035983)
                  ·
                    rfl

theorem cell20_667989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 5, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 5, 1, 2, 1, 3].length) (baseStart_667989 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_667989 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_667989 prefixEnd_667989 := by exact prefixLift 667989
  have htrace : WordTrace (prefixWord ++ tailWord_667989) baseStart_667989 baseEnd_667989 := by
    simpa [prefixWord, tailWord_667989, baseEnd_667989] using wordTrace_append hprefix tailTrace_667989
  have hstable : (prefixWord ++ tailWord_667989).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_667989).length < 2 ^ (prefixWord ++ tailWord_667989).sum := by decide
  have hdescent : baseEnd_667989 < baseStart_667989 := by decide
  rcases family_descends (prefixWord ++ tailWord_667989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_668072 : List Nat := [2, 1, 6, 1, 1, 2, 2, 3, 2]
def baseStart_668072 : Nat := 118140960795 + 668072 * 2 ^ 59
def prefixEnd_668072 : Nat := 4983230072969 + 3 ^ 40 * 668072 * 2
def baseEnd_668072 : Nat := 304926264720547021268977

theorem tailTrace_668072 : CollatzResearch.WordTrace tailWord_668072 prefixEnd_668072 304926264720547021268977 := by
  unfold tailWord_668072
  simp only [CollatzResearch.WordTrace]
  refine ⟨12183293817848358229467235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16244391757131144305956313 12183293817848358229467235)
  ·
    refine ⟨18274940726772537344200853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12183293817848358229467235 18274940726772537344200853)
    ·
      refine ⟨856637846567462688009415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 18274940726772537344200853 856637846567462688009415)
      ·
        refine ⟨1284956769851194032014123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 856637846567462688009415 1284956769851194032014123)
        ·
          refine ⟨1927435154776791048021185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1284956769851194032014123 1927435154776791048021185)
          ·
            refine ⟨1445576366082593286015889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1927435154776791048021185 1445576366082593286015889)
            ·
              refine ⟨1084182274561944964511917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1445576366082593286015889 1084182274561944964511917)
              ·
                refine ⟨406568352960729361691969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1084182274561944964511917 406568352960729361691969)
                ·
                  refine ⟨304926264720547021268977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 406568352960729361691969 304926264720547021268977)
                  ·
                    rfl

theorem cell20_668072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 2, 2, 3, 2].length) (baseStart_668072 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_668072 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_668072 prefixEnd_668072 := by exact prefixLift 668072
  have htrace : WordTrace (prefixWord ++ tailWord_668072) baseStart_668072 baseEnd_668072 := by
    simpa [prefixWord, tailWord_668072, baseEnd_668072] using wordTrace_append hprefix tailTrace_668072
  have hstable : (prefixWord ++ tailWord_668072).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_668072).length < 2 ^ (prefixWord ++ tailWord_668072).sum := by decide
  have hdescent : baseEnd_668072 < baseStart_668072 := by decide
  rcases family_descends (prefixWord ++ tailWord_668072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_668142 : List Nat := [4, 1, 2, 1, 2, 2, 8]
def baseStart_668142 : Nat := 118140960795 + 668142 * 2 ^ 59
def prefixEnd_668142 : Nat := 4983230072969 + 3 ^ 40 * 668142 * 2
def baseEnd_668142 : Nat := 33884246069770876548373

theorem tailTrace_668142 : CollatzResearch.WordTrace tailWord_668142 prefixEnd_668142 33884246069770876548373 := by
  unfold tailWord_668142
  simp only [CollatzResearch.WordTrace]
  refine ⟨3046142593180389801747835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16246093830295412275988453 3046142593180389801747835)
  ·
    refine ⟨4569213889770584702621753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3046142593180389801747835 4569213889770584702621753)
    ·
      refine ⟨3426910417327938526966315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4569213889770584702621753 3426910417327938526966315)
      ·
        refine ⟨5140365625991907790449473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3426910417327938526966315 5140365625991907790449473)
        ·
          refine ⟨3855274219493930842837105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5140365625991907790449473 3855274219493930842837105)
          ·
            refine ⟨2891455664620448132127829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3855274219493930842837105 2891455664620448132127829)
            ·
              refine ⟨33884246069770876548373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2891455664620448132127829 33884246069770876548373)
              ·
                rfl

theorem cell20_668142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 8].length) (baseStart_668142 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_668142 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_668142 prefixEnd_668142 := by exact prefixLift 668142
  have htrace : WordTrace (prefixWord ++ tailWord_668142) baseStart_668142 baseEnd_668142 := by
    simpa [prefixWord, tailWord_668142, baseEnd_668142] using wordTrace_append hprefix tailTrace_668142
  have hstable : (prefixWord ++ tailWord_668142).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_668142).length < 2 ^ (prefixWord ++ tailWord_668142).sum := by decide
  have hdescent : baseEnd_668142 < baseStart_668142 := by decide
  rcases family_descends (prefixWord ++ tailWord_668142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_668162 : List Nat := [3, 4, 1, 2, 2, 1, 1, 3, 3]
def baseStart_668162 : Nat := 118140960795 + 668162 * 2 ^ 59
def prefixEnd_668162 : Nat := 4983230072969 + 3 ^ 40 * 668162 * 2
def baseEnd_668162 : Nat := 304967343172906708268609

theorem tailTrace_668162 : CollatzResearch.WordTrace tailWord_668162 prefixEnd_668162 304967343172906708268609 := by
  unfold tailWord_668162
  simp only [CollatzResearch.WordTrace]
  refine ⟨6092467551342665457427685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16246580136913774553140493 6092467551342665457427685)
  ·
    refine ⟨1142337665876749773267691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6092467551342665457427685 1142337665876749773267691)
    ·
      refine ⟨1713506498815124659901537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1142337665876749773267691 1713506498815124659901537)
      ·
        refine ⟨1285129874111343494926153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1713506498815124659901537 1285129874111343494926153)
        ·
          refine ⟨963847405583507621194615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1285129874111343494926153 963847405583507621194615)
          ·
            refine ⟨1445771108375261431791923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 963847405583507621194615 1445771108375261431791923)
            ·
              refine ⟨2168656662562892147687885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1445771108375261431791923 2168656662562892147687885)
              ·
                refine ⟨813246248461084555382957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2168656662562892147687885 813246248461084555382957)
                ·
                  refine ⟨304967343172906708268609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 813246248461084555382957 304967343172906708268609)
                  ·
                    rfl

theorem cell20_668162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 1, 1, 3, 3].length) (baseStart_668162 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_668162 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_668162 prefixEnd_668162 := by exact prefixLift 668162
  have htrace : WordTrace (prefixWord ++ tailWord_668162) baseStart_668162 baseEnd_668162 := by
    simpa [prefixWord, tailWord_668162, baseEnd_668162] using wordTrace_append hprefix tailTrace_668162
  have hstable : (prefixWord ++ tailWord_668162).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_668162).length < 2 ^ (prefixWord ++ tailWord_668162).sum := by decide
  have hdescent : baseEnd_668162 < baseStart_668162 := by decide
  rcases family_descends (prefixWord ++ tailWord_668162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_668214 : List Nat := [5, 1, 2, 1, 2, 3, 1, 5]
def baseStart_668214 : Nat := 118140960795 + 668214 * 2 ^ 59
def prefixEnd_668214 : Nat := 4983230072969 + 3 ^ 40 * 668214 * 2
def baseEnd_668214 : Nat := 101663692463275212845021

theorem tailTrace_668214 : CollatzResearch.WordTrace tailWord_668214 prefixEnd_668214 101663692463275212845021 := by
  unfold tailWord_668214
  simp only [CollatzResearch.WordTrace]
  refine ⟨1523235425073892169412731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 16247844534121516473735797 1523235425073892169412731)
  ·
    refine ⟨2284853137610838254119097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1523235425073892169412731 2284853137610838254119097)
    ·
      refine ⟨1713639853208128690589323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2284853137610838254119097 1713639853208128690589323)
      ·
        refine ⟨2570459779812193035883985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1713639853208128690589323 2570459779812193035883985)
        ·
          refine ⟨1927844834859144776912989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2570459779812193035883985 1927844834859144776912989)
          ·
            refine ⟨722941813072179291342371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1927844834859144776912989 722941813072179291342371)
            ·
              refine ⟨1084412719608268937013557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 722941813072179291342371 1084412719608268937013557)
              ·
                refine ⟨101663692463275212845021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1084412719608268937013557 101663692463275212845021)
                ·
                  rfl

theorem cell20_668214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 3, 1, 5].length) (baseStart_668214 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_668214 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_668214 prefixEnd_668214 := by exact prefixLift 668214
  have htrace : WordTrace (prefixWord ++ tailWord_668214) baseStart_668214 baseEnd_668214 := by
    simpa [prefixWord, tailWord_668214, baseEnd_668214] using wordTrace_append hprefix tailTrace_668214
  have hstable : (prefixWord ++ tailWord_668214).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_668214).length < 2 ^ (prefixWord ++ tailWord_668214).sum := by decide
  have hdescent : baseEnd_668214 < baseStart_668214 := by decide
  rcases family_descends (prefixWord ++ tailWord_668214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_668218 : List Nat := [3, 1, 1, 1, 3, 3, 3, 5]
def baseStart_668218 : Nat := 118140960795 + 668218 * 2 ^ 59
def prefixEnd_668218 : Nat := 4983230072969 + 3 ^ 40 * 668218 * 2
def baseEnd_668218 : Nat := 101664301032939800800571

theorem tailTrace_668218 : CollatzResearch.WordTrace tailWord_668218 prefixEnd_668218 101664301032939800800571 := by
  unfold tailWord_668218
  simp only [CollatzResearch.WordTrace]
  refine ⟨6092978173291945848437327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16247941795445188929166205 6092978173291945848437327)
  ·
    refine ⟨9139467259937918772655991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6092978173291945848437327 9139467259937918772655991)
    ·
      refine ⟨13709200889906878158983987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9139467259937918772655991 13709200889906878158983987)
      ·
        refine ⟨20563801334860317238475981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13709200889906878158983987 20563801334860317238475981)
        ·
          refine ⟨7711425500572618964428493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20563801334860317238475981 7711425500572618964428493)
          ·
            refine ⟨2891784562714732111660685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7711425500572618964428493 2891784562714732111660685)
            ·
              refine ⟨1084419211018024541872757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2891784562714732111660685 1084419211018024541872757)
              ·
                refine ⟨101664301032939800800571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1084419211018024541872757 101664301032939800800571)
                ·
                  rfl

theorem cell20_668218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 3, 5].length) (baseStart_668218 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_668218 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_668218 prefixEnd_668218 := by exact prefixLift 668218
  have htrace : WordTrace (prefixWord ++ tailWord_668218) baseStart_668218 baseEnd_668218 := by
    simpa [prefixWord, tailWord_668218, baseEnd_668218] using wordTrace_append hprefix tailTrace_668218
  have hstable : (prefixWord ++ tailWord_668218).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_668218).length < 2 ^ (prefixWord ++ tailWord_668218).sum := by decide
  have hdescent : baseEnd_668218 < baseStart_668218 := by decide
  rcases family_descends (prefixWord ++ tailWord_668218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_668239 : List Nat := [1, 1, 2, 1, 1, 2, 4, 8]
def baseStart_668239 : Nat := 118140960795 + 668239 * 2 ^ 59
def prefixEnd_668239 : Nat := 4983230072969 + 3 ^ 40 * 668239 * 2
def baseEnd_668239 : Nat := 101667496023678887567209

theorem tailTrace_668239 : CollatzResearch.WordTrace tailWord_668239 prefixEnd_668239 101667496023678887567209 := by
  unfold tailWord_668239
  simp only [CollatzResearch.WordTrace]
  refine ⟨24372678626091703980263771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16248452417394469320175847 24372678626091703980263771)
  ·
    refine ⟨36559017939137555970395657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24372678626091703980263771 36559017939137555970395657)
    ·
      refine ⟨27419263454353166977796743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36559017939137555970395657 27419263454353166977796743)
      ·
        refine ⟨41128895181529750466695115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27419263454353166977796743 41128895181529750466695115)
        ·
          refine ⟨61693342772294625700042673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41128895181529750466695115 61693342772294625700042673)
          ·
            refine ⟨46270007079220969275032005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61693342772294625700042673 46270007079220969275032005)
            ·
              refine ⟨8675626327353931739068501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 46270007079220969275032005 8675626327353931739068501)
              ·
                refine ⟨101667496023678887567209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8675626327353931739068501 101667496023678887567209)
                ·
                  rfl

theorem cell20_668239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 4, 8].length) (baseStart_668239 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_668239 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_668239 prefixEnd_668239 := by exact prefixLift 668239
  have htrace : WordTrace (prefixWord ++ tailWord_668239) baseStart_668239 baseEnd_668239 := by
    simpa [prefixWord, tailWord_668239, baseEnd_668239] using wordTrace_append hprefix tailTrace_668239
  have hstable : (prefixWord ++ tailWord_668239).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_668239).length < 2 ^ (prefixWord ++ tailWord_668239).sum := by decide
  have hdescent : baseEnd_668239 < baseStart_668239 := by decide
  rcases family_descends (prefixWord ++ tailWord_668239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_668266 : List Nat := [3, 1, 3, 2, 1, 1, 1, 6, 2]
def baseStart_668266 : Nat := 118140960795 + 668266 * 2 ^ 59
def prefixEnd_668266 : Nat := 4983230072969 + 3 ^ 40 * 668266 * 2
def baseEnd_668266 : Nat := 305014811606744568801517

theorem tailTrace_668266 : CollatzResearch.WordTrace tailWord_668266 prefixEnd_668266 305014811606744568801517 := by
  unfold tailWord_668266
  simp only [CollatzResearch.WordTrace]
  refine ⟨6093415849248471897874163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16249108931329258394331101 6093415849248471897874163)
  ·
    refine ⟨9140123773872707846811245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6093415849248471897874163 9140123773872707846811245)
    ·
      refine ⟨3427546415202265442554217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9140123773872707846811245 3427546415202265442554217)
      ·
        refine ⟨2570659811401699081915663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3427546415202265442554217 2570659811401699081915663)
        ·
          refine ⟨3855989717102548622873495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2570659811401699081915663 3855989717102548622873495)
          ·
            refine ⟨5783984575653822934310243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3855989717102548622873495 5783984575653822934310243)
            ·
              refine ⟨8675976863480734401465365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5783984575653822934310243 8675976863480734401465365)
              ·
                refine ⟨406686415475659425068689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 8675976863480734401465365 406686415475659425068689)
                ·
                  refine ⟨305014811606744568801517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 406686415475659425068689 305014811606744568801517)
                  ·
                    rfl

theorem cell20_668266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 1, 6, 2].length) (baseStart_668266 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_668266 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_668266 prefixEnd_668266 := by exact prefixLift 668266
  have htrace : WordTrace (prefixWord ++ tailWord_668266) baseStart_668266 baseEnd_668266 := by
    simpa [prefixWord, tailWord_668266, baseEnd_668266] using wordTrace_append hprefix tailTrace_668266
  have hstable : (prefixWord ++ tailWord_668266).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_668266).length < 2 ^ (prefixWord ++ tailWord_668266).sum := by decide
  have hdescent : baseEnd_668266 < baseStart_668266 := by decide
  rcases family_descends (prefixWord ++ tailWord_668266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_668318 : List Nat := [4, 3, 1, 1, 1, 1, 1, 3, 5]
def baseStart_668318 : Nat := 118140960795 + 668318 * 2 ^ 59
def prefixEnd_668318 : Nat := 4983230072969 + 3 ^ 40 * 668318 * 2
def baseEnd_668318 : Nat := 305038545823663499067971

theorem tailTrace_668318 : CollatzResearch.WordTrace tailWord_668318 prefixEnd_668318 305038545823663499067971 := by
  unfold tailWord_668318
  simp only [CollatzResearch.WordTrace]
  refine ⟨3046944999100687559048701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16250373328537000314926405 3046944999100687559048701)
  ·
    refine ⟨1142604374662757834643263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3046944999100687559048701 1142604374662757834643263)
    ·
      refine ⟨1713906561994136751964895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1142604374662757834643263 1713906561994136751964895)
      ·
        refine ⟨2570859842991205127947343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1713906561994136751964895 2570859842991205127947343)
        ·
          refine ⟨3856289764486807691921015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2570859842991205127947343 3856289764486807691921015)
          ·
            refine ⟨5784434646730211537881523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3856289764486807691921015 5784434646730211537881523)
            ·
              refine ⟨8676651970095317306822285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5784434646730211537881523 8676651970095317306822285)
              ·
                refine ⟨3253744488785743990058357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8676651970095317306822285 3253744488785743990058357)
                ·
                  refine ⟨305038545823663499067971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3253744488785743990058357 305038545823663499067971)
                  ·
                    rfl

theorem cell20_668318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 1, 3, 5].length) (baseStart_668318 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_668318 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_668318 prefixEnd_668318 := by exact prefixLift 668318
  have htrace : WordTrace (prefixWord ++ tailWord_668318) baseStart_668318 baseEnd_668318 := by
    simpa [prefixWord, tailWord_668318, baseEnd_668318] using wordTrace_append hprefix tailTrace_668318
  have hstable : (prefixWord ++ tailWord_668318).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_668318).length < 2 ^ (prefixWord ++ tailWord_668318).sum := by decide
  have hdescent : baseEnd_668318 < baseStart_668318 := by decide
  rcases family_descends (prefixWord ++ tailWord_668318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_668321 : List Nat := [1, 2, 3, 3, 4, 1, 1, 1, 4]
def baseStart_668321 : Nat := 118140960795 + 668321 * 2 ^ 59
def prefixEnd_668321 : Nat := 4983230072969 + 3 ^ 40 * 668321 * 2
def baseEnd_668321 : Nat := 305039915105408821967959

theorem tailTrace_668321 : CollatzResearch.WordTrace tailWord_668321 prefixEnd_668321 305039915105408821967959 := by
  unfold tailWord_668321
  simp only [CollatzResearch.WordTrace]
  refine ⟨24375669411794631984748817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16250446274529754656499211 24375669411794631984748817)
  ·
    refine ⟨18281752058845973988561613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24375669411794631984748817 18281752058845973988561613)
    ·
      refine ⟨6855657022067240245710605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18281752058845973988561613 6855657022067240245710605)
      ·
        refine ⟨2570871383275215092141477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6855657022067240245710605 2570871383275215092141477)
        ·
          refine ⟨482038384364102829776527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2570871383275215092141477 482038384364102829776527)
          ·
            refine ⟨723057576546154244664791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 482038384364102829776527 723057576546154244664791)
            ·
              refine ⟨1084586364819231366997187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 723057576546154244664791 1084586364819231366997187)
              ·
                refine ⟨1626879547228847050495781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1084586364819231366997187 1626879547228847050495781)
                ·
                  refine ⟨305039915105408821967959, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1626879547228847050495781 305039915105408821967959)
                  ·
                    rfl

theorem cell20_668321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 4, 1, 1, 1, 4].length) (baseStart_668321 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_668321 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_668321 prefixEnd_668321 := by exact prefixLift 668321
  have htrace : WordTrace (prefixWord ++ tailWord_668321) baseStart_668321 baseEnd_668321 := by
    simpa [prefixWord, tailWord_668321, baseEnd_668321] using wordTrace_append hprefix tailTrace_668321
  have hstable : (prefixWord ++ tailWord_668321).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_668321).length < 2 ^ (prefixWord ++ tailWord_668321).sum := by decide
  have hdescent : baseEnd_668321 < baseStart_668321 := by decide
  rcases family_descends (prefixWord ++ tailWord_668321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_668335 : List Nat := [1, 1, 2, 1, 2, 7, 2, 1, 3]
def baseStart_668335 : Nat := 118140960795 + 668335 * 2 ^ 59
def prefixEnd_668335 : Nat := 4983230072969 + 3 ^ 40 * 668335 * 2
def baseEnd_668335 : Nat := 305046305086886995501235

theorem tailTrace_668335 : CollatzResearch.WordTrace tailWord_668335 prefixEnd_668335 305046305086886995501235 := by
  unfold tailWord_668335
  simp only [CollatzResearch.WordTrace]
  refine ⟨24376180033743912375758459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16250786689162608250505639 24376180033743912375758459)
  ·
    refine ⟨36564270050615868563637689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24376180033743912375758459 36564270050615868563637689)
    ·
      refine ⟨27423202537961901422728267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36564270050615868563637689 27423202537961901422728267)
      ·
        refine ⟨41134803806942852134092401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27423202537961901422728267 41134803806942852134092401)
        ·
          refine ⟨30851102855207139100569301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41134803806942852134092401 30851102855207139100569301)
          ·
            refine ⟨723072723168917322669593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 30851102855207139100569301 723072723168917322669593)
            ·
              refine ⟨542304542376687992002195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 723072723168917322669593 542304542376687992002195)
              ·
                refine ⟨813456813565031988003293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 542304542376687992002195 813456813565031988003293)
                ·
                  refine ⟨305046305086886995501235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 813456813565031988003293 305046305086886995501235)
                  ·
                    rfl

theorem cell20_668335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 7, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 7, 2, 1, 3].length) (baseStart_668335 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_668335 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_668335 prefixEnd_668335 := by exact prefixLift 668335
  have htrace : WordTrace (prefixWord ++ tailWord_668335) baseStart_668335 baseEnd_668335 := by
    simpa [prefixWord, tailWord_668335, baseEnd_668335] using wordTrace_append hprefix tailTrace_668335
  have hstable : (prefixWord ++ tailWord_668335).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_668335).length < 2 ^ (prefixWord ++ tailWord_668335).sum := by decide
  have hdescent : baseEnd_668335 < baseStart_668335 := by decide
  rcases family_descends (prefixWord ++ tailWord_668335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_668346 : List Nat := [3, 1, 1, 1, 2, 3, 2, 1, 6]
def baseStart_668346 : Nat := 118140960795 + 668346 * 2 ^ 59
def prefixEnd_668346 : Nat := 4983230072969 + 3 ^ 40 * 668346 * 2
def baseEnd_668346 : Nat := 305051325786619846134523

theorem tailTrace_668346 : CollatzResearch.WordTrace tailWord_668346 prefixEnd_668346 305051325786619846134523 := by
  unfold tailWord_668346
  simp only [CollatzResearch.WordTrace]
  refine ⟨6094145309176015313602223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16251054157802707502939261 6094145309176015313602223)
  ·
    refine ⟨9141217963764022970403335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6094145309176015313602223 9141217963764022970403335)
    ·
      refine ⟨13711826945646034455605003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9141217963764022970403335 13711826945646034455605003)
      ·
        refine ⟨20567740418469051683407505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13711826945646034455605003 20567740418469051683407505)
        ·
          refine ⟨15425805313851788762555629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20567740418469051683407505 15425805313851788762555629)
          ·
            refine ⟨5784676992694420785958361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15425805313851788762555629 5784676992694420785958361)
            ·
              refine ⟨4338507744520815589468771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5784676992694420785958361 4338507744520815589468771)
              ·
                refine ⟨6507761616781223384203157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4338507744520815589468771 6507761616781223384203157)
                ·
                  refine ⟨305051325786619846134523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6507761616781223384203157 305051325786619846134523)
                  ·
                    rfl

theorem cell20_668346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 2, 1, 6].length) (baseStart_668346 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_668346 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_668346 prefixEnd_668346 := by exact prefixLift 668346
  have htrace : WordTrace (prefixWord ++ tailWord_668346) baseStart_668346 baseEnd_668346 := by
    simpa [prefixWord, tailWord_668346, baseEnd_668346] using wordTrace_append hprefix tailTrace_668346
  have hstable : (prefixWord ++ tailWord_668346).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_668346).length < 2 ^ (prefixWord ++ tailWord_668346).sum := by decide
  have hdescent : baseEnd_668346 < baseStart_668346 := by decide
  rcases family_descends (prefixWord ++ tailWord_668346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_668370 : List Nat := [3, 2, 2, 2, 3, 8]
def baseStart_668370 : Nat := 118140960795 + 668370 * 2 ^ 59
def prefixEnd_668370 : Nat := 4983230072969 + 3 ^ 40 * 668370 * 2
def baseEnd_668370 : Nat := 11298602964466015901275

theorem tailTrace_668370 : CollatzResearch.WordTrace tailWord_668370 prefixEnd_668370 11298602964466015901275 := by
  unfold tailWord_668370
  simp only [CollatzResearch.WordTrace]
  refine ⟨6094364147154278338320641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16251637725744742235521709 6094364147154278338320641)
  ·
    refine ⟨4570773110365708753740481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6094364147154278338320641 4570773110365708753740481)
    ·
      refine ⟨3428079832774281565305361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4570773110365708753740481 3428079832774281565305361)
      ·
        refine ⟨2571059874580711173979021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3428079832774281565305361 2571059874580711173979021)
        ·
          refine ⟨964147452967766690242133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2571059874580711173979021 964147452967766690242133)
          ·
            refine ⟨11298602964466015901275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 964147452967766690242133 11298602964466015901275)
            ·
              rfl

theorem cell20_668370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 8].length) (baseStart_668370 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_668370 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_668370 prefixEnd_668370 := by exact prefixLift 668370
  have htrace : WordTrace (prefixWord ++ tailWord_668370) baseStart_668370 baseEnd_668370 := by
    simpa [prefixWord, tailWord_668370, baseEnd_668370] using wordTrace_append hprefix tailTrace_668370
  have hstable : (prefixWord ++ tailWord_668370).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_668370).length < 2 ^ (prefixWord ++ tailWord_668370).sum := by decide
  have hdescent : baseEnd_668370 < baseStart_668370 := by decide
  rcases family_descends (prefixWord ++ tailWord_668370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_668384 : List Nat := [2, 1, 1, 3, 1, 2, 1, 5, 4]
def baseStart_668384 : Nat := 118140960795 + 668384 * 2 ^ 59
def prefixEnd_668384 : Nat := 4983230072969 + 3 ^ 40 * 668384 * 2
def baseEnd_668384 : Nat := 305068670022060602867701

theorem tailTrace_668384 : CollatzResearch.WordTrace tailWord_668384 prefixEnd_668384 305068670022060602867701 := by
  unfold tailWord_668384
  simp only [CollatzResearch.WordTrace]
  refine ⟨12188983605283196872146103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16251978140377595829528137 12188983605283196872146103)
  ·
    refine ⟨18283475407924795308219155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12188983605283196872146103 18283475407924795308219155)
    ·
      refine ⟨27425213111887192962328733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18283475407924795308219155 27425213111887192962328733)
      ·
        refine ⟨10284454916957697360873275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27425213111887192962328733 10284454916957697360873275)
        ·
          refine ⟨15426682375436546041309913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10284454916957697360873275 15426682375436546041309913)
          ·
            refine ⟨11570011781577409530982435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15426682375436546041309913 11570011781577409530982435)
            ·
              refine ⟨17355017672366114296473653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11570011781577409530982435 17355017672366114296473653)
              ·
                refine ⟨1627032906784323215294405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 17355017672366114296473653 1627032906784323215294405)
                ·
                  refine ⟨305068670022060602867701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1627032906784323215294405 305068670022060602867701)
                  ·
                    rfl

theorem cell20_668384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 5, 4].length) (baseStart_668384 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_668384 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_668384 prefixEnd_668384 := by exact prefixLift 668384
  have htrace : WordTrace (prefixWord ++ tailWord_668384) baseStart_668384 baseEnd_668384 := by
    simpa [prefixWord, tailWord_668384, baseEnd_668384] using wordTrace_append hprefix tailTrace_668384
  have hstable : (prefixWord ++ tailWord_668384).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_668384).length < 2 ^ (prefixWord ++ tailWord_668384).sum := by decide
  have hdescent : baseEnd_668384 < baseStart_668384 := by decide
  rcases family_descends (prefixWord ++ tailWord_668384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_668387 : List Nat := [1, 1, 1, 7, 1, 3, 1, 5]
def baseStart_668387 : Nat := 118140960795 + 668387 * 2 ^ 59
def prefixEnd_668387 : Nat := 4983230072969 + 3 ^ 40 * 668387 * 2
def baseEnd_668387 : Nat := 101690013101268641922563

theorem tailTrace_668387 : CollatzResearch.WordTrace tailWord_668387 prefixEnd_668387 101690013101268641922563 := by
  unfold tailWord_668387
  simp only [CollatzResearch.WordTrace]
  refine ⟨24378076629555525256651415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16252051086370350171100943 24378076629555525256651415)
  ·
    refine ⟨36567114944333287884977123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24378076629555525256651415 36567114944333287884977123)
    ·
      refine ⟨54850672416499931827465685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36567114944333287884977123 54850672416499931827465685)
      ·
        refine ⟨1285562634761717152206227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 54850672416499931827465685 1285562634761717152206227)
        ·
          refine ⟨1928343952142575728309341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1285562634761717152206227 1928343952142575728309341)
          ·
            refine ⟨723128982053465898116003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1928343952142575728309341 723128982053465898116003)
            ·
              refine ⟨1084693473080198847174005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 723128982053465898116003 1084693473080198847174005)
              ·
                refine ⟨101690013101268641922563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1084693473080198847174005 101690013101268641922563)
                ·
                  rfl

theorem cell20_668387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 3, 1, 5].length) (baseStart_668387 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_668387 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_668387 prefixEnd_668387 := by exact prefixLift 668387
  have htrace : WordTrace (prefixWord ++ tailWord_668387) baseStart_668387 baseEnd_668387 := by
    simpa [prefixWord, tailWord_668387, baseEnd_668387] using wordTrace_append hprefix tailTrace_668387
  have hstable : (prefixWord ++ tailWord_668387).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_668387).length < 2 ^ (prefixWord ++ tailWord_668387).sum := by decide
  have hdescent : baseEnd_668387 < baseStart_668387 := by decide
  rcases family_descends (prefixWord ++ tailWord_668387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_668408 : List Nat := [2, 1, 2, 1, 1, 2, 7, 4]
def baseStart_668408 : Nat := 118140960795 + 668408 * 2 ^ 59
def prefixEnd_668408 : Nat := 4983230072969 + 3 ^ 40 * 668408 * 2
def baseEnd_668408 : Nat := 101693208092007728689201

theorem tailTrace_668408 : CollatzResearch.WordTrace tailWord_668408 prefixEnd_668408 101693208092007728689201 := by
  unfold tailWord_668408
  simp only [CollatzResearch.WordTrace]
  refine ⟨12189421281239722921582939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16252561708319630562110585 12189421281239722921582939)
  ·
    refine ⟨18284131921859584382374409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12189421281239722921582939 18284131921859584382374409)
    ·
      refine ⟨13713098941394688286780807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18284131921859584382374409 13713098941394688286780807)
      ·
        refine ⟨20569648412092032430171211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13713098941394688286780807 20569648412092032430171211)
        ·
          refine ⟨30854472618138048645256817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20569648412092032430171211 30854472618138048645256817)
          ·
            refine ⟨23140854463603536483942613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30854472618138048645256817 23140854463603536483942613)
            ·
              refine ⟨542363776490707886342405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 23140854463603536483942613 542363776490707886342405)
              ·
                refine ⟨101693208092007728689201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 542363776490707886342405 101693208092007728689201)
                ·
                  rfl

theorem cell20_668408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 7, 4].length) (baseStart_668408 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_668408 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_668408 prefixEnd_668408 := by exact prefixLift 668408
  have htrace : WordTrace (prefixWord ++ tailWord_668408) baseStart_668408 baseEnd_668408 := by
    simpa [prefixWord, tailWord_668408, baseEnd_668408] using wordTrace_append hprefix tailTrace_668408
  have hstable : (prefixWord ++ tailWord_668408).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_668408).length < 2 ^ (prefixWord ++ tailWord_668408).sum := by decide
  have hdescent : baseEnd_668408 < baseStart_668408 := by decide
  rcases family_descends (prefixWord ++ tailWord_668408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_668460 : List Nat := [2, 2, 1, 1, 1, 4, 1, 4, 4]
def baseStart_668460 : Nat := 118140960795 + 668460 * 2 ^ 59
def prefixEnd_668460 : Nat := 4983230072969 + 3 ^ 40 * 668460 * 2
def baseEnd_668460 : Nat := 305103358492942116334057

theorem tailTrace_668460 : CollatzResearch.WordTrace tailWord_668460 prefixEnd_668460 305103358492942116334057 := by
  unfold tailWord_668460
  simp only [CollatzResearch.WordTrace]
  refine ⟨12190369579145529362029417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16253826105527372482705889 12190369579145529362029417)
  ·
    refine ⟨9142777184359147021522063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12190369579145529362029417 9142777184359147021522063)
    ·
      refine ⟨13714165776538720532283095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9142777184359147021522063 13714165776538720532283095)
      ·
        refine ⟨20571248664808080798424643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13714165776538720532283095 20571248664808080798424643)
        ·
          refine ⟨30856872997212121197636965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20571248664808080798424643 30856872997212121197636965)
          ·
            refine ⟨5785663686977272724556931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 30856872997212121197636965 5785663686977272724556931)
            ·
              refine ⟨8678495530465909086835397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5785663686977272724556931 8678495530465909086835397)
              ·
                refine ⟨1627217911962357953781637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8678495530465909086835397 1627217911962357953781637)
                ·
                  refine ⟨305103358492942116334057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1627217911962357953781637 305103358492942116334057)
                  ·
                    rfl

theorem cell20_668460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 4].length) (baseStart_668460 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_668460 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_668460 prefixEnd_668460 := by exact prefixLift 668460
  have htrace : WordTrace (prefixWord ++ tailWord_668460) baseStart_668460 baseEnd_668460 := by
    simpa [prefixWord, tailWord_668460, baseEnd_668460] using wordTrace_append hprefix tailTrace_668460
  have hstable : (prefixWord ++ tailWord_668460).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_668460).length < 2 ^ (prefixWord ++ tailWord_668460).sum := by decide
  have hdescent : baseEnd_668460 < baseStart_668460 := by decide
  rcases family_descends (prefixWord ++ tailWord_668460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_668505 : List Nat := [1, 2, 1, 2, 2, 4, 1, 7]
def baseStart_668505 : Nat := 118140960795 + 668505 * 2 ^ 59
def prefixEnd_668505 : Nat := 4983230072969 + 3 ^ 40 * 668505 * 2
def baseEnd_668505 : Nat := 101707965906373986611291

theorem tailTrace_668505 : CollatzResearch.WordTrace tailWord_668505 prefixEnd_668505 101707965906373986611291 := by
  unfold tailWord_668505
  simp only [CollatzResearch.WordTrace]
  refine ⟨24382380443128031409446969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16254920295418687606297979 24382380443128031409446969)
  ·
    refine ⟨18286785332346023557085227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24382380443128031409446969 18286785332346023557085227)
    ·
      refine ⟨27430177998519035335627841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18286785332346023557085227 27430177998519035335627841)
      ·
        refine ⟨20572633498889276501720881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27430177998519035335627841 20572633498889276501720881)
        ·
          refine ⟨15429475124166957376290661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20572633498889276501720881 15429475124166957376290661)
          ·
            refine ⟨2893026585781304508054499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15429475124166957376290661 2893026585781304508054499)
            ·
              refine ⟨4339539878671956762081749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2893026585781304508054499 4339539878671956762081749)
              ·
                refine ⟨101707965906373986611291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4339539878671956762081749 101707965906373986611291)
                ·
                  rfl

theorem cell20_668505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 1, 7].length) (baseStart_668505 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_668505 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_668505 prefixEnd_668505 := by exact prefixLift 668505
  have htrace : WordTrace (prefixWord ++ tailWord_668505) baseStart_668505 baseEnd_668505 := by
    simpa [prefixWord, tailWord_668505, baseEnd_668505] using wordTrace_append hprefix tailTrace_668505
  have hstable : (prefixWord ++ tailWord_668505).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_668505).length < 2 ^ (prefixWord ++ tailWord_668505).sum := by decide
  have hdescent : baseEnd_668505 < baseStart_668505 := by decide
  rcases family_descends (prefixWord ++ tailWord_668505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_668542 : List Nat := [4, 2, 3, 1, 2, 1, 2, 2, 3]
def baseStart_668542 : Nat := 118140960795 + 668542 * 2 ^ 59
def prefixEnd_668542 : Nat := 4983230072969 + 3 ^ 40 * 668542 * 2
def baseEnd_668542 : Nat := 305140785527314275600389

theorem tailTrace_668542 : CollatzResearch.WordTrace tailWord_668542 prefixEnd_668542 305140785527314275600389 := by
  unfold tailWord_668542
  simp only [CollatzResearch.WordTrace]
  refine ⟨3047966242999248341067985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16255819962662657819029253 3047966242999248341067985)
  ·
    refine ⟨2285974682249436255800989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3047966242999248341067985 2285974682249436255800989)
    ·
      refine ⟨857240505843538595925371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2285974682249436255800989 857240505843538595925371)
      ·
        refine ⟨1285860758765307893888057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 857240505843538595925371 1285860758765307893888057)
        ·
          refine ⟨964395569073980920416043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1285860758765307893888057 964395569073980920416043)
          ·
            refine ⟨1446593353610971380624065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 964395569073980920416043 1446593353610971380624065)
            ·
              refine ⟨1084945015208228535468049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1446593353610971380624065 1084945015208228535468049)
              ·
                refine ⟨813708761406171401601037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1084945015208228535468049 813708761406171401601037)
                ·
                  refine ⟨305140785527314275600389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 813708761406171401601037 305140785527314275600389)
                  ·
                    rfl

theorem cell20_668542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 1, 2, 2, 3].length) (baseStart_668542 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_668542 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_668542 prefixEnd_668542 := by exact prefixLift 668542
  have htrace : WordTrace (prefixWord ++ tailWord_668542) baseStart_668542 baseEnd_668542 := by
    simpa [prefixWord, tailWord_668542, baseEnd_668542] using wordTrace_append hprefix tailTrace_668542
  have hstable : (prefixWord ++ tailWord_668542).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_668542).length < 2 ^ (prefixWord ++ tailWord_668542).sum := by decide
  have hdescent : baseEnd_668542 < baseStart_668542 := by decide
  rcases family_descends (prefixWord ++ tailWord_668542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_668549 : List Nat := [1, 3, 1, 1, 3, 5, 2, 2, 2]
def baseStart_668549 : Nat := 118140960795 + 668549 * 2 ^ 59
def prefixEnd_668549 : Nat := 4983230072969 + 3 ^ 40 * 668549 * 2
def baseEnd_668549 : Nat := 305143980518053362367027

theorem tailTrace_668549 : CollatzResearch.WordTrace tailWord_668549 prefixEnd_668549 305143980518053362367027 := by
  unfold tailWord_668549
  simp only [CollatzResearch.WordTrace]
  refine ⟨24383985254968626924048701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16255990169979084616032467 24383985254968626924048701)
  ·
    refine ⟨9143994470613235096518263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24383985254968626924048701 9143994470613235096518263)
    ·
      refine ⟨13715991705919852644777395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9143994470613235096518263 13715991705919852644777395)
      ·
        refine ⟨20573987558879778967166093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13715991705919852644777395 20573987558879778967166093)
        ·
          refine ⟨7715245334579917112687285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20573987558879778967166093 7715245334579917112687285)
          ·
            refine ⟨723304250116867229314433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 7715245334579917112687285 723304250116867229314433)
            ·
              refine ⟨542478187587650421985825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 723304250116867229314433 542478187587650421985825)
              ·
                refine ⟨406858640690737816489369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 542478187587650421985825 406858640690737816489369)
                ·
                  refine ⟨305143980518053362367027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 406858640690737816489369 305143980518053362367027)
                  ·
                    rfl

theorem cell20_668549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 5, 2, 2, 2].length) (baseStart_668549 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_668549 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_668549 prefixEnd_668549 := by exact prefixLift 668549
  have htrace : WordTrace (prefixWord ++ tailWord_668549) baseStart_668549 baseEnd_668549 := by
    simpa [prefixWord, tailWord_668549, baseEnd_668549] using wordTrace_append hprefix tailTrace_668549
  have hstable : (prefixWord ++ tailWord_668549).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_668549).length < 2 ^ (prefixWord ++ tailWord_668549).sum := by decide
  have hdescent : baseEnd_668549 < baseStart_668549 := by decide
  rcases family_descends (prefixWord ++ tailWord_668549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_668567 : List Nat := [1, 1, 3, 3, 1, 2, 1, 5, 3]
def baseStart_668567 : Nat := 118140960795 + 668567 * 2 ^ 59
def prefixEnd_668567 : Nat := 4983230072969 + 3 ^ 40 * 668567 * 2
def baseEnd_668567 : Nat := 305152196208525299766953

theorem tailTrace_668567 : CollatzResearch.WordTrace tailWord_668567 prefixEnd_668567 305152196208525299766953 := by
  unfold tailWord_668567
  simp only [CollatzResearch.WordTrace]
  refine ⟨24384641768903415998203955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16256427845935610665469303 24384641768903415998203955)
  ·
    refine ⟨36576962653355123997305933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24384641768903415998203955 36576962653355123997305933)
    ·
      refine ⟨13716360995008171498989725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36576962653355123997305933 13716360995008171498989725)
      ·
        refine ⟨5143635373128064312121147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13716360995008171498989725 5143635373128064312121147)
        ·
          refine ⟨7715453059692096468181721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5143635373128064312121147 7715453059692096468181721)
          ·
            refine ⟨5786589794769072351136291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7715453059692096468181721 5786589794769072351136291)
            ·
              refine ⟨8679884692153608526704437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5786589794769072351136291 8679884692153608526704437)
              ·
                refine ⟨813739189889400799378541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8679884692153608526704437 813739189889400799378541)
                ·
                  refine ⟨305152196208525299766953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 813739189889400799378541 305152196208525299766953)
                  ·
                    rfl

theorem cell20_668567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 1, 5, 3].length) (baseStart_668567 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_668567 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_668567 prefixEnd_668567 := by exact prefixLift 668567
  have htrace : WordTrace (prefixWord ++ tailWord_668567) baseStart_668567 baseEnd_668567 := by
    simpa [prefixWord, tailWord_668567, baseEnd_668567] using wordTrace_append hprefix tailTrace_668567
  have hstable : (prefixWord ++ tailWord_668567).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_668567).length < 2 ^ (prefixWord ++ tailWord_668567).sum := by decide
  have hdescent : baseEnd_668567 < baseStart_668567 := by decide
  rcases family_descends (prefixWord ++ tailWord_668567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_668577 : List Nat := [1, 2, 3, 4, 1, 2, 3, 4]
def baseStart_668577 : Nat := 118140960795 + 668577 * 2 ^ 59
def prefixEnd_668577 : Nat := 4983230072969 + 3 ^ 40 * 668577 * 2
def baseEnd_668577 : Nat := 101718920160336569811193

theorem tailTrace_668577 : CollatzResearch.WordTrace tailWord_668577 prefixEnd_668577 101718920160336569811193 := by
  unfold tailWord_668577
  simp only [CollatzResearch.WordTrace]
  refine ⟨24385006498867187706067985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16256670999244791804045323 24385006498867187706067985)
  ·
    refine ⟨18288754874150390779550989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24385006498867187706067985 18288754874150390779550989)
    ·
      refine ⟨6858283077806396542331621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18288754874150390779550989 6858283077806396542331621)
      ·
        refine ⟨1285928077088699351687179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6858283077806396542331621 1285928077088699351687179)
        ·
          refine ⟨1928892115633049027530769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1285928077088699351687179 1928892115633049027530769)
          ·
            refine ⟨1446669086724786770648077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1928892115633049027530769 1446669086724786770648077)
            ·
              refine ⟨542500907521795038993029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1446669086724786770648077 542500907521795038993029)
              ·
                refine ⟨101718920160336569811193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 542500907521795038993029 101718920160336569811193)
                ·
                  rfl

theorem cell20_668577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 2, 3, 4].length) (baseStart_668577 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_668577 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_668577 prefixEnd_668577 := by exact prefixLift 668577
  have htrace : WordTrace (prefixWord ++ tailWord_668577) baseStart_668577 baseEnd_668577 := by
    simpa [prefixWord, tailWord_668577, baseEnd_668577] using wordTrace_append hprefix tailTrace_668577
  have hstable : (prefixWord ++ tailWord_668577).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_668577).length < 2 ^ (prefixWord ++ tailWord_668577).sum := by decide
  have hdescent : baseEnd_668577 < baseStart_668577 := by decide
  rcases family_descends (prefixWord ++ tailWord_668577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_668588 : List Nat := [2, 2, 1, 1, 1, 1, 2, 3, 7]
def baseStart_668588 : Nat := 118140960795 + 668588 * 2 ^ 59
def prefixEnd_668588 : Nat := 4983230072969 + 3 ^ 40 * 668588 * 2
def baseEnd_668588 : Nat := 305161781180742560066867

theorem tailTrace_668588 : CollatzResearch.WordTrace tailWord_668588 prefixEnd_668588 305161781180742560066867 := by
  unfold tailWord_668588
  simp only [CollatzResearch.WordTrace]
  refine ⟨12192703850913668292359209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16256938467884891056478945 12192703850913668292359209)
  ·
    refine ⟨9144527888185251219269407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12192703850913668292359209 9144527888185251219269407)
    ·
      refine ⟨13716791832277876828904111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9144527888185251219269407 13716791832277876828904111)
      ·
        refine ⟨20575187748416815243356167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13716791832277876828904111 20575187748416815243356167)
        ·
          refine ⟨30862781622625222865034251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20575187748416815243356167 30862781622625222865034251)
          ·
            refine ⟨46294172433937834297551377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30862781622625222865034251 46294172433937834297551377)
            ·
              refine ⟨34720629325453375723163533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46294172433937834297551377 34720629325453375723163533)
              ·
                refine ⟨13020235997045015896186325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34720629325453375723163533 13020235997045015896186325)
                ·
                  refine ⟨305161781180742560066867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13020235997045015896186325 305161781180742560066867)
                  ·
                    rfl

theorem cell20_668588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 7].length) (baseStart_668588 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_668588 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_668588 prefixEnd_668588 := by exact prefixLift 668588
  have htrace : WordTrace (prefixWord ++ tailWord_668588) baseStart_668588 baseEnd_668588 := by
    simpa [prefixWord, tailWord_668588, baseEnd_668588] using wordTrace_append hprefix tailTrace_668588
  have hstable : (prefixWord ++ tailWord_668588).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_668588).length < 2 ^ (prefixWord ++ tailWord_668588).sum := by decide
  have hdescent : baseEnd_668588 < baseStart_668588 := by decide
  rcases family_descends (prefixWord ++ tailWord_668588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_668642 : List Nat := [3, 3, 3, 1, 1, 3, 1, 3, 2]
def baseStart_668642 : Nat := 118140960795 + 668642 * 2 ^ 59
def prefixEnd_668642 : Nat := 4983230072969 + 3 ^ 40 * 668642 * 2
def baseEnd_668642 : Nat := 305186428252158372266647

theorem tailTrace_668642 : CollatzResearch.WordTrace tailWord_668642 prefixEnd_668642 305186428252158372266647 := by
  unfold tailWord_668642
  simp only [CollatzResearch.WordTrace]
  refine ⟨6096844310907925951796045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16258251495754469204789453 6096844310907925951796045)
  ·
    refine ⟨2286316616590472231923517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6096844310907925951796045 2286316616590472231923517)
    ·
      refine ⟨857368731221427086971319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2286316616590472231923517 857368731221427086971319)
      ·
        refine ⟨1286053096832140630456979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 857368731221427086971319 1286053096832140630456979)
        ·
          refine ⟨1929079645248210945685469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1286053096832140630456979 1929079645248210945685469)
          ·
            refine ⟨723404866968079104632051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1929079645248210945685469 723404866968079104632051)
            ·
              refine ⟨1085107300452118656948077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 723404866968079104632051 1085107300452118656948077)
              ·
                refine ⟨406915237669544496355529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1085107300452118656948077 406915237669544496355529)
                ·
                  refine ⟨305186428252158372266647, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 406915237669544496355529 305186428252158372266647)
                  ·
                    rfl

theorem cell20_668642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 3, 1, 3, 2].length) (baseStart_668642 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_668642 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_668642 prefixEnd_668642 := by exact prefixLift 668642
  have htrace : WordTrace (prefixWord ++ tailWord_668642) baseStart_668642 baseEnd_668642 := by
    simpa [prefixWord, tailWord_668642, baseEnd_668642] using wordTrace_append hprefix tailTrace_668642
  have hstable : (prefixWord ++ tailWord_668642).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_668642).length < 2 ^ (prefixWord ++ tailWord_668642).sum := by decide
  have hdescent : baseEnd_668642 < baseStart_668642 := by decide
  rcases family_descends (prefixWord ++ tailWord_668642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_668657 : List Nat := [1, 2, 2, 2, 4, 1, 8]
def baseStart_668657 : Nat := 118140960795 + 668657 * 2 ^ 59
def prefixEnd_668657 : Nat := 4983230072969 + 3 ^ 40 * 668657 * 2
def baseEnd_668657 : Nat := 33910363851209442974065

theorem tailTrace_668657 : CollatzResearch.WordTrace tailWord_668657 prefixEnd_668657 33910363851209442974065 := by
  unfold tailWord_668657
  simp only [CollatzResearch.WordTrace]
  refine ⟨24387924338577361368980225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16258616225718240912653483 24387924338577361368980225)
  ·
    refine ⟨18290943253933021026735169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24387924338577361368980225 18290943253933021026735169)
    ·
      refine ⟨13718207440449765770051377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18290943253933021026735169 13718207440449765770051377)
      ·
        refine ⟨10288655580337324327538533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13718207440449765770051377 10288655580337324327538533)
        ·
          refine ⟨1929122921313248311413475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10288655580337324327538533 1929122921313248311413475)
          ·
            refine ⟨2893684381969872467120213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1929122921313248311413475 2893684381969872467120213)
            ·
              refine ⟨33910363851209442974065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2893684381969872467120213 33910363851209442974065)
              ·
                rfl

theorem cell20_668657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 8].length) (baseStart_668657 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_668657 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_668657 prefixEnd_668657 := by exact prefixLift 668657
  have htrace : WordTrace (prefixWord ++ tailWord_668657) baseStart_668657 baseEnd_668657 := by
    simpa [prefixWord, tailWord_668657, baseEnd_668657] using wordTrace_append hprefix tailTrace_668657
  have hstable : (prefixWord ++ tailWord_668657).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_668657).length < 2 ^ (prefixWord ++ tailWord_668657).sum := by decide
  have hdescent : baseEnd_668657 < baseStart_668657 := by decide
  rcases family_descends (prefixWord ++ tailWord_668657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_668750 : List Nat := [4, 1, 1, 1, 1, 3, 5, 4]
def baseStart_668750 : Nat := 118140960795 + 668750 * 2 ^ 59
def prefixEnd_668750 : Nat := 4983230072969 + 3 ^ 40 * 668750 * 2
def baseEnd_668750 : Nat := 101745240798329998888735

theorem tailTrace_668750 : CollatzResearch.WordTrace tailWord_668750 prefixEnd_668750 101745240798329998888735 := by
  unfold tailWord_668750
  simp only [CollatzResearch.WordTrace]
  refine ⟨3048914540905054781514463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16260877551493625501410469 3048914540905054781514463)
  ·
    refine ⟨4573371811357582172271695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3048914540905054781514463 4573371811357582172271695)
    ·
      refine ⟨6860057717036373258407543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4573371811357582172271695 6860057717036373258407543)
      ·
        refine ⟨10290086575554559887611315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6860057717036373258407543 10290086575554559887611315)
        ·
          refine ⟨15435129863331839831416973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10290086575554559887611315 15435129863331839831416973)
          ·
            refine ⟨5788173698749439936781365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15435129863331839831416973 5788173698749439936781365)
            ·
              refine ⟨542641284257759994073253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5788173698749439936781365 542641284257759994073253)
              ·
                refine ⟨101745240798329998888735, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 542641284257759994073253 101745240798329998888735)
                ·
                  rfl

theorem cell20_668750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 5, 4].length) (baseStart_668750 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_668750 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_668750 prefixEnd_668750 := by exact prefixLift 668750
  have htrace : WordTrace (prefixWord ++ tailWord_668750) baseStart_668750 baseEnd_668750 := by
    simpa [prefixWord, tailWord_668750, baseEnd_668750] using wordTrace_append hprefix tailTrace_668750
  have hstable : (prefixWord ++ tailWord_668750).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_668750).length < 2 ^ (prefixWord ++ tailWord_668750).sum := by decide
  have hdescent : baseEnd_668750 < baseStart_668750 := by decide
  rcases family_descends (prefixWord ++ tailWord_668750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_668764 : List Nat := [2, 2, 4, 1, 1, 1, 1, 2, 6]
def baseStart_668764 : Nat := 118140960795 + 668764 * 2 ^ 59
def prefixEnd_668764 : Nat := 4983230072969 + 3 ^ 40 * 668764 * 2
def baseEnd_668764 : Nat := 305242112376468170199481

theorem tailTrace_668764 : CollatzResearch.WordTrace tailWord_668764 prefixEnd_668764 305242112376468170199481 := by
  unfold tailWord_668764
  simp only [CollatzResearch.WordTrace]
  refine ⟨12195913474594859321562673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16261217966126479095416897 12195913474594859321562673)
  ·
    refine ⟨9146935105946144491172005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12195913474594859321562673 9146935105946144491172005)
    ·
      refine ⟨1715050332364902092094751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9146935105946144491172005 1715050332364902092094751)
      ·
        refine ⟨2572575498547353138142127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1715050332364902092094751 2572575498547353138142127)
        ·
          refine ⟨3858863247821029707213191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2572575498547353138142127 3858863247821029707213191)
          ·
            refine ⟨5788294871731544560819787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3858863247821029707213191 5788294871731544560819787)
            ·
              refine ⟨8682442307597316841229681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5788294871731544560819787 8682442307597316841229681)
              ·
                refine ⟨6511831730697987630922261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8682442307597316841229681 6511831730697987630922261)
                ·
                  refine ⟨305242112376468170199481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6511831730697987630922261 305242112376468170199481)
                  ·
                    rfl

theorem cell20_668764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 1, 2, 6].length) (baseStart_668764 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_668764 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_668764 prefixEnd_668764 := by exact prefixLift 668764
  have htrace : WordTrace (prefixWord ++ tailWord_668764) baseStart_668764 baseEnd_668764 := by
    simpa [prefixWord, tailWord_668764, baseEnd_668764] using wordTrace_append hprefix tailTrace_668764
  have hstable : (prefixWord ++ tailWord_668764).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_668764).length < 2 ^ (prefixWord ++ tailWord_668764).sum := by decide
  have hdescent : baseEnd_668764 < baseStart_668764 := by decide
  rcases family_descends (prefixWord ++ tailWord_668764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_668781 : List Nat := [1, 5, 1, 1, 2, 3, 2, 1, 4]
def baseStart_668781 : Nat := 118140960795 + 668781 * 2 ^ 59
def prefixEnd_668781 : Nat := 4983230072969 + 3 ^ 40 * 668781 * 2
def baseEnd_668781 : Nat := 305249871639691666632745

theorem tailTrace_668781 : CollatzResearch.WordTrace tailWord_668781 prefixEnd_668781 305249871639691666632745 := by
  unfold tailWord_668781
  simp only [CollatzResearch.WordTrace]
  refine ⟨24392446990128130546494197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16261631326752087030996131 24392446990128130546494197)
  ·
    refine ⟨2286791905324512238733831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 24392446990128130546494197 2286791905324512238733831)
    ·
      refine ⟨3430187857986768358100747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2286791905324512238733831 3430187857986768358100747)
      ·
        refine ⟨5145281786980152537151121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3430187857986768358100747 5145281786980152537151121)
        ·
          refine ⟨3858961340235114402863341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5145281786980152537151121 3858961340235114402863341)
          ·
            refine ⟨1447110502588167901073753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3858961340235114402863341 1447110502588167901073753)
            ·
              refine ⟨1085332876941125925805315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1447110502588167901073753 1085332876941125925805315)
              ·
                refine ⟨1627999315411688888707973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1085332876941125925805315 1627999315411688888707973)
                ·
                  refine ⟨305249871639691666632745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1627999315411688888707973 305249871639691666632745)
                  ·
                    rfl

theorem cell20_668781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 3, 2, 1, 4].length) (baseStart_668781 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_668781 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_668781 prefixEnd_668781 := by exact prefixLift 668781
  have htrace : WordTrace (prefixWord ++ tailWord_668781) baseStart_668781 baseEnd_668781 := by
    simpa [prefixWord, tailWord_668781, baseEnd_668781] using wordTrace_append hprefix tailTrace_668781
  have hstable : (prefixWord ++ tailWord_668781).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_668781).length < 2 ^ (prefixWord ++ tailWord_668781).sum := by decide
  have hdescent : baseEnd_668781 < baseStart_668781 := by decide
  rcases family_descends (prefixWord ++ tailWord_668781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_668805 : List Nat := [1, 3, 1, 1, 6, 2, 2, 4]
def baseStart_668805 : Nat := 118140960795 + 668805 * 2 ^ 59
def prefixEnd_668805 : Nat := 4983230072969 + 3 ^ 40 * 668805 * 2
def baseEnd_668805 : Nat := 101753608631218083277549

theorem tailTrace_668805 : CollatzResearch.WordTrace tailWord_668805 prefixEnd_668805 101753608631218083277549 := by
  unfold tailWord_668805
  simp only [CollatzResearch.WordTrace]
  refine ⟨24393322342041182645367869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16262214894694121763578579 24393322342041182645367869)
  ·
    refine ⟨9147495878265443492012951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24393322342041182645367869 9147495878265443492012951)
    ·
      refine ⟨13721243817398165238019427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9147495878265443492012951 13721243817398165238019427)
      ·
        refine ⟨20581865726097247857029141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13721243817398165238019427 20581865726097247857029141)
        ·
          refine ⟨964774955910808493298241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 20581865726097247857029141 964774955910808493298241)
          ·
            refine ⟨723581216933106369973681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 964774955910808493298241 723581216933106369973681)
            ·
              refine ⟨542685912699829777480261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 723581216933106369973681 542685912699829777480261)
              ·
                refine ⟨101753608631218083277549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 542685912699829777480261 101753608631218083277549)
                ·
                  rfl

theorem cell20_668805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 2, 2, 4].length) (baseStart_668805 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_668805 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_668805 prefixEnd_668805 := by exact prefixLift 668805
  have htrace : WordTrace (prefixWord ++ tailWord_668805) baseStart_668805 baseEnd_668805 := by
    simpa [prefixWord, tailWord_668805, baseEnd_668805] using wordTrace_append hprefix tailTrace_668805
  have hstable : (prefixWord ++ tailWord_668805).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_668805).length < 2 ^ (prefixWord ++ tailWord_668805).sum := by decide
  have hdescent : baseEnd_668805 < baseStart_668805 := by decide
  rcases family_descends (prefixWord ++ tailWord_668805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_668809 : List Nat := [1, 2, 1, 1, 4, 4, 1, 6]
def baseStart_668809 : Nat := 118140960795 + 668809 * 2 ^ 59
def prefixEnd_668809 : Nat := 4983230072969 + 3 ^ 40 * 668809 * 2
def baseEnd_668809 : Nat := 101754217200882671233099

theorem tailTrace_668809 : CollatzResearch.WordTrace tailWord_668809 prefixEnd_668809 101754217200882671233099 := by
  unfold tailWord_668809
  simp only [CollatzResearch.WordTrace]
  refine ⟨24393468234026691328513481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16262312156017794219008987 24393468234026691328513481)
  ·
    refine ⟨18295101175520018496385111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24393468234026691328513481 18295101175520018496385111)
    ·
      refine ⟨27442651763280027744577667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18295101175520018496385111 27442651763280027744577667)
      ·
        refine ⟨41163977644920041616866501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27442651763280027744577667 41163977644920041616866501)
        ·
          refine ⟨7718245808422507803162469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 41163977644920041616866501 7718245808422507803162469)
          ·
            refine ⟨1447171089079220213092963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7718245808422507803162469 1447171089079220213092963)
            ·
              refine ⟨2170756633618830319639445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1447171089079220213092963 2170756633618830319639445)
              ·
                refine ⟨101754217200882671233099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2170756633618830319639445 101754217200882671233099)
                ·
                  rfl

theorem cell20_668809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 4, 1, 6].length) (baseStart_668809 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_668809 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_668809 prefixEnd_668809 := by exact prefixLift 668809
  have htrace : WordTrace (prefixWord ++ tailWord_668809) baseStart_668809 baseEnd_668809 := by
    simpa [prefixWord, tailWord_668809, baseEnd_668809] using wordTrace_append hprefix tailTrace_668809
  have hstable : (prefixWord ++ tailWord_668809).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_668809).length < 2 ^ (prefixWord ++ tailWord_668809).sum := by decide
  have hdescent : baseEnd_668809 < baseStart_668809 := by decide
  rcases family_descends (prefixWord ++ tailWord_668809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_668819 : List Nat := [1, 1, 1, 2, 1, 2, 7, 3, 2]
def baseStart_668819 : Nat := 118140960795 + 668819 * 2 ^ 59
def prefixEnd_668819 : Nat := 4983230072969 + 3 ^ 40 * 668819 * 2
def baseEnd_668819 : Nat := 305267215875132423365923

theorem tailTrace_668819 : CollatzResearch.WordTrace tailWord_668819 prefixEnd_668819 305267215875132423365923 := by
  unfold tailWord_668819
  simp only [CollatzResearch.WordTrace]
  refine ⟨24393832963990463036377511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16262555309326975357585007 24393832963990463036377511)
  ·
    refine ⟨36590749445985694554566267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24393832963990463036377511 36590749445985694554566267)
    ·
      refine ⟨54886124168978541831849401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36590749445985694554566267 54886124168978541831849401)
      ·
        refine ⟨41164593126733906373887051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54886124168978541831849401 41164593126733906373887051)
        ·
          refine ⟨61746889690100859560830577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41164593126733906373887051 61746889690100859560830577)
          ·
            refine ⟨46310167267575644670622933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61746889690100859560830577 46310167267575644670622933)
            ·
              refine ⟨1085394545333804171967725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 46310167267575644670622933 1085394545333804171967725)
              ·
                refine ⟨407022954500176564487897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1085394545333804171967725 407022954500176564487897)
                ·
                  refine ⟨305267215875132423365923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 407022954500176564487897 305267215875132423365923)
                  ·
                    rfl

theorem cell20_668819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 7, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 7, 3, 2].length) (baseStart_668819 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_668819 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_668819 prefixEnd_668819 := by exact prefixLift 668819
  have htrace : WordTrace (prefixWord ++ tailWord_668819) baseStart_668819 baseEnd_668819 := by
    simpa [prefixWord, tailWord_668819, baseEnd_668819] using wordTrace_append hprefix tailTrace_668819
  have hstable : (prefixWord ++ tailWord_668819).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_668819).length < 2 ^ (prefixWord ++ tailWord_668819).sum := by decide
  have hdescent : baseEnd_668819 < baseStart_668819 := by decide
  rcases family_descends (prefixWord ++ tailWord_668819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_668826 : List Nat := [3, 1, 1, 5, 1, 3, 6]
def baseStart_668826 : Nat := 118140960795 + 668826 * 2 ^ 59
def prefixEnd_668826 : Nat := 4983230072969 + 3 ^ 40 * 668826 * 2
def baseEnd_668826 : Nat := 33918934540652390014729

theorem tailTrace_668826 : CollatzResearch.WordTrace tailWord_668826 prefixEnd_668826 33918934540652390014729 := by
  unfold tailWord_668826
  simp only [CollatzResearch.WordTrace]
  refine ⟨6098522068741275807970583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16262725516643402154588221 6098522068741275807970583)
  ·
    refine ⟨9147783103111913711955875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6098522068741275807970583 9147783103111913711955875)
    ·
      refine ⟨13721674654667870567933813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9147783103111913711955875 13721674654667870567933813)
      ·
        refine ⟨1286406998875112865743795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 13721674654667870567933813 1286406998875112865743795)
        ·
          refine ⟨1929610498312669298615693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1286406998875112865743795 1929610498312669298615693)
          ·
            refine ⟨723603936867250986980885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1929610498312669298615693 723603936867250986980885)
            ·
              refine ⟨33918934540652390014729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 723603936867250986980885 33918934540652390014729)
              ·
                rfl

theorem cell20_668826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 3, 6].length) (baseStart_668826 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_668826 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_668826 prefixEnd_668826 := by exact prefixLift 668826
  have htrace : WordTrace (prefixWord ++ tailWord_668826) baseStart_668826 baseEnd_668826 := by
    simpa [prefixWord, tailWord_668826, baseEnd_668826] using wordTrace_append hprefix tailTrace_668826
  have hstable : (prefixWord ++ tailWord_668826).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_668826).length < 2 ^ (prefixWord ++ tailWord_668826).sum := by decide
  have hdescent : baseEnd_668826 < baseStart_668826 := by decide
  rcases family_descends (prefixWord ++ tailWord_668826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_668833 : List Nat := [1, 2, 3, 3, 1, 1, 2, 4, 3]
def baseStart_668833 : Nat := 118140960795 + 668833 * 2 ^ 59
def prefixEnd_668833 : Nat := 4983230072969 + 3 ^ 40 * 668833 * 2
def baseEnd_668833 : Nat := 305273605856610596899199

theorem tailTrace_668833 : CollatzResearch.WordTrace tailWord_668833 prefixEnd_668833 305273605856610596899199 := by
  unfold tailWord_668833
  simp only [CollatzResearch.WordTrace]
  refine ⟨24394343585939743427387153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16262895723959828951591435 24394343585939743427387153)
  ·
    refine ⟨18295757689454807570540365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24394343585939743427387153 18295757689454807570540365)
    ·
      refine ⟨6860909133545552838952637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18295757689454807570540365 6860909133545552838952637)
      ·
        refine ⟨2572840925079582314607239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6860909133545552838952637 2572840925079582314607239)
        ·
          refine ⟨3859261387619373471910859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2572840925079582314607239 3859261387619373471910859)
          ·
            refine ⟨5788892081429060207866289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3859261387619373471910859 5788892081429060207866289)
            ·
              refine ⟨4341669061071795155899717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5788892081429060207866289 4341669061071795155899717)
              ·
                refine ⟨814062948950961591731197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4341669061071795155899717 814062948950961591731197)
                ·
                  refine ⟨305273605856610596899199, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 814062948950961591731197 305273605856610596899199)
                  ·
                    rfl

theorem cell20_668833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 2, 4, 3].length) (baseStart_668833 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_668833 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_668833 prefixEnd_668833 := by exact prefixLift 668833
  have htrace : WordTrace (prefixWord ++ tailWord_668833) baseStart_668833 baseEnd_668833 := by
    simpa [prefixWord, tailWord_668833, baseEnd_668833] using wordTrace_append hprefix tailTrace_668833
  have hstable : (prefixWord ++ tailWord_668833).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_668833).length < 2 ^ (prefixWord ++ tailWord_668833).sum := by decide
  have hdescent : baseEnd_668833 < baseStart_668833 := by decide
  rcases family_descends (prefixWord ++ tailWord_668833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_668850 : List Nat := [3, 2, 1, 1, 1, 4, 4, 1, 3]
def baseStart_668850 : Nat := 118140960795 + 668850 * 2 ^ 59
def prefixEnd_668850 : Nat := 4983230072969 + 3 ^ 40 * 668850 * 2
def baseEnd_668850 : Nat := 305281365119834093332463

theorem tailTrace_668850 : CollatzResearch.WordTrace tailWord_668850 prefixEnd_668850 305281365119834093332463 := by
  unfold tailWord_668850
  simp only [CollatzResearch.WordTrace]
  refine ⟨6098740906719538832689001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16263309084585436887170669 6098740906719538832689001)
  ·
    refine ⟨4574055680039654124516751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6098740906719538832689001 4574055680039654124516751)
    ·
      refine ⟨6861083520059481186775127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4574055680039654124516751 6861083520059481186775127)
      ·
        refine ⟨10291625280089221780162691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6861083520059481186775127 10291625280089221780162691)
        ·
          refine ⟨15437437920133832670244037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10291625280089221780162691 15437437920133832670244037)
          ·
            refine ⟨2894519610025093625670757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15437437920133832670244037 2894519610025093625670757)
            ·
              refine ⟨542722426879705054813267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2894519610025093625670757 542722426879705054813267)
              ·
                refine ⟨814083640319557582219901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 542722426879705054813267 814083640319557582219901)
                ·
                  refine ⟨305281365119834093332463, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 814083640319557582219901 305281365119834093332463)
                  ·
                    rfl

theorem cell20_668850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 4, 1, 3].length) (baseStart_668850 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_668850 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_668850 prefixEnd_668850 := by exact prefixLift 668850
  have htrace : WordTrace (prefixWord ++ tailWord_668850) baseStart_668850 baseEnd_668850 := by
    simpa [prefixWord, tailWord_668850, baseEnd_668850] using wordTrace_append hprefix tailTrace_668850
  have hstable : (prefixWord ++ tailWord_668850).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_668850).length < 2 ^ (prefixWord ++ tailWord_668850).sum := by decide
  have hdescent : baseEnd_668850 < baseStart_668850 := by decide
  rcases family_descends (prefixWord ++ tailWord_668850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_668885 : List Nat := [1, 3, 2, 4, 1, 9]
def baseStart_668885 : Nat := 118140960795 + 668885 * 2 ^ 59
def prefixEnd_668885 : Nat := 4983230072969 + 3 ^ 40 * 668885 * 2
def baseEnd_668885 : Nat := 11307308891612204709839

theorem tailTrace_668885 : CollatzResearch.WordTrace tailWord_668885 prefixEnd_668885 11307308891612204709839 := by
  unfold tailWord_668885
  simp only [CollatzResearch.WordTrace]
  refine ⟨24396240181751356308280109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16264160121167570872186739 24396240181751356308280109)
  ·
    refine ⟨9148590068156758615605041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24396240181751356308280109 9148590068156758615605041)
    ·
      refine ⟨6861442551117568961703781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9148590068156758615605041 6861442551117568961703781)
      ·
        refine ⟨1286520478334544180319459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6861442551117568961703781 1286520478334544180319459)
        ·
          refine ⟨1929780717501816270479189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1286520478334544180319459 1929780717501816270479189)
          ·
            refine ⟨11307308891612204709839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1929780717501816270479189 11307308891612204709839)
            ·
              rfl

theorem cell20_668885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 9].length) (baseStart_668885 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_668885 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_668885 prefixEnd_668885 := by exact prefixLift 668885
  have htrace : WordTrace (prefixWord ++ tailWord_668885) baseStart_668885 baseEnd_668885 := by
    simpa [prefixWord, tailWord_668885, baseEnd_668885] using wordTrace_append hprefix tailTrace_668885
  have hstable : (prefixWord ++ tailWord_668885).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_668885).length < 2 ^ (prefixWord ++ tailWord_668885).sum := by decide
  have hdescent : baseEnd_668885 < baseStart_668885 := by decide
  rcases family_descends (prefixWord ++ tailWord_668885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_668888 : List Nat := [2, 1, 2, 2, 5, 1, 2, 2, 3]
def baseStart_668888 : Nat := 118140960795 + 668888 * 2 ^ 59
def prefixEnd_668888 : Nat := 4983230072969 + 3 ^ 40 * 668888 * 2
def baseEnd_668888 : Nat := 305298709355274850065641

theorem tailTrace_668888 : CollatzResearch.WordTrace tailWord_668888 prefixEnd_668888 305298709355274850065641 := by
  unfold tailWord_668888
  simp only [CollatzResearch.WordTrace]
  refine ⟨12198174800370243910319659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16264233067160325213759545 12198174800370243910319659)
  ·
    refine ⟨18297262200555365865479489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12198174800370243910319659 18297262200555365865479489)
    ·
      refine ⟨13722946650416524399109617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18297262200555365865479489 13722946650416524399109617)
      ·
        refine ⟨10292209987812393299332213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13722946650416524399109617 10292209987812393299332213)
        ·
          refine ⟨964894686357411871812395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 10292209987812393299332213 964894686357411871812395)
          ·
            refine ⟨1447342029536117807718593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 964894686357411871812395 1447342029536117807718593)
            ·
              refine ⟨1085506522152088355788945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1447342029536117807718593 1085506522152088355788945)
              ·
                refine ⟨814129891614066266841709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1085506522152088355788945 814129891614066266841709)
                ·
                  refine ⟨305298709355274850065641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 814129891614066266841709 305298709355274850065641)
                  ·
                    rfl

theorem cell20_668888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 1, 2, 2, 3].length) (baseStart_668888 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_668888 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_668888 prefixEnd_668888 := by exact prefixLift 668888
  have htrace : WordTrace (prefixWord ++ tailWord_668888) baseStart_668888 baseEnd_668888 := by
    simpa [prefixWord, tailWord_668888, baseEnd_668888] using wordTrace_append hprefix tailTrace_668888
  have hstable : (prefixWord ++ tailWord_668888).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_668888).length < 2 ^ (prefixWord ++ tailWord_668888).sum := by decide
  have hdescent : baseEnd_668888 < baseStart_668888 := by decide
  rcases family_descends (prefixWord ++ tailWord_668888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_668933 : List Nat := [1, 3, 1, 1, 2, 1, 6, 3, 2]
def baseStart_668933 : Nat := 118140960795 + 668933 * 2 ^ 59
def prefixEnd_668933 : Nat := 4983230072969 + 3 ^ 40 * 668933 * 2
def baseEnd_668933 : Nat := 305319248581454693565457

theorem tailTrace_668933 : CollatzResearch.WordTrace tailWord_668933 prefixEnd_668933 305319248581454693565457 := by
  unfold tailWord_668933
  simp only [CollatzResearch.WordTrace]
  refine ⟨24397990885577460506027453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16265327257051640337351635 24397990885577460506027453)
  ·
    refine ⟨9149246582091547689760295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24397990885577460506027453 9149246582091547689760295)
    ·
      refine ⟨13723869873137321534640443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9149246582091547689760295 13723869873137321534640443)
      ·
        refine ⟨20585804809705982301960665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13723869873137321534640443 20585804809705982301960665)
        ·
          refine ⟨15439353607279486726470499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20585804809705982301960665 15439353607279486726470499)
          ·
            refine ⟨23159030410919230089705749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15439353607279486726470499 23159030410919230089705749)
            ·
              refine ⟨1085579550511838910454957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 23159030410919230089705749 1085579550511838910454957)
              ·
                refine ⟨407092331441939591420609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1085579550511838910454957 407092331441939591420609)
                ·
                  refine ⟨305319248581454693565457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 407092331441939591420609 305319248581454693565457)
                  ·
                    rfl

theorem cell20_668933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 6, 3, 2].length) (baseStart_668933 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_668933 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_668933 prefixEnd_668933 := by exact prefixLift 668933
  have htrace : WordTrace (prefixWord ++ tailWord_668933) baseStart_668933 baseEnd_668933 := by
    simpa [prefixWord, tailWord_668933, baseEnd_668933] using wordTrace_append hprefix tailTrace_668933
  have hstable : (prefixWord ++ tailWord_668933).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_668933).length < 2 ^ (prefixWord ++ tailWord_668933).sum := by decide
  have hdescent : baseEnd_668933 < baseStart_668933 := by decide
  rcases family_descends (prefixWord ++ tailWord_668933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_668937 : List Nat := [1, 2, 1, 1, 3, 3, 1, 2, 6]
def baseStart_668937 : Nat := 118140960795 + 668937 * 2 ^ 59
def prefixEnd_668937 : Nat := 4983230072969 + 3 ^ 40 * 668937 * 2
def baseEnd_668937 : Nat := 305321074290448457432107

theorem tailTrace_668937 : CollatzResearch.WordTrace tailWord_668937 prefixEnd_668937 305321074290448457432107 := by
  unfold tailWord_668937
  simp only [CollatzResearch.WordTrace]
  refine ⟨24398136777562969189173065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16265424518375312792782043 24398136777562969189173065)
  ·
    refine ⟨18298602583172226891879799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24398136777562969189173065 18298602583172226891879799)
    ·
      refine ⟨27447903874758340337819699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18298602583172226891879799 27447903874758340337819699)
      ·
        refine ⟨41171855812137510506729549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27447903874758340337819699 41171855812137510506729549)
        ·
          refine ⟨15439445929551566440023581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41171855812137510506729549 15439445929551566440023581)
          ·
            refine ⟨5789792223581837415008843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15439445929551566440023581 5789792223581837415008843)
            ·
              refine ⟨8684688335372756122513265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5789792223581837415008843 8684688335372756122513265)
              ·
                refine ⟨6513516251529567091884949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8684688335372756122513265 6513516251529567091884949)
                ·
                  refine ⟨305321074290448457432107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6513516251529567091884949 305321074290448457432107)
                  ·
                    rfl

theorem cell20_668937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 1, 2, 6].length) (baseStart_668937 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_668937 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_668937 prefixEnd_668937 := by exact prefixLift 668937
  have htrace : WordTrace (prefixWord ++ tailWord_668937) baseStart_668937 baseEnd_668937 := by
    simpa [prefixWord, tailWord_668937, baseEnd_668937] using wordTrace_append hprefix tailTrace_668937
  have hstable : (prefixWord ++ tailWord_668937).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_668937).length < 2 ^ (prefixWord ++ tailWord_668937).sum := by decide
  have hdescent : baseEnd_668937 < baseStart_668937 := by decide
  rcases family_descends (prefixWord ++ tailWord_668937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_668954 : List Nat := [3, 1, 1, 3, 3, 1, 1, 3, 4]
def baseStart_668954 : Nat := 118140960795 + 668954 * 2 ^ 59
def prefixEnd_668954 : Nat := 4983230072969 + 3 ^ 40 * 668954 * 2
def baseEnd_668954 : Nat := 305328833553671953865371

theorem tailTrace_668954 : CollatzResearch.WordTrace tailWord_668954 prefixEnd_668954 305328833553671953865371 := by
  unfold tailWord_668954
  simp only [CollatzResearch.WordTrace]
  refine ⟨6099689204625345273135479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16265837879000920728361277 6099689204625345273135479)
  ·
    refine ⟨9149533806938017909703219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6099689204625345273135479 9149533806938017909703219)
    ·
      refine ⟨13724300710407026864554829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9149533806938017909703219 13724300710407026864554829)
      ·
        refine ⟨5146612766402635074208061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13724300710407026864554829 5146612766402635074208061)
        ·
          refine ⟨1929979787400988152828023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5146612766402635074208061 1929979787400988152828023)
          ·
            refine ⟨2894969681101482229242035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1929979787400988152828023 2894969681101482229242035)
            ·
              refine ⟨4342454521652223343863053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2894969681101482229242035 4342454521652223343863053)
              ·
                refine ⟨1628420445619583753948645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4342454521652223343863053 1628420445619583753948645)
                ·
                  refine ⟨305328833553671953865371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1628420445619583753948645 305328833553671953865371)
                  ·
                    rfl

theorem cell20_668954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 1, 3, 4].length) (baseStart_668954 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_668954 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_668954 prefixEnd_668954 := by exact prefixLift 668954
  have htrace : WordTrace (prefixWord ++ tailWord_668954) baseStart_668954 baseEnd_668954 := by
    simpa [prefixWord, tailWord_668954, baseEnd_668954] using wordTrace_append hprefix tailTrace_668954
  have hstable : (prefixWord ++ tailWord_668954).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_668954).length < 2 ^ (prefixWord ++ tailWord_668954).sum := by decide
  have hdescent : baseEnd_668954 < baseStart_668954 := by decide
  rcases family_descends (prefixWord ++ tailWord_668954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_668964 : List Nat := [2, 3, 1, 3, 1, 1, 5, 1, 3]
def baseStart_668964 : Nat := 118140960795 + 668964 * 2 ^ 59
def prefixEnd_668964 : Nat := 4983230072969 + 3 ^ 40 * 668964 * 2
def baseEnd_668964 : Nat := 305333397826156363531997

theorem tailTrace_668964 : CollatzResearch.WordTrace tailWord_668964 prefixEnd_668964 305333397826156363531997 := by
  unfold tailWord_668964
  simp only [CollatzResearch.WordTrace]
  refine ⟨12199560774232576400202973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16266081032310101866937297 12199560774232576400202973)
  ·
    refine ⟨4574835290337216150076115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12199560774232576400202973 4574835290337216150076115)
    ·
      refine ⟨6862252935505824225114173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4574835290337216150076115 6862252935505824225114173)
      ·
        refine ⟨2573344850814684084417815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6862252935505824225114173 2573344850814684084417815)
        ·
          refine ⟨3860017276222026126626723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2573344850814684084417815 3860017276222026126626723)
          ·
            refine ⟨5790025914333039189940085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3860017276222026126626723 5790025914333039189940085)
            ·
              refine ⟨542814929468722424056883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5790025914333039189940085 542814929468722424056883)
              ·
                refine ⟨814222394203083636085325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 542814929468722424056883 814222394203083636085325)
                ·
                  refine ⟨305333397826156363531997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 814222394203083636085325 305333397826156363531997)
                  ·
                    rfl

theorem cell20_668964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 5, 1, 3].length) (baseStart_668964 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_668964 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_668964 prefixEnd_668964 := by exact prefixLift 668964
  have htrace : WordTrace (prefixWord ++ tailWord_668964) baseStart_668964 baseEnd_668964 := by
    simpa [prefixWord, tailWord_668964, baseEnd_668964] using wordTrace_append hprefix tailTrace_668964
  have hstable : (prefixWord ++ tailWord_668964).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_668964).length < 2 ^ (prefixWord ++ tailWord_668964).sum := by decide
  have hdescent : baseEnd_668964 < baseStart_668964 := by decide
  rcases family_descends (prefixWord ++ tailWord_668964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_668978 : List Nat := [3, 2, 1, 1, 4, 1, 4, 4]
def baseStart_668978 : Nat := 118140960795 + 668978 * 2 ^ 59
def prefixEnd_668978 : Nat := 4983230072969 + 3 ^ 40 * 668978 * 2
def baseEnd_668978 : Nat := 101779929269211512355091

theorem tailTrace_668978 : CollatzResearch.WordTrace tailWord_668978 prefixEnd_668978 101779929269211512355091 := by
  unfold tailWord_668978
  simp only [CollatzResearch.WordTrace]
  refine ⟨6099908042603608297853897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16266421446942955460943725 6099908042603608297853897)
  ·
    refine ⟨4574931031952706223390423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6099908042603608297853897 4574931031952706223390423)
    ·
      refine ⟨6862396547929059335085635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4574931031952706223390423 6862396547929059335085635)
      ·
        refine ⟨10293594821893589002628453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6862396547929059335085635 10293594821893589002628453)
        ·
          refine ⟨1930049029105047937992835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10293594821893589002628453 1930049029105047937992835)
          ·
            refine ⟨2895073543657571906989253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1930049029105047937992835 2895073543657571906989253)
            ·
              refine ⟨542826289435794732560485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2895073543657571906989253 542826289435794732560485)
              ·
                refine ⟨101779929269211512355091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 542826289435794732560485 101779929269211512355091)
                ·
                  rfl

theorem cell20_668978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 4, 4].length) (baseStart_668978 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_668978 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_668978 prefixEnd_668978 := by exact prefixLift 668978
  have htrace : WordTrace (prefixWord ++ tailWord_668978) baseStart_668978 baseEnd_668978 := by
    simpa [prefixWord, tailWord_668978, baseEnd_668978] using wordTrace_append hprefix tailTrace_668978
  have hstable : (prefixWord ++ tailWord_668978).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_668978).length < 2 ^ (prefixWord ++ tailWord_668978).sum := by decide
  have hdescent : baseEnd_668978 < baseStart_668978 := by decide
  rcases family_descends (prefixWord ++ tailWord_668978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_668988 : List Nat := [2, 2, 2, 2, 1, 5, 1, 3, 2]
def baseStart_668988 : Nat := 118140960795 + 668988 * 2 ^ 59
def prefixEnd_668988 : Nat := 4983230072969 + 3 ^ 40 * 668988 * 2
def baseEnd_668988 : Nat := 305344352080118946731899

theorem tailTrace_668988 : CollatzResearch.WordTrace tailWord_668988 prefixEnd_668988 305344352080118946731899 := by
  unfold tailWord_668988
  simp only [CollatzResearch.WordTrace]
  refine ⟨12199998450189102449639809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16266664600252136599519745 12199998450189102449639809)
  ·
    refine ⟨9149998837641826837229857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12199998450189102449639809 9149998837641826837229857)
    ·
      refine ⟨6862499128231370127922393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9149998837641826837229857 6862499128231370127922393)
      ·
        refine ⟨5146874346173527595941795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6862499128231370127922393 5146874346173527595941795)
        ·
          refine ⟨7720311519260291393912693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5146874346173527595941795 7720311519260291393912693)
          ·
            refine ⟨723779204930652318179315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 7720311519260291393912693 723779204930652318179315)
            ·
              refine ⟨1085668807395978477268973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 723779204930652318179315 1085668807395978477268973)
              ·
                refine ⟨407125802773491928975865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1085668807395978477268973 407125802773491928975865)
                ·
                  refine ⟨305344352080118946731899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 407125802773491928975865 305344352080118946731899)
                  ·
                    rfl

theorem cell20_668988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 5, 1, 3, 2].length) (baseStart_668988 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_668988 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_668988 prefixEnd_668988 := by exact prefixLift 668988
  have htrace : WordTrace (prefixWord ++ tailWord_668988) baseStart_668988 baseEnd_668988 := by
    simpa [prefixWord, tailWord_668988, baseEnd_668988] using wordTrace_append hprefix tailTrace_668988
  have hstable : (prefixWord ++ tailWord_668988).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_668988).length < 2 ^ (prefixWord ++ tailWord_668988).sum := by decide
  have hdescent : baseEnd_668988 < baseStart_668988 := by decide
  rcases family_descends (prefixWord ++ tailWord_668988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_668999 : List Nat := [1, 1, 4, 1, 2, 5, 6]
def baseStart_668999 : Nat := 118140960795 + 668999 * 2 ^ 59
def prefixEnd_668999 : Nat := 4983230072969 + 3 ^ 40 * 668999 * 2
def baseEnd_668999 : Nat := 33927708086650199707243

theorem tailTrace_668999 : CollatzResearch.WordTrace tailWord_668999 prefixEnd_668999 33927708086650199707243 := by
  unfold tailWord_668999
  simp only [CollatzResearch.WordTrace]
  refine ⟨24400398103338353777930051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16266932068892235851953367 24400398103338353777930051)
  ·
    refine ⟨36600597155007530666895077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24400398103338353777930051 36600597155007530666895077)
    ·
      refine ⟨6862611966563912000042827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 36600597155007530666895077 6862611966563912000042827)
      ·
        refine ⟨10293917949845868000064241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6862611966563912000042827 10293917949845868000064241)
        ·
          refine ⟨7720438462384401000048181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10293917949845868000064241 7720438462384401000048181)
          ·
            refine ⟨723791105848537593754517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 7720438462384401000048181 723791105848537593754517)
            ·
              refine ⟨33927708086650199707243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 723791105848537593754517 33927708086650199707243)
              ·
                rfl

theorem cell20_668999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 5, 6].length) (baseStart_668999 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_668999 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_668999 prefixEnd_668999 := by exact prefixLift 668999
  have htrace : WordTrace (prefixWord ++ tailWord_668999) baseStart_668999 baseEnd_668999 := by
    simpa [prefixWord, tailWord_668999, baseEnd_668999] using wordTrace_append hprefix tailTrace_668999
  have hstable : (prefixWord ++ tailWord_668999).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_668999).length < 2 ^ (prefixWord ++ tailWord_668999).sum := by decide
  have hdescent : baseEnd_668999 < baseStart_668999 := by decide
  rcases family_descends (prefixWord ++ tailWord_668999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_669005 : List Nat := [1, 6, 1, 3, 1, 2, 1, 1, 4]
def baseStart_669005 : Nat := 118140960795 + 669005 * 2 ^ 59
def prefixEnd_669005 : Nat := 4983230072969 + 3 ^ 40 * 669005 * 2
def baseEnd_669005 : Nat := 305352111343342443165163

theorem tailTrace_669005 : CollatzResearch.WordTrace tailWord_669005 prefixEnd_669005 305352111343342443165163 := by
  unfold tailWord_669005
  simp only [CollatzResearch.WordTrace]
  refine ⟨24400616941316616802648469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16267077960877744535098979 24400616941316616802648469)
  ·
    refine ⟨1143778919124216412624147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 24400616941316616802648469 1143778919124216412624147)
    ·
      refine ⟨1715668378686324618936221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1143778919124216412624147 1715668378686324618936221)
      ·
        refine ⟨643375642007371732101083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1715668378686324618936221 643375642007371732101083)
        ·
          refine ⟨965063463011057598151625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 643375642007371732101083 965063463011057598151625)
          ·
            refine ⟨723797597258293198613719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 965063463011057598151625 723797597258293198613719)
            ·
              refine ⟨1085696395887439797920579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 723797597258293198613719 1085696395887439797920579)
              ·
                refine ⟨1628544593831159696880869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1085696395887439797920579 1628544593831159696880869)
                ·
                  refine ⟨305352111343342443165163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1628544593831159696880869 305352111343342443165163)
                  ·
                    rfl

theorem cell20_669005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 2, 1, 1, 4].length) (baseStart_669005 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_669005 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_669005 prefixEnd_669005 := by exact prefixLift 669005
  have htrace : WordTrace (prefixWord ++ tailWord_669005) baseStart_669005 baseEnd_669005 := by
    simpa [prefixWord, tailWord_669005, baseEnd_669005] using wordTrace_append hprefix tailTrace_669005
  have hstable : (prefixWord ++ tailWord_669005).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_669005).length < 2 ^ (prefixWord ++ tailWord_669005).sum := by decide
  have hdescent : baseEnd_669005 < baseStart_669005 := by decide
  rcases family_descends (prefixWord ++ tailWord_669005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_669006 : List Nat := [4, 1, 1, 1, 1, 1, 3, 3, 5]
def baseStart_669006 : Nat := 118140960795 + 669006 * 2 ^ 59
def prefixEnd_669006 : Nat := 4983230072969 + 3 ^ 40 * 669006 * 2
def baseEnd_669006 : Nat := 305352567770590884131825

theorem tailTrace_669006 : CollatzResearch.WordTrace tailWord_669006 prefixEnd_669006 305352567770590884131825 := by
  unfold tailWord_669006
  simp only [CollatzResearch.WordTrace]
  refine ⟨3050081676789124246679359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16267102276208662648956581 3050081676789124246679359)
  ·
    refine ⟨4575122515183686370019039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3050081676789124246679359 4575122515183686370019039)
    ·
      refine ⟨6862683772775529555028559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4575122515183686370019039 6862683772775529555028559)
      ·
        refine ⟨10294025659163294332542839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6862683772775529555028559 10294025659163294332542839)
        ·
          refine ⟨15441038488744941498814259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10294025659163294332542839 15441038488744941498814259)
          ·
            refine ⟨23161557733117412248221389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15441038488744941498814259 23161557733117412248221389)
            ·
              refine ⟨8685584149919029593083021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23161557733117412248221389 8685584149919029593083021)
              ·
                refine ⟨3257094056219636097406133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8685584149919029593083021 3257094056219636097406133)
                ·
                  refine ⟨305352567770590884131825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3257094056219636097406133 305352567770590884131825)
                  ·
                    rfl

theorem cell20_669006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 3, 3, 5].length) (baseStart_669006 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_669006 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_669006 prefixEnd_669006 := by exact prefixLift 669006
  have htrace : WordTrace (prefixWord ++ tailWord_669006) baseStart_669006 baseEnd_669006 := by
    simpa [prefixWord, tailWord_669006, baseEnd_669006] using wordTrace_append hprefix tailTrace_669006
  have hstable : (prefixWord ++ tailWord_669006).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_669006).length < 2 ^ (prefixWord ++ tailWord_669006).sum := by decide
  have hdescent : baseEnd_669006 < baseStart_669006 := by decide
  rcases family_descends (prefixWord ++ tailWord_669006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_669037 : List Nat := [1, 5, 1, 1, 1, 3, 2, 6]
def baseStart_669037 : Nat := 118140960795 + 669037 * 2 ^ 59
def prefixEnd_669037 : Nat := 4983230072969 + 3 ^ 40 * 669037 * 2
def baseEnd_669037 : Nat := 101788905671764184699455

theorem tailTrace_669037 : CollatzResearch.WordTrace tailWord_669037 prefixEnd_669037 101788905671764184699455 := by
  unfold tailWord_669037
  simp only [CollatzResearch.WordTrace]
  refine ⟨24401784077200686267813365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16267856051467124178542243 24401784077200686267813365)
  ·
    refine ⟨2287667257237564337607503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 24401784077200686267813365 2287667257237564337607503)
    ·
      refine ⟨3431500885856346506411255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2287667257237564337607503 3431500885856346506411255)
      ·
        refine ⟨5147251328784519759616883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3431500885856346506411255 5147251328784519759616883)
        ·
          refine ⟨7720876993176779639425325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5147251328784519759616883 7720876993176779639425325)
          ·
            refine ⟨2895328872441292364784497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7720876993176779639425325 2895328872441292364784497)
            ·
              refine ⟨2171496654330969273588373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2895328872441292364784497 2171496654330969273588373)
              ·
                refine ⟨101788905671764184699455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2171496654330969273588373 101788905671764184699455)
                ·
                  rfl

theorem cell20_669037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 2, 6].length) (baseStart_669037 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_669037 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_669037 prefixEnd_669037 := by exact prefixLift 669037
  have htrace : WordTrace (prefixWord ++ tailWord_669037) baseStart_669037 baseEnd_669037 := by
    simpa [prefixWord, tailWord_669037, baseEnd_669037] using wordTrace_append hprefix tailTrace_669037
  have hstable : (prefixWord ++ tailWord_669037).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_669037).length < 2 ^ (prefixWord ++ tailWord_669037).sum := by decide
  have hdescent : baseEnd_669037 < baseStart_669037 := by decide
  rcases family_descends (prefixWord ++ tailWord_669037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_669054 : List Nat := [4, 2, 3, 2, 9]
def baseStart_669054 : Nat := 118140960795 + 669054 * 2 ^ 59
def prefixEnd_669054 : Nat := 4983230072969 + 3 ^ 40 * 669054 * 2
def baseEnd_669054 : Nat := 3770055262697729018909

theorem tailTrace_669054 : CollatzResearch.WordTrace tailWord_669054 prefixEnd_669054 3770055262697729018909 := by
  unfold tailWord_669054
  simp only [CollatzResearch.WordTrace]
  refine ⟨3050300514767387271397777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16268269412092732114121477 3050300514767387271397777)
  ·
    refine ⟨2287725386075540453548333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3050300514767387271397777 2287725386075540453548333)
    ·
      refine ⟨857897019778327670080625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2287725386075540453548333 857897019778327670080625)
      ·
        refine ⟨643422764833745752560469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 857897019778327670080625 643422764833745752560469)
        ·
          refine ⟨3770055262697729018909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 9 643422764833745752560469 3770055262697729018909)
          ·
            rfl

theorem cell20_669054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 9].length) (baseStart_669054 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_669054 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_669054 prefixEnd_669054 := by exact prefixLift 669054
  have htrace : WordTrace (prefixWord ++ tailWord_669054) baseStart_669054 baseEnd_669054 := by
    simpa [prefixWord, tailWord_669054, baseEnd_669054] using wordTrace_append hprefix tailTrace_669054
  have hstable : (prefixWord ++ tailWord_669054).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_669054).length < 2 ^ (prefixWord ++ tailWord_669054).sum := by decide
  have hdescent : baseEnd_669054 < baseStart_669054 := by decide
  rcases family_descends (prefixWord ++ tailWord_669054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_669064 : List Nat := [2, 1, 3, 3, 1, 2, 4, 2, 2]
def baseStart_669064 : Nat := 118140960795 + 669064 * 2 ^ 59
def prefixEnd_669064 : Nat := 4983230072969 + 3 ^ 40 * 669064 * 2
def baseEnd_669064 : Nat := 305379040551000460198255

theorem tailTrace_669064 : CollatzResearch.WordTrace tailWord_669064 prefixEnd_669064 305379040551000460198255 := by
  unfold tailWord_669064
  simp only [CollatzResearch.WordTrace]
  refine ⟨12201384424051434939523123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16268512565401913252697497 12201384424051434939523123)
  ·
    refine ⟨18302076636077152409284685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12201384424051434939523123 18302076636077152409284685)
    ·
      refine ⟨6863278738528932153481757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18302076636077152409284685 6863278738528932153481757)
      ·
        refine ⟨2573729526948349557555659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6863278738528932153481757 2573729526948349557555659)
        ·
          refine ⟨3860594290422524336333489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2573729526948349557555659 3860594290422524336333489)
          ·
            refine ⟨2895445717816893252250117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3860594290422524336333489 2895445717816893252250117)
            ·
              refine ⟨542896072090667484796897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2895445717816893252250117 542896072090667484796897)
              ·
                refine ⟨407172054068000613597673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 542896072090667484796897 407172054068000613597673)
                ·
                  refine ⟨305379040551000460198255, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 407172054068000613597673 305379040551000460198255)
                  ·
                    rfl

theorem cell20_669064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 4, 2, 2].length) (baseStart_669064 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_669064 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_669064 prefixEnd_669064 := by exact prefixLift 669064
  have htrace : WordTrace (prefixWord ++ tailWord_669064) baseStart_669064 baseEnd_669064 := by
    simpa [prefixWord, tailWord_669064, baseEnd_669064] using wordTrace_append hprefix tailTrace_669064
  have hstable : (prefixWord ++ tailWord_669064).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_669064).length < 2 ^ (prefixWord ++ tailWord_669064).sum := by decide
  have hdescent : baseEnd_669064 < baseStart_669064 := by decide
  rcases family_descends (prefixWord ++ tailWord_669064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_669113 : List Nat := [1, 2, 1, 4, 4, 1, 7]
def baseStart_669113 : Nat := 118140960795 + 669113 * 2 ^ 59
def prefixEnd_669113 : Nat := 4983230072969 + 3 ^ 40 * 669113 * 2
def baseEnd_669113 : Nat := 33933489498463785284969

theorem tailTrace_669113 : CollatzResearch.WordTrace tailWord_669113 prefixEnd_669113 33933489498463785284969 := by
  unfold tailWord_669113
  simp only [CollatzResearch.WordTrace]
  refine ⟨24404556024925351247579993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16269704016616900831719995 24404556024925351247579993)
  ·
    refine ⟨18303417018694013435684995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24404556024925351247579993 18303417018694013435684995)
    ·
      refine ⟨27455125528041020153527493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18303417018694013435684995 27455125528041020153527493)
      ·
        refine ⟨5147836036507691278786405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 27455125528041020153527493 5147836036507691278786405)
        ·
          refine ⟨965219256845192114772451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5147836036507691278786405 965219256845192114772451)
          ·
            refine ⟨1447828885267788172158677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 965219256845192114772451 1447828885267788172158677)
            ·
              refine ⟨33933489498463785284969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1447828885267788172158677 33933489498463785284969)
              ·
                rfl

theorem cell20_669113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 1, 7].length) (baseStart_669113 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_669113 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_669113 prefixEnd_669113 := by exact prefixLift 669113
  have htrace : WordTrace (prefixWord ++ tailWord_669113) baseStart_669113 baseEnd_669113 := by
    simpa [prefixWord, tailWord_669113, baseEnd_669113] using wordTrace_append hprefix tailTrace_669113
  have hstable : (prefixWord ++ tailWord_669113).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_669113).length < 2 ^ (prefixWord ++ tailWord_669113).sum := by decide
  have hdescent : baseEnd_669113 < baseStart_669113 := by decide
  rcases family_descends (prefixWord ++ tailWord_669113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_669188 : List Nat := [2, 3, 2, 3, 3, 1, 2, 1, 3]
def baseStart_669188 : Nat := 118140960795 + 669188 * 2 ^ 59
def prefixEnd_669188 : Nat := 4983230072969 + 3 ^ 40 * 669188 * 2
def baseEnd_669188 : Nat := 305435637529807140064415

theorem tailTrace_669188 : CollatzResearch.WordTrace tailWord_669188 prefixEnd_669188 305435637529807140064415 := by
  unfold tailWord_669188
  simp only [CollatzResearch.WordTrace]
  refine ⟨12203645749826819528280109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16271527666435759371040145 12203645749826819528280109)
  ·
    refine ⟨4576367156185057323105041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12203645749826819528280109 4576367156185057323105041)
    ·
      refine ⟨3432275367138792992328781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4576367156185057323105041 3432275367138792992328781)
      ·
        refine ⟨1287103262677047372123293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3432275367138792992328781 1287103262677047372123293)
        ·
          refine ⟨482663723503892764546235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1287103262677047372123293 482663723503892764546235)
          ·
            refine ⟨723995585255839146819353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 482663723503892764546235 723995585255839146819353)
            ·
              refine ⟨542996688941879360114515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 723995585255839146819353 542996688941879360114515)
              ·
                refine ⟨814495033412819040171773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 542996688941879360114515 814495033412819040171773)
                ·
                  refine ⟨305435637529807140064415, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 814495033412819040171773 305435637529807140064415)
                  ·
                    rfl

theorem cell20_669188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 3, 1, 2, 1, 3].length) (baseStart_669188 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_669188 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_669188 prefixEnd_669188 := by exact prefixLift 669188
  have htrace : WordTrace (prefixWord ++ tailWord_669188) baseStart_669188 baseEnd_669188 := by
    simpa [prefixWord, tailWord_669188, baseEnd_669188] using wordTrace_append hprefix tailTrace_669188
  have hstable : (prefixWord ++ tailWord_669188).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_669188).length < 2 ^ (prefixWord ++ tailWord_669188).sum := by decide
  have hdescent : baseEnd_669188 < baseStart_669188 := by decide
  rcases family_descends (prefixWord ++ tailWord_669188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_669230 : List Nat := [4, 1, 3, 1, 2, 2, 2, 2, 3]
def baseStart_669230 : Nat := 118140960795 + 669230 * 2 ^ 59
def prefixEnd_669230 : Nat := 4983230072969 + 3 ^ 40 * 669230 * 2
def baseEnd_669230 : Nat := 305454807474241660664243

theorem tailTrace_669230 : CollatzResearch.WordTrace tailWord_669230 prefixEnd_669230 305454807474241660664243 := by
  unfold tailWord_669230
  simp only [CollatzResearch.WordTrace]
  refine ⟨3051102920687685028698643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16272548910334320153059429 3051102920687685028698643)
  ·
    refine ⟨4576654381031527543047965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3051102920687685028698643 4576654381031527543047965)
    ·
      refine ⟨1716245392886822828642987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4576654381031527543047965 1716245392886822828642987)
      ·
        refine ⟨2574368089330234242964481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1716245392886822828642987 2574368089330234242964481)
        ·
          refine ⟨1930776066997675682223361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2574368089330234242964481 1930776066997675682223361)
          ·
            refine ⟨1448082050248256761667521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1930776066997675682223361 1448082050248256761667521)
            ·
              refine ⟨1086061537686192571250641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1448082050248256761667521 1086061537686192571250641)
              ·
                refine ⟨814546153264644428437981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1086061537686192571250641 814546153264644428437981)
                ·
                  refine ⟨305454807474241660664243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 814546153264644428437981 305454807474241660664243)
                  ·
                    rfl

theorem cell20_669230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 2, 2, 2, 3].length) (baseStart_669230 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_669230 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_669230 prefixEnd_669230 := by exact prefixLift 669230
  have htrace : WordTrace (prefixWord ++ tailWord_669230) baseStart_669230 baseEnd_669230 := by
    simpa [prefixWord, tailWord_669230, baseEnd_669230] using wordTrace_append hprefix tailTrace_669230
  have hstable : (prefixWord ++ tailWord_669230).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_669230).length < 2 ^ (prefixWord ++ tailWord_669230).sum := by decide
  have hdescent : baseEnd_669230 < baseStart_669230 := by decide
  rcases family_descends (prefixWord ++ tailWord_669230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_669237 : List Nat := [1, 3, 3, 1, 1, 4, 1, 4, 2]
def baseStart_669237 : Nat := 118140960795 + 669237 * 2 ^ 59
def prefixEnd_669237 : Nat := 4983230072969 + 3 ^ 40 * 669237 * 2
def baseEnd_669237 : Nat := 305458002464980747430881

theorem tailTrace_669237 : CollatzResearch.WordTrace tailWord_669237 prefixEnd_669237 305458002464980747430881 := by
  unfold tailWord_669237
  simp only [CollatzResearch.WordTrace]
  refine ⟨24409078676476120425093965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16272719117650746950062643 24409078676476120425093965)
  ·
    refine ⟨9153404503678545159410237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24409078676476120425093965 9153404503678545159410237)
    ·
      refine ⟨3432526688879454434778839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9153404503678545159410237 3432526688879454434778839)
      ·
        refine ⟨5148790033319181652168259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3432526688879454434778839 5148790033319181652168259)
        ·
          refine ⟨7723185049978772478252389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5148790033319181652168259 7723185049978772478252389)
          ·
            refine ⟨1448097196871019839672323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7723185049978772478252389 1448097196871019839672323)
            ·
              refine ⟨2172145795306529759508485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1448097196871019839672323 2172145795306529759508485)
              ·
                refine ⟨407277336619974329907841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2172145795306529759508485 407277336619974329907841)
                ·
                  refine ⟨305458002464980747430881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 407277336619974329907841 305458002464980747430881)
                  ·
                    rfl

theorem cell20_669237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 4, 1, 4, 2].length) (baseStart_669237 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_669237 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_669237 prefixEnd_669237 := by exact prefixLift 669237
  have htrace : WordTrace (prefixWord ++ tailWord_669237) baseStart_669237 baseEnd_669237 := by
    simpa [prefixWord, tailWord_669237, baseEnd_669237] using wordTrace_append hprefix tailTrace_669237
  have hstable : (prefixWord ++ tailWord_669237).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_669237).length < 2 ^ (prefixWord ++ tailWord_669237).sum := by decide
  have hdescent : baseEnd_669237 < baseStart_669237 := by decide
  rcases family_descends (prefixWord ++ tailWord_669237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_669244 : List Nat := [2, 2, 2, 2, 4, 2, 1, 5]
def baseStart_669244 : Nat := 118140960795 + 669244 * 2 ^ 59
def prefixEnd_669244 : Nat := 4983230072969 + 3 ^ 40 * 669244 * 2
def baseEnd_669244 : Nat := 101820399151906611399173

theorem tailTrace_669244 : CollatzResearch.WordTrace tailWord_669244 prefixEnd_669244 101820399151906611399173 := by
  unfold tailWord_669244
  simp only [CollatzResearch.WordTrace]
  refine ⟨12204666993725380310299393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16272889324967173747065857 12204666993725380310299393)
  ·
    refine ⟨9153500245294035232724545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12204666993725380310299393 9153500245294035232724545)
    ·
      refine ⟨6865125183970526424543409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9153500245294035232724545 6865125183970526424543409)
      ·
        refine ⟨5148843887977894818407557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6865125183970526424543409 5148843887977894818407557)
        ·
          refine ⟨965408228995855278451417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5148843887977894818407557 965408228995855278451417)
          ·
            refine ⟨724056171746891458838563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 965408228995855278451417 724056171746891458838563)
            ·
              refine ⟨1086084257620337188257845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 724056171746891458838563 1086084257620337188257845)
              ·
                refine ⟨101820399151906611399173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1086084257620337188257845 101820399151906611399173)
                ·
                  rfl

theorem cell20_669244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 2, 1, 5].length) (baseStart_669244 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_669244 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_669244 prefixEnd_669244 := by exact prefixLift 669244
  have htrace : WordTrace (prefixWord ++ tailWord_669244) baseStart_669244 baseEnd_669244 := by
    simpa [prefixWord, tailWord_669244, baseEnd_669244] using wordTrace_append hprefix tailTrace_669244
  have hstable : (prefixWord ++ tailWord_669244).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_669244).length < 2 ^ (prefixWord ++ tailWord_669244).sum := by decide
  have hdescent : baseEnd_669244 < baseStart_669244 := by decide
  rcases family_descends (prefixWord ++ tailWord_669244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_669254 : List Nat := [6, 1, 1, 1, 3, 1, 1, 2, 4]
def baseStart_669254 : Nat := 118140960795 + 669254 * 2 ^ 59
def prefixEnd_669254 : Nat := 4983230072969 + 3 ^ 40 * 669254 * 2
def baseEnd_669254 : Nat := 305465761728204243864145

theorem tailTrace_669254 : CollatzResearch.WordTrace tailWord_669254 prefixEnd_669254 305465761728204243864145 := by
  unfold tailWord_669254
  simp only [CollatzResearch.WordTrace]
  refine ⟨762803084919204135264463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 16273132478276354885641877 762803084919204135264463)
  ·
    refine ⟨1144204627378806202896695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 762803084919204135264463 1144204627378806202896695)
    ·
      refine ⟨1716306941068209304345043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1144204627378806202896695 1716306941068209304345043)
      ·
        refine ⟨2574460411602313956517565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1716306941068209304345043 2574460411602313956517565)
        ·
          refine ⟨965422654350867733694087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2574460411602313956517565 965422654350867733694087)
          ·
            refine ⟨1448133981526301600541131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 965422654350867733694087 1448133981526301600541131)
            ·
              refine ⟨2172200972289452400811697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1448133981526301600541131 2172200972289452400811697)
              ·
                refine ⟨1629150729217089300608773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2172200972289452400811697 1629150729217089300608773)
                ·
                  refine ⟨305465761728204243864145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1629150729217089300608773 305465761728204243864145)
                  ·
                    rfl

theorem cell20_669254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 1, 1, 2, 4].length) (baseStart_669254 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_669254 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_669254 prefixEnd_669254 := by exact prefixLift 669254
  have htrace : WordTrace (prefixWord ++ tailWord_669254) baseStart_669254 baseEnd_669254 := by
    simpa [prefixWord, tailWord_669254, baseEnd_669254] using wordTrace_append hprefix tailTrace_669254
  have hstable : (prefixWord ++ tailWord_669254).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_669254).length < 2 ^ (prefixWord ++ tailWord_669254).sum := by decide
  have hdescent : baseEnd_669254 < baseStart_669254 := by decide
  rcases family_descends (prefixWord ++ tailWord_669254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_669261 : List Nat := [1, 6, 1, 1, 3, 1, 3, 4]
def baseStart_669261 : Nat := 118140960795 + 669261 * 2 ^ 59
def prefixEnd_669261 : Nat := 4983230072969 + 3 ^ 40 * 669261 * 2
def baseEnd_669261 : Nat := 101822985572981110210261

theorem tailTrace_669261 : CollatzResearch.WordTrace tailWord_669261 prefixEnd_669261 101822985572981110210261 := by
  unfold tailWord_669261
  simp only [CollatzResearch.WordTrace]
  refine ⟨24409954028389172523967637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16273302685592781682645091 24409954028389172523967637)
  ·
    refine ⟨1144216595080742462060983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 24409954028389172523967637 1144216595080742462060983)
    ·
      refine ⟨1716324892621113693091475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1144216595080742462060983 1716324892621113693091475)
      ·
        refine ⟨2574487338931670539637213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1716324892621113693091475 2574487338931670539637213)
        ·
          refine ⟨965432752099376452363955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2574487338931670539637213 965432752099376452363955)
          ·
            refine ⟨1448149128149064678545933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 965432752099376452363955 1448149128149064678545933)
            ·
              refine ⟨543055923055899254454725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1448149128149064678545933 543055923055899254454725)
              ·
                refine ⟨101822985572981110210261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 543055923055899254454725 101822985572981110210261)
                ·
                  rfl

theorem cell20_669261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 1, 3, 4].length) (baseStart_669261 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_669261 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_669261 prefixEnd_669261 := by exact prefixLift 669261
  have htrace : WordTrace (prefixWord ++ tailWord_669261) baseStart_669261 baseEnd_669261 := by
    simpa [prefixWord, tailWord_669261, baseEnd_669261] using wordTrace_append hprefix tailTrace_669261
  have hstable : (prefixWord ++ tailWord_669261).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_669261).length < 2 ^ (prefixWord ++ tailWord_669261).sum := by decide
  have hdescent : baseEnd_669261 < baseStart_669261 := by decide
  rcases family_descends (prefixWord ++ tailWord_669261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_669265 : List Nat := [1, 2, 2, 1, 3, 2, 5, 4]
def baseStart_669265 : Nat := 118140960795 + 669265 * 2 ^ 59
def prefixEnd_669265 : Nat := 4983230072969 + 3 ^ 40 * 669265 * 2
def baseEnd_669265 : Nat := 101823594142645698165811

theorem tailTrace_669265 : CollatzResearch.WordTrace tailWord_669265 prefixEnd_669265 101823594142645698165811 := by
  unfold tailWord_669265
  simp only [CollatzResearch.WordTrace]
  refine ⟨24410099920374681207113249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16273399946916454138075499 24410099920374681207113249)
  ·
    refine ⟨18307574940281010905334937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24410099920374681207113249 18307574940281010905334937)
    ·
      refine ⟨13730681205210758179001203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18307574940281010905334937 13730681205210758179001203)
      ·
        refine ⟨20596021807816137268501805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13730681205210758179001203 20596021807816137268501805)
        ·
          refine ⟨7723508177931051475688177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20596021807816137268501805 7723508177931051475688177)
          ·
            refine ⟨5792631133448288606766133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7723508177931051475688177 5792631133448288606766133)
            ·
              refine ⟨543059168760777056884325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5792631133448288606766133 543059168760777056884325)
              ·
                refine ⟨101823594142645698165811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 543059168760777056884325 101823594142645698165811)
                ·
                  rfl

theorem cell20_669265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 5, 4].length) (baseStart_669265 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_669265 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_669265 prefixEnd_669265 := by exact prefixLift 669265
  have htrace : WordTrace (prefixWord ++ tailWord_669265) baseStart_669265 baseEnd_669265 := by
    simpa [prefixWord, tailWord_669265, baseEnd_669265] using wordTrace_append hprefix tailTrace_669265
  have hstable : (prefixWord ++ tailWord_669265).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_669265).length < 2 ^ (prefixWord ++ tailWord_669265).sum := by decide
  have hdescent : baseEnd_669265 < baseStart_669265 := by decide
  rcases family_descends (prefixWord ++ tailWord_669265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_669296 : List Nat := [2, 1, 1, 1, 6, 2, 2, 1, 4]
def baseStart_669296 : Nat := 118140960795 + 669296 * 2 ^ 59
def prefixEnd_669296 : Nat := 4983230072969 + 3 ^ 40 * 669296 * 2
def baseEnd_669296 : Nat := 305484931672638764463973

theorem tailTrace_669296 : CollatzResearch.WordTrace tailWord_669296 prefixEnd_669296 305484931672638764463973 := by
  unfold tailWord_669296
  simp only [CollatzResearch.WordTrace]
  refine ⟨12205615291631186750745871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16274153722174915667661161 12205615291631186750745871)
  ·
    refine ⟨18308422937446780126118807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12205615291631186750745871 18308422937446780126118807)
    ·
      refine ⟨27462634406170170189178211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18308422937446780126118807 27462634406170170189178211)
      ·
        refine ⟨41193951609255255283767317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27462634406170170189178211 41193951609255255283767317)
        ·
          refine ⟨1930966481683840091426593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 41193951609255255283767317 1930966481683840091426593)
          ·
            refine ⟨1448224861262880068569945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1930966481683840091426593 1448224861262880068569945)
            ·
              refine ⟨1086168645947160051427459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1448224861262880068569945 1086168645947160051427459)
              ·
                refine ⟨1629252968920740077141189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1086168645947160051427459 1629252968920740077141189)
                ·
                  refine ⟨305484931672638764463973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1629252968920740077141189 305484931672638764463973)
                  ·
                    rfl

theorem cell20_669296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 2, 2, 1, 4].length) (baseStart_669296 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_669296 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_669296 prefixEnd_669296 := by exact prefixLift 669296
  have htrace : WordTrace (prefixWord ++ tailWord_669296) baseStart_669296 baseEnd_669296 := by
    simpa [prefixWord, tailWord_669296, baseEnd_669296] using wordTrace_append hprefix tailTrace_669296
  have hstable : (prefixWord ++ tailWord_669296).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_669296).length < 2 ^ (prefixWord ++ tailWord_669296).sum := by decide
  have hdescent : baseEnd_669296 < baseStart_669296 := by decide
  rcases family_descends (prefixWord ++ tailWord_669296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_669317 : List Nat := [1, 3, 1, 1, 4, 1, 1, 4, 4]
def baseStart_669317 : Nat := 118140960795 + 669317 * 2 ^ 59
def prefixEnd_669317 : Nat := 4983230072969 + 3 ^ 40 * 669317 * 2
def baseEnd_669317 : Nat := 305494516644856024763887

theorem tailTrace_669317 : CollatzResearch.WordTrace tailWord_669317 prefixEnd_669317 305494516644856024763887 := by
  unfold tailWord_669317
  simp only [CollatzResearch.WordTrace]
  refine ⟨24411996516186294088006205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16274664344124196058670803 24411996516186294088006205)
  ·
    refine ⟨9154498693569860283002327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24411996516186294088006205 9154498693569860283002327)
    ·
      refine ⟨13731748040354790424503491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9154498693569860283002327 13731748040354790424503491)
      ·
        refine ⟨20597622060532185636755237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13731748040354790424503491 20597622060532185636755237)
        ·
          refine ⟨3862054136349784806891607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20597622060532185636755237 3862054136349784806891607)
          ·
            refine ⟨5793081204524677210337411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3862054136349784806891607 5793081204524677210337411)
            ·
              refine ⟨8689621806787015815506117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5793081204524677210337411 8689621806787015815506117)
              ·
                refine ⟨1629304088772565465407397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8689621806787015815506117 1629304088772565465407397)
                ·
                  refine ⟨305494516644856024763887, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1629304088772565465407397 305494516644856024763887)
                  ·
                    rfl

theorem cell20_669317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 1, 4, 4].length) (baseStart_669317 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_669317 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_669317 prefixEnd_669317 := by exact prefixLift 669317
  have htrace : WordTrace (prefixWord ++ tailWord_669317) baseStart_669317 baseEnd_669317 := by
    simpa [prefixWord, tailWord_669317, baseEnd_669317] using wordTrace_append hprefix tailTrace_669317
  have hstable : (prefixWord ++ tailWord_669317).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_669317).length < 2 ^ (prefixWord ++ tailWord_669317).sum := by decide
  have hdescent : baseEnd_669317 < baseStart_669317 := by decide
  rcases family_descends (prefixWord ++ tailWord_669317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_669320 : List Nat := [2, 1, 3, 5, 1, 1, 1, 6]
def baseStart_669320 : Nat := 118140960795 + 669320 * 2 ^ 59
def prefixEnd_669320 : Nat := 4983230072969 + 3 ^ 40 * 669320 * 2
def baseEnd_669320 : Nat := 101831961975533782554625

theorem tailTrace_669320 : CollatzResearch.WordTrace tailWord_669320 prefixEnd_669320 101831961975533782554625 := by
  unfold tailWord_669320
  simp only [CollatzResearch.WordTrace]
  refine ⟨12206052967587712800182707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16274737290116950400243609 12206052967587712800182707)
  ·
    refine ⟨18309079451381569200274061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12206052967587712800182707 18309079451381569200274061)
    ·
      refine ⟨6865904794268088450102773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18309079451381569200274061 6865904794268088450102773)
      ·
        refine ⟨643678574462633292197135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 6865904794268088450102773 643678574462633292197135)
        ·
          refine ⟨965517861693949938295703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 643678574462633292197135 965517861693949938295703)
          ·
            refine ⟨1448276792540924907443555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 965517861693949938295703 1448276792540924907443555)
            ·
              refine ⟨2172415188811387361165333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1448276792540924907443555 2172415188811387361165333)
              ·
                refine ⟨101831961975533782554625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2172415188811387361165333 101831961975533782554625)
                ·
                  rfl

theorem cell20_669320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 1, 1, 6].length) (baseStart_669320 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_669320 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_669320 prefixEnd_669320 := by exact prefixLift 669320
  have htrace : WordTrace (prefixWord ++ tailWord_669320) baseStart_669320 baseEnd_669320 := by
    simpa [prefixWord, tailWord_669320, baseEnd_669320] using wordTrace_append hprefix tailTrace_669320
  have hstable : (prefixWord ++ tailWord_669320).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_669320).length < 2 ^ (prefixWord ++ tailWord_669320).sum := by decide
  have hdescent : baseEnd_669320 < baseStart_669320 := by decide
  rcases family_descends (prefixWord ++ tailWord_669320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_669324 : List Nat := [2, 2, 1, 2, 1, 1, 5, 6]
def baseStart_669324 : Nat := 118140960795 + 669324 * 2 ^ 59
def prefixEnd_669324 : Nat := 4983230072969 + 3 ^ 40 * 669324 * 2
def baseEnd_669324 : Nat := 101832570545198370510175

theorem tailTrace_669324 : CollatzResearch.WordTrace tailWord_669324 prefixEnd_669324 101832570545198370510175 := by
  unfold tailWord_669324
  simp only [CollatzResearch.WordTrace]
  refine ⟨12206125913580467141755513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16274834551440622855674017 12206125913580467141755513)
  ·
    refine ⟨9154594435185350356316635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12206125913580467141755513 9154594435185350356316635)
    ·
      refine ⟨13731891652778025534474953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9154594435185350356316635 13731891652778025534474953)
      ·
        refine ⟨10298918739583519150856215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13731891652778025534474953 10298918739583519150856215)
        ·
          refine ⟨15448378109375278726284323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10298918739583519150856215 15448378109375278726284323)
          ·
            refine ⟨23172567164062918089426485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15448378109375278726284323 23172567164062918089426485)
            ·
              refine ⟨2172428171630898570883733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 23172567164062918089426485 2172428171630898570883733)
              ·
                refine ⟨101832570545198370510175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2172428171630898570883733 101832570545198370510175)
                ·
                  rfl

theorem cell20_669324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 5, 6].length) (baseStart_669324 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_669324 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_669324 prefixEnd_669324 := by exact prefixLift 669324
  have htrace : WordTrace (prefixWord ++ tailWord_669324) baseStart_669324 baseEnd_669324 := by
    simpa [prefixWord, tailWord_669324, baseEnd_669324] using wordTrace_append hprefix tailTrace_669324
  have hstable : (prefixWord ++ tailWord_669324).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_669324).length < 2 ^ (prefixWord ++ tailWord_669324).sum := by decide
  have hdescent : baseEnd_669324 < baseStart_669324 := by decide
  rcases family_descends (prefixWord ++ tailWord_669324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_669348 : List Nat := [2, 3, 1, 2, 2, 2, 2, 1, 5]
def baseStart_669348 : Nat := 118140960795 + 669348 * 2 ^ 59
def prefixEnd_669348 : Nat := 4983230072969 + 3 ^ 40 * 669348 * 2
def baseEnd_669348 : Nat := 305508665889557694730427

theorem tailTrace_669348 : CollatzResearch.WordTrace tailWord_669348 prefixEnd_669348 305508665889557694730427 := by
  unfold tailWord_669348
  simp only [CollatzResearch.WordTrace]
  refine ⟨12206563589536993191192349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16275418119382657588256465 12206563589536993191192349)
  ·
    refine ⟨4577461346076372446697131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12206563589536993191192349 4577461346076372446697131)
    ·
      refine ⟨6866192019114558670045697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4577461346076372446697131 6866192019114558670045697)
      ·
        refine ⟨5149644014335919002534273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6866192019114558670045697 5149644014335919002534273)
        ·
          refine ⟨3862233010751939251900705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5149644014335919002534273 3862233010751939251900705)
          ·
            refine ⟨2896674758063954438925529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3862233010751939251900705 2896674758063954438925529)
            ·
              refine ⟨2172506068547965829194147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2896674758063954438925529 2172506068547965829194147)
              ·
                refine ⟨3258759102821948743791221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2172506068547965829194147 3258759102821948743791221)
                ·
                  refine ⟨305508665889557694730427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3258759102821948743791221 305508665889557694730427)
                  ·
                    rfl

theorem cell20_669348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 2, 1, 5].length) (baseStart_669348 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_669348 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_669348 prefixEnd_669348 := by exact prefixLift 669348
  have htrace : WordTrace (prefixWord ++ tailWord_669348) baseStart_669348 baseEnd_669348 := by
    simpa [prefixWord, tailWord_669348, baseEnd_669348] using wordTrace_append hprefix tailTrace_669348
  have hstable : (prefixWord ++ tailWord_669348).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_669348).length < 2 ^ (prefixWord ++ tailWord_669348).sum := by decide
  have hdescent : baseEnd_669348 < baseStart_669348 := by decide
  rcases family_descends (prefixWord ++ tailWord_669348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_669362 : List Nat := [3, 2, 1, 1, 1, 2, 3, 7]
def baseStart_669362 : Nat := 118140960795 + 669362 * 2 ^ 59
def prefixEnd_669362 : Nat := 4983230072969 + 3 ^ 40 * 669362 * 2
def baseEnd_669362 : Nat := 101838351957011956087901

theorem tailTrace_669362 : CollatzResearch.WordTrace tailWord_669362 prefixEnd_669362 101838351957011956087901 := by
  unfold tailWord_669362
  simp only [CollatzResearch.WordTrace]
  refine ⟨6103409450255816693348585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16275758534015511182262893 6103409450255816693348585)
  ·
    refine ⟨4577557087691862520011439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6103409450255816693348585 4577557087691862520011439)
    ·
      refine ⟨6866335631537793780017159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4577557087691862520011439 6866335631537793780017159)
      ·
        refine ⟨10299503447306690670025739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6866335631537793780017159 10299503447306690670025739)
        ·
          refine ⟨15449255170960036005038609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10299503447306690670025739 15449255170960036005038609)
          ·
            refine ⟨11586941378220027003778957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15449255170960036005038609 11586941378220027003778957)
            ·
              refine ⟨4345103016832510126417109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11586941378220027003778957 4345103016832510126417109)
              ·
                refine ⟨101838351957011956087901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4345103016832510126417109 101838351957011956087901)
                ·
                  rfl

theorem cell20_669362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 3, 7].length) (baseStart_669362 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_669362 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_669362 prefixEnd_669362 := by exact prefixLift 669362
  have htrace : WordTrace (prefixWord ++ tailWord_669362) baseStart_669362 baseEnd_669362 := by
    simpa [prefixWord, tailWord_669362, baseEnd_669362] using wordTrace_append hprefix tailTrace_669362
  have hstable : (prefixWord ++ tailWord_669362).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_669362).length < 2 ^ (prefixWord ++ tailWord_669362).sum := by decide
  have hdescent : baseEnd_669362 < baseStart_669362 := by decide
  rcases family_descends (prefixWord ++ tailWord_669362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_669458 : List Nat := [3, 2, 4, 1, 1, 1, 3, 2, 3]
def baseStart_669458 : Nat := 118140960795 + 669458 * 2 ^ 59
def prefixEnd_669458 : Nat := 4983230072969 + 3 ^ 40 * 669458 * 2
def baseEnd_669458 : Nat := 305558872886886201063311

theorem tailTrace_669458 : CollatzResearch.WordTrace tailWord_669458 prefixEnd_669458 305558872886886201063311 := by
  unfold tailWord_669458
  simp only [CollatzResearch.WordTrace]
  refine ⟨6104284802168868792222257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16278092805783650112592685 6104284802168868792222257)
  ·
    refine ⟨4578213601626651594166693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6104284802168868792222257 4578213601626651594166693)
    ·
      refine ⟨858415050304997173906255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4578213601626651594166693 858415050304997173906255)
      ·
        refine ⟨1287622575457495760859383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 858415050304997173906255 1287622575457495760859383)
        ·
          refine ⟨1931433863186243641289075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1287622575457495760859383 1931433863186243641289075)
          ·
            refine ⟨2897150794779365461933613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1931433863186243641289075 2897150794779365461933613)
            ·
              refine ⟨1086431548042262048225105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2897150794779365461933613 1086431548042262048225105)
              ·
                refine ⟨814823661031696536168829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1086431548042262048225105 814823661031696536168829)
                ·
                  refine ⟨305558872886886201063311, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 814823661031696536168829 305558872886886201063311)
                  ·
                    rfl

theorem cell20_669458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 3, 2, 3].length) (baseStart_669458 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_669458 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_669458 prefixEnd_669458 := by exact prefixLift 669458
  have htrace : WordTrace (prefixWord ++ tailWord_669458) baseStart_669458 baseEnd_669458 := by
    simpa [prefixWord, tailWord_669458, baseEnd_669458] using wordTrace_append hprefix tailTrace_669458
  have hstable : (prefixWord ++ tailWord_669458).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_669458).length < 2 ^ (prefixWord ++ tailWord_669458).sum := by decide
  have hdescent : baseEnd_669458 < baseStart_669458 := by decide
  rcases family_descends (prefixWord ++ tailWord_669458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_669493 : List Nat := [1, 3, 3, 1, 4, 1, 1, 6]
def baseStart_669493 : Nat := 118140960795 + 669493 * 2 ^ 59
def prefixEnd_669493 : Nat := 4983230072969 + 3 ^ 40 * 669493 * 2
def baseEnd_669493 : Nat := 101858282613527211632167

theorem tailTrace_669493 : CollatzResearch.WordTrace tailWord_669493 prefixEnd_669493 101858282613527211632167 := by
  unfold tailWord_669493
  simp only [CollatzResearch.WordTrace]
  refine ⟨24418415763548676146413133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16278943842365784097608755 24418415763548676146413133)
  ·
    refine ⟨9156905911330753554904925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24418415763548676146413133 9156905911330753554904925)
    ·
      refine ⟨3433839716749032583089347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9156905911330753554904925 3433839716749032583089347)
      ·
        refine ⟨5150759575123548874634021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3433839716749032583089347 5150759575123548874634021)
        ·
          refine ⟨965767420335665413993879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5150759575123548874634021 965767420335665413993879)
          ·
            refine ⟨1448651130503498120990819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 965767420335665413993879 1448651130503498120990819)
            ·
              refine ⟨2172976695755247181486229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1448651130503498120990819 2172976695755247181486229)
              ·
                refine ⟨101858282613527211632167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2172976695755247181486229 101858282613527211632167)
                ·
                  rfl

theorem cell20_669493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 1, 1, 6].length) (baseStart_669493 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_669493 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_669493 prefixEnd_669493 := by exact prefixLift 669493
  have htrace : WordTrace (prefixWord ++ tailWord_669493) baseStart_669493 baseEnd_669493 := by
    simpa [prefixWord, tailWord_669493, baseEnd_669493] using wordTrace_append hprefix tailTrace_669493
  have hstable : (prefixWord ++ tailWord_669493).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_669493).length < 2 ^ (prefixWord ++ tailWord_669493).sum := by decide
  have hdescent : baseEnd_669493 < baseStart_669493 := by decide
  rcases family_descends (prefixWord ++ tailWord_669493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_669510 : List Nat := [6, 1, 1, 2, 1, 1, 8]
def baseStart_669510 : Nat := 118140960795 + 669510 * 2 ^ 59
def prefixEnd_669510 : Nat := 4983230072969 + 3 ^ 40 * 669510 * 2
def baseEnd_669510 : Nat := 33953623011533903481085

theorem tailTrace_669510 : CollatzResearch.WordTrace tailWord_669510 prefixEnd_669510 33953623011533903481085 := by
  unfold tailWord_669510
  simp only [CollatzResearch.WordTrace]
  refine ⟨763094868890221501555687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 16279357202991392033187989 763094868890221501555687)
  ·
    refine ⟨1144642303335332252333531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 763094868890221501555687 1144642303335332252333531)
    ·
      refine ⟨1716963455002998378500297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1144642303335332252333531 1716963455002998378500297)
      ·
        refine ⟨1287722591252248783875223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1716963455002998378500297 1287722591252248783875223)
        ·
          refine ⟨1931583886878373175812835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1287722591252248783875223 1931583886878373175812835)
          ·
            refine ⟨2897375830317559763719253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1931583886878373175812835 2897375830317559763719253)
            ·
              refine ⟨33953623011533903481085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2897375830317559763719253 33953623011533903481085)
              ·
                rfl

theorem cell20_669510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 8].length) (baseStart_669510 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_669510 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_669510 prefixEnd_669510 := by exact prefixLift 669510
  have htrace : WordTrace (prefixWord ++ tailWord_669510) baseStart_669510 baseEnd_669510 := by
    simpa [prefixWord, tailWord_669510, baseEnd_669510] using wordTrace_append hprefix tailTrace_669510
  have hstable : (prefixWord ++ tailWord_669510).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_669510).length < 2 ^ (prefixWord ++ tailWord_669510).sum := by decide
  have hdescent : baseEnd_669510 < baseStart_669510 := by decide
  rcases family_descends (prefixWord ++ tailWord_669510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_669517 : List Nat := [1, 6, 1, 2, 1, 1, 2, 1, 5]
def baseStart_669517 : Nat := 118140960795 + 669517 * 2 ^ 59
def prefixEnd_669517 : Nat := 4983230072969 + 3 ^ 40 * 669517 * 2
def baseEnd_669517 : Nat := 305585802094544218096403

theorem tailTrace_669517 : CollatzResearch.WordTrace tailWord_669517 prefixEnd_669517 305585802094544218096403 := by
  unfold tailWord_669517
  simp only [CollatzResearch.WordTrace]
  refine ⟨24419291115461728245286805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16279527410307818830191203 24419291115461728245286805)
  ·
    refine ⟨1144654271037268511497819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 24419291115461728245286805 1144654271037268511497819)
    ·
      refine ⟨1716981406555902767246729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1144654271037268511497819 1716981406555902767246729)
      ·
        refine ⟨1287736054916927075435047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1716981406555902767246729 1287736054916927075435047)
        ·
          refine ⟨1931604082375390613152571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1287736054916927075435047 1931604082375390613152571)
          ·
            refine ⟨2897406123563085919728857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1931604082375390613152571 2897406123563085919728857)
            ·
              refine ⟨2173054592672314439796643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2897406123563085919728857 2173054592672314439796643)
              ·
                refine ⟨3259581889008471659694965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2173054592672314439796643 3259581889008471659694965)
                ·
                  refine ⟨305585802094544218096403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3259581889008471659694965 305585802094544218096403)
                  ·
                    rfl

theorem cell20_669517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 2, 1, 5].length) (baseStart_669517 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_669517 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_669517 prefixEnd_669517 := by exact prefixLift 669517
  have htrace : WordTrace (prefixWord ++ tailWord_669517) baseStart_669517 baseEnd_669517 := by
    simpa [prefixWord, tailWord_669517, baseEnd_669517] using wordTrace_append hprefix tailTrace_669517
  have hstable : (prefixWord ++ tailWord_669517).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_669517).length < 2 ^ (prefixWord ++ tailWord_669517).sum := by decide
  have hdescent : baseEnd_669517 < baseStart_669517 := by decide
  rcases family_descends (prefixWord ++ tailWord_669517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_669524 : List Nat := [2, 4, 1, 1, 3, 1, 3, 1, 4]
def baseStart_669524 : Nat := 118140960795 + 669524 * 2 ^ 59
def prefixEnd_669524 : Nat := 4983230072969 + 3 ^ 40 * 669524 * 2
def baseEnd_669524 : Nat := 305588997085283304863041

theorem tailTrace_669524 : CollatzResearch.WordTrace tailWord_669524 prefixEnd_669524 305588997085283304863041 := by
  unfold tailWord_669524
  simp only [CollatzResearch.WordTrace]
  refine ⟨12209773213218184220395813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16279697617624245627194417 12209773213218184220395813)
  ·
    refine ⟨2289332477478409541324215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12209773213218184220395813 2289332477478409541324215)
    ·
      refine ⟨3433998716217614311986323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2289332477478409541324215 3433998716217614311986323)
      ·
        refine ⟨5150998074326421467979485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3433998716217614311986323 5150998074326421467979485)
        ·
          refine ⟨1931624277872408050492307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5150998074326421467979485 1931624277872408050492307)
          ·
            refine ⟨2897436416808612075738461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1931624277872408050492307 2897436416808612075738461)
            ·
              refine ⟨1086538656303229528401923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2897436416808612075738461 1086538656303229528401923)
              ·
                refine ⟨1629807984454844292602885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1086538656303229528401923 1629807984454844292602885)
                ·
                  refine ⟨305588997085283304863041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1629807984454844292602885 305588997085283304863041)
                  ·
                    rfl

theorem cell20_669524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 3, 1, 4].length) (baseStart_669524 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_669524 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_669524 prefixEnd_669524 := by exact prefixLift 669524
  have htrace : WordTrace (prefixWord ++ tailWord_669524) baseStart_669524 baseEnd_669524 := by
    simpa [prefixWord, tailWord_669524, baseEnd_669524] using wordTrace_append hprefix tailTrace_669524
  have hstable : (prefixWord ++ tailWord_669524).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_669524).length < 2 ^ (prefixWord ++ tailWord_669524).sum := by decide
  have hdescent : baseEnd_669524 < baseStart_669524 := by decide
  rcases family_descends (prefixWord ++ tailWord_669524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_669569 : List Nat := [1, 2, 4, 4, 1, 8]
def baseStart_669569 : Nat := 118140960795 + 669569 * 2 ^ 59
def prefixEnd_669569 : Nat := 4983230072969 + 3 ^ 40 * 669569 * 2
def baseEnd_669569 : Nat := 11318871715239375865291

theorem tailTrace_669569 : CollatzResearch.WordTrace tailWord_669569 prefixEnd_669569 11318871715239375865291 := by
  unfold tailWord_669569
  simp only [CollatzResearch.WordTrace]
  refine ⟨24421187711273341126179761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16280791807515560750786507 24421187711273341126179761)
  ·
    refine ⟨18315890783455005844634821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24421187711273341126179761 18315890783455005844634821)
    ·
      refine ⟨3434229521897813595869029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18315890783455005844634821 3434229521897813595869029)
      ·
        refine ⟨643918035355840049225443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3434229521897813595869029 643918035355840049225443)
        ·
          refine ⟨965877053033760073838165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 643918035355840049225443 965877053033760073838165)
          ·
            refine ⟨11318871715239375865291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 965877053033760073838165 11318871715239375865291)
            ·
              rfl

theorem cell20_669569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 8].length) (baseStart_669569 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_669569 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_669569 prefixEnd_669569 := by exact prefixLift 669569
  have htrace : WordTrace (prefixWord ++ tailWord_669569) baseStart_669569 baseEnd_669569 := by
    simpa [prefixWord, tailWord_669569, baseEnd_669569] using wordTrace_append hprefix tailTrace_669569
  have hstable : (prefixWord ++ tailWord_669569).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_669569).length < 2 ^ (prefixWord ++ tailWord_669569).sum := by decide
  have hdescent : baseEnd_669569 < baseStart_669569 := by decide
  rcases family_descends (prefixWord ++ tailWord_669569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_669575 : List Nat := [1, 1, 4, 2, 5, 1, 2, 2, 2]
def baseStart_669575 : Nat := 118140960795 + 669575 * 2 ^ 59
def prefixEnd_669575 : Nat := 4983230072969 + 3 ^ 40 * 669575 * 2
def baseEnd_669575 : Nat := 305612274874953794162833

theorem tailTrace_669575 : CollatzResearch.WordTrace tailWord_669575 prefixEnd_669575 305612274874953794162833 := by
  unfold tailWord_669575
  simp only [CollatzResearch.WordTrace]
  refine ⟨24421406549251604150898179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16280937699501069433932119 24421406549251604150898179)
  ·
    refine ⟨36632109823877406226347269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24421406549251604150898179 36632109823877406226347269)
    ·
      refine ⟨6868520591977013667440113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 36632109823877406226347269 6868520591977013667440113)
      ·
        refine ⟨5151390443982760250580085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6868520591977013667440113 5151390443982760250580085)
        ·
          refine ⟨482942854123383773491883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 5151390443982760250580085 482942854123383773491883)
          ·
            refine ⟨724414281185075660237825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 482942854123383773491883 724414281185075660237825)
            ·
              refine ⟨543310710888806745178369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 724414281185075660237825 543310710888806745178369)
              ·
                refine ⟨407483033166605058883777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 543310710888806745178369 407483033166605058883777)
                ·
                  refine ⟨305612274874953794162833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 407483033166605058883777 305612274874953794162833)
                  ·
                    rfl

theorem cell20_669575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 5, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 5, 1, 2, 2, 2].length) (baseStart_669575 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_669575 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_669575 prefixEnd_669575 := by exact prefixLift 669575
  have htrace : WordTrace (prefixWord ++ tailWord_669575) baseStart_669575 baseEnd_669575 := by
    simpa [prefixWord, tailWord_669575, baseEnd_669575] using wordTrace_append hprefix tailTrace_669575
  have hstable : (prefixWord ++ tailWord_669575).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_669575).length < 2 ^ (prefixWord ++ tailWord_669575).sum := by decide
  have hdescent : baseEnd_669575 < baseStart_669575 := by decide
  rcases family_descends (prefixWord ++ tailWord_669575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_669586 : List Nat := [3, 2, 3, 2, 1, 3, 1, 5]
def baseStart_669586 : Nat := 118140960795 + 669586 * 2 ^ 59
def prefixEnd_669586 : Nat := 4983230072969 + 3 ^ 40 * 669586 * 2
def baseEnd_669586 : Nat := 101872431858228881598707

theorem tailTrace_669586 : CollatzResearch.WordTrace tailWord_669586 prefixEnd_669586 101872431858228881598707 := by
  unfold tailWord_669586
  simp only [CollatzResearch.WordTrace]
  refine ⟨6105451938052938257387153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16281205168141168686365741 6105451938052938257387153)
  ·
    refine ⟨4579088953539703693040365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6105451938052938257387153 4579088953539703693040365)
    ·
      refine ⟨1717158357577388884890137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4579088953539703693040365 1717158357577388884890137)
      ·
        refine ⟨1287868768183041663667603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1717158357577388884890137 1287868768183041663667603)
        ·
          refine ⟨1931803152274562495501405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1287868768183041663667603 1931803152274562495501405)
          ·
            refine ⟨724426182102960935813027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1931803152274562495501405 724426182102960935813027)
            ·
              refine ⟨1086639273154441403719541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 724426182102960935813027 1086639273154441403719541)
              ·
                refine ⟨101872431858228881598707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1086639273154441403719541 101872431858228881598707)
                ·
                  rfl

theorem cell20_669586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 3, 1, 5].length) (baseStart_669586 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_669586 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_669586 prefixEnd_669586 := by exact prefixLift 669586
  have htrace : WordTrace (prefixWord ++ tailWord_669586) baseStart_669586 baseEnd_669586 := by
    simpa [prefixWord, tailWord_669586, baseEnd_669586] using wordTrace_append hprefix tailTrace_669586
  have hstable : (prefixWord ++ tailWord_669586).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_669586).length < 2 ^ (prefixWord ++ tailWord_669586).sum := by decide
  have hdescent : baseEnd_669586 < baseStart_669586 := by decide
  rcases family_descends (prefixWord ++ tailWord_669586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_669617 : List Nat := [1, 2, 2, 4, 2, 2, 2, 3, 2]
def baseStart_669617 : Nat := 118140960795 + 669617 * 2 ^ 59
def prefixEnd_669617 : Nat := 4983230072969 + 3 ^ 40 * 669617 * 2
def baseEnd_669617 : Nat := 305631444819388314762661

theorem tailTrace_669617 : CollatzResearch.WordTrace tailWord_669617 prefixEnd_669617 305631444819388314762661 := by
  unfold tailWord_669617
  simp only [CollatzResearch.WordTrace]
  refine ⟨24422938415099445323927105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16281958943399630215951403 24422938415099445323927105)
  ·
    refine ⟨18317203811324583992945329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24422938415099445323927105 18317203811324583992945329)
    ·
      refine ⟨13737902858493437994708997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18317203811324583992945329 13737902858493437994708997)
      ·
        refine ⟨2575856785967519624007937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13737902858493437994708997 2575856785967519624007937)
        ·
          refine ⟨1931892589475639718005953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2575856785967519624007937 1931892589475639718005953)
          ·
            refine ⟨1448919442106729788504465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1931892589475639718005953 1448919442106729788504465)
            ·
              refine ⟨1086689581580047341378349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1448919442106729788504465 1086689581580047341378349)
              ·
                refine ⟨407508593092517753016881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1086689581580047341378349 407508593092517753016881)
                ·
                  refine ⟨305631444819388314762661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 407508593092517753016881 305631444819388314762661)
                  ·
                    rfl

theorem cell20_669617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 2, 2, 3, 2].length) (baseStart_669617 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_669617 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_669617 prefixEnd_669617 := by exact prefixLift 669617
  have htrace : WordTrace (prefixWord ++ tailWord_669617) baseStart_669617 baseEnd_669617 := by
    simpa [prefixWord, tailWord_669617, baseEnd_669617] using wordTrace_append hprefix tailTrace_669617
  have hstable : (prefixWord ++ tailWord_669617).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_669617).length < 2 ^ (prefixWord ++ tailWord_669617).sum := by decide
  have hdescent : baseEnd_669617 < baseStart_669617 := by decide
  rcases family_descends (prefixWord ++ tailWord_669617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_669680 : List Nat := [2, 1, 1, 1, 3, 2, 2, 2, 6]
def baseStart_669680 : Nat := 118140960795 + 669680 * 2 ^ 59
def prefixEnd_669680 : Nat := 4983230072969 + 3 ^ 40 * 669680 * 2
def baseEnd_669680 : Nat := 305660199736040095662403

theorem tailTrace_669680 : CollatzResearch.WordTrace tailWord_669680 prefixEnd_669680 305660199736040095662403 := by
  unfold tailWord_669680
  simp only [CollatzResearch.WordTrace]
  refine ⟨12212618106935603541735247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16283490809247471388980329 12212618106935603541735247)
  ·
    refine ⟨18318927160403405312602871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12212618106935603541735247 18318927160403405312602871)
    ·
      refine ⟨27478390740605107968904307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18318927160403405312602871 27478390740605107968904307)
      ·
        refine ⟨41217586110907661953356461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27478390740605107968904307 41217586110907661953356461)
        ·
          refine ⟨15456594791590373232508673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41217586110907661953356461 15456594791590373232508673)
          ·
            refine ⟨11592446093692779924381505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15456594791590373232508673 11592446093692779924381505)
            ·
              refine ⟨8694334570269584943286129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11592446093692779924381505 8694334570269584943286129)
              ·
                refine ⟨6520750927702188707464597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8694334570269584943286129 6520750927702188707464597)
                ·
                  refine ⟨305660199736040095662403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6520750927702188707464597 305660199736040095662403)
                  ·
                    rfl

theorem cell20_669680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 2, 2, 6].length) (baseStart_669680 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_669680 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_669680 prefixEnd_669680 := by exact prefixLift 669680
  have htrace : WordTrace (prefixWord ++ tailWord_669680) baseStart_669680 baseEnd_669680 := by
    simpa [prefixWord, tailWord_669680, baseEnd_669680] using wordTrace_append hprefix tailTrace_669680
  have hstable : (prefixWord ++ tailWord_669680).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_669680).length < 2 ^ (prefixWord ++ tailWord_669680).sum := by decide
  have hdescent : baseEnd_669680 < baseStart_669680 := by decide
  rcases family_descends (prefixWord ++ tailWord_669680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_669700 : List Nat := [2, 3, 2, 4, 1, 1, 2, 5]
def baseStart_669700 : Nat := 118140960795 + 669700 * 2 ^ 59
def prefixEnd_669700 : Nat := 4983230072969 + 3 ^ 40 * 669700 * 2
def baseEnd_669700 : Nat := 101889776093669638331885

theorem tailTrace_669700 : CollatzResearch.WordTrace tailWord_669700 prefixEnd_669700 101889776093669638331885 := by
  unfold tailWord_669700
  simp only [CollatzResearch.WordTrace]
  refine ⟨12212982836899375249599277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16283977115865833666132369 12212982836899375249599277)
  ·
    refine ⟨4579868563837265718599729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12212982836899375249599277 4579868563837265718599729)
    ·
      refine ⟨3434901422877949288949797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4579868563837265718599729 3434901422877949288949797)
      ·
        refine ⟨644044016789615491678087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3434901422877949288949797 644044016789615491678087)
        ·
          refine ⟨966066025184423237517131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 644044016789615491678087 966066025184423237517131)
          ·
            refine ⟨1449099037776634856275697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 966066025184423237517131 1449099037776634856275697)
            ·
              refine ⟨1086824278332476142206773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1449099037776634856275697 1086824278332476142206773)
              ·
                refine ⟨101889776093669638331885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1086824278332476142206773 101889776093669638331885)
                ·
                  rfl

theorem cell20_669700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 1, 2, 5].length) (baseStart_669700 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_669700 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_669700 prefixEnd_669700 := by exact prefixLift 669700
  have htrace : WordTrace (prefixWord ++ tailWord_669700) baseStart_669700 baseEnd_669700 := by
    simpa [prefixWord, tailWord_669700, baseEnd_669700] using wordTrace_append hprefix tailTrace_669700
  have hstable : (prefixWord ++ tailWord_669700).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_669700).length < 2 ^ (prefixWord ++ tailWord_669700).sum := by decide
  have hdescent : baseEnd_669700 < baseStart_669700 := by decide
  rcases family_descends (prefixWord ++ tailWord_669700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_669704 : List Nat := [2, 1, 3, 2, 1, 2, 4, 5]
def baseStart_669704 : Nat := 118140960795 + 669704 * 2 ^ 59
def prefixEnd_669704 : Nat := 4983230072969 + 3 ^ 40 * 669704 * 2
def baseEnd_669704 : Nat := 101890384663334226287435

theorem tailTrace_669704 : CollatzResearch.WordTrace tailWord_669704 prefixEnd_669704 101890384663334226287435 := by
  unfold tailWord_669704
  simp only [CollatzResearch.WordTrace]
  refine ⟨12213055782892129591172083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16284074377189506121562777 12213055782892129591172083)
  ·
    refine ⟨18319583674338194386758125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12213055782892129591172083 18319583674338194386758125)
    ·
      refine ⟨6869843877876822895034297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18319583674338194386758125 6869843877876822895034297)
      ·
        refine ⟨5152382908407617171275723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6869843877876822895034297 5152382908407617171275723)
        ·
          refine ⟨7728574362611425756913585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5152382908407617171275723 7728574362611425756913585)
          ·
            refine ⟨5796430771958569317685189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7728574362611425756913585 5796430771958569317685189)
            ·
              refine ⟨1086830769742231747065973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5796430771958569317685189 1086830769742231747065973)
              ·
                refine ⟨101890384663334226287435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1086830769742231747065973 101890384663334226287435)
                ·
                  rfl

theorem cell20_669704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 4, 5].length) (baseStart_669704 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_669704 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_669704 prefixEnd_669704 := by exact prefixLift 669704
  have htrace : WordTrace (prefixWord ++ tailWord_669704) baseStart_669704 baseEnd_669704 := by
    simpa [prefixWord, tailWord_669704, baseEnd_669704] using wordTrace_append hprefix tailTrace_669704
  have hstable : (prefixWord ++ tailWord_669704).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_669704).length < 2 ^ (prefixWord ++ tailWord_669704).sum := by decide
  have hdescent : baseEnd_669704 < baseStart_669704 := by decide
  rcases family_descends (prefixWord ++ tailWord_669704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_669742 : List Nat := [4, 1, 3, 1, 1, 10]
def baseStart_669742 : Nat := 118140960795 + 669742 * 2 ^ 59
def prefixEnd_669742 : Nat := 4983230072969 + 3 ^ 40 * 669742 * 2
def baseEnd_669742 : Nat := 11321796230571979096129

theorem tailTrace_669742 : CollatzResearch.WordTrace tailWord_669742 prefixEnd_669742 11321796230571979096129 := by
  unfold tailWord_669742
  simp only [CollatzResearch.WordTrace]
  refine ⟨3053437192455823959028435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16284998359764394448151653 3053437192455823959028435)
  ·
    refine ⟨4580155788683735938542653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3053437192455823959028435 4580155788683735938542653)
    ·
      refine ⟨1717558420756400976953495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4580155788683735938542653 1717558420756400976953495)
      ·
        refine ⟨2576337631134601465430243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1717558420756400976953495 2576337631134601465430243)
        ·
          refine ⟨3864506446701902198145365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2576337631134601465430243 3864506446701902198145365)
          ·
            refine ⟨11321796230571979096129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 3864506446701902198145365 11321796230571979096129)
            ·
              rfl

theorem cell20_669742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 10].length) (baseStart_669742 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_669742 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_669742 prefixEnd_669742 := by exact prefixLift 669742
  have htrace : WordTrace (prefixWord ++ tailWord_669742) baseStart_669742 baseEnd_669742 := by
    simpa [prefixWord, tailWord_669742, baseEnd_669742] using wordTrace_append hprefix tailTrace_669742
  have hstable : (prefixWord ++ tailWord_669742).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_669742).length < 2 ^ (prefixWord ++ tailWord_669742).sum := by decide
  have hdescent : baseEnd_669742 < baseStart_669742 := by decide
  rcases family_descends (prefixWord ++ tailWord_669742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_669748 : List Nat := [2, 5, 1, 2, 2, 1, 1, 4, 2]
def baseStart_669748 : Nat := 118140960795 + 669748 * 2 ^ 59
def prefixEnd_669748 : Nat := 4983230072969 + 3 ^ 40 * 669748 * 2
def baseEnd_669748 : Nat := 305691236788934081395459

theorem tailTrace_669748 : CollatzResearch.WordTrace tailWord_669748 prefixEnd_669748 305691236788934081395459 := by
  unfold tailWord_669748
  simp only [CollatzResearch.WordTrace]
  refine ⟨12213858188812427348472949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16285144251749903131297265 12213858188812427348472949)
  ·
    refine ⟨1145049205201165063919339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 12213858188812427348472949 1145049205201165063919339)
    ·
      refine ⟨1717573807801747595879009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1145049205201165063919339 1717573807801747595879009)
      ·
        refine ⟨1288180355851310696909257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1717573807801747595879009 1288180355851310696909257)
        ·
          refine ⟨966135266888483022681943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1288180355851310696909257 966135266888483022681943)
          ·
            refine ⟨1449202900332724534022915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 966135266888483022681943 1449202900332724534022915)
            ·
              refine ⟨2173804350499086801034373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1449202900332724534022915 2173804350499086801034373)
              ·
                refine ⟨407588315718578775193945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2173804350499086801034373 407588315718578775193945)
                ·
                  refine ⟨305691236788934081395459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 407588315718578775193945 305691236788934081395459)
                  ·
                    rfl

theorem cell20_669748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 1, 1, 4, 2].length) (baseStart_669748 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_669748 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_669748 prefixEnd_669748 := by exact prefixLift 669748
  have htrace : WordTrace (prefixWord ++ tailWord_669748) baseStart_669748 baseEnd_669748 := by
    simpa [prefixWord, tailWord_669748, baseEnd_669748] using wordTrace_append hprefix tailTrace_669748
  have hstable : (prefixWord ++ tailWord_669748).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_669748).length < 2 ^ (prefixWord ++ tailWord_669748).sum := by decide
  have hdescent : baseEnd_669748 < baseStart_669748 := by decide
  rcases family_descends (prefixWord ++ tailWord_669748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_669749 : List Nat := [1, 3, 3, 1, 1, 1, 2, 3, 5]
def baseStart_669749 : Nat := 118140960795 + 669749 * 2 ^ 59
def prefixEnd_669749 : Nat := 4983230072969 + 3 ^ 40 * 669749 * 2
def baseEnd_669749 : Nat := 305691693216182522362121

theorem tailTrace_669749 : CollatzResearch.WordTrace tailWord_669749 prefixEnd_669749 305691693216182522362121 := by
  unfold tailWord_669749
  simp only [CollatzResearch.WordTrace]
  refine ⟨24427752850621231867732301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16285168567080821245154867 24427752850621231867732301)
  ·
    refine ⟨9160407318982961950399613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24427752850621231867732301 9160407318982961950399613)
    ·
      refine ⟨3435152744618610731399855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9160407318982961950399613 3435152744618610731399855)
      ·
        refine ⟨5152729116927916097099783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3435152744618610731399855 5152729116927916097099783)
        ·
          refine ⟨7729093675391874145649675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5152729116927916097099783 7729093675391874145649675)
          ·
            refine ⟨11593640513087811218474513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7729093675391874145649675 11593640513087811218474513)
            ·
              refine ⟨8695230384815858413855885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11593640513087811218474513 8695230384815858413855885)
              ·
                refine ⟨3260711394305946905195957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8695230384815858413855885 3260711394305946905195957)
                ·
                  refine ⟨305691693216182522362121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3260711394305946905195957 305691693216182522362121)
                  ·
                    rfl

theorem cell20_669749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 2, 3, 5].length) (baseStart_669749 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_669749 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_669749 prefixEnd_669749 := by exact prefixLift 669749
  have htrace : WordTrace (prefixWord ++ tailWord_669749) baseStart_669749 baseEnd_669749 := by
    simpa [prefixWord, tailWord_669749, baseEnd_669749] using wordTrace_append hprefix tailTrace_669749
  have hstable : (prefixWord ++ tailWord_669749).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_669749).length < 2 ^ (prefixWord ++ tailWord_669749).sum := by decide
  have hdescent : baseEnd_669749 < baseStart_669749 := by decide
  rcases family_descends (prefixWord ++ tailWord_669749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_669763 : List Nat := [1, 1, 1, 3, 1, 2, 2, 9]
def baseStart_669763 : Nat := 118140960795 + 669763 * 2 ^ 59
def prefixEnd_669763 : Nat := 4983230072969 + 3 ^ 40 * 669763 * 2
def baseEnd_669763 : Nat := 101899361065886898631799

theorem tailTrace_669763 : CollatzResearch.WordTrace tailWord_669763 prefixEnd_669763 101899361065886898631799 := by
  unfold tailWord_669763
  simp only [CollatzResearch.WordTrace]
  refine ⟨24428263472570512258741943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16285508981713674839161295 24428263472570512258741943)
  ·
    refine ⟨36642395208855768388112915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24428263472570512258741943 36642395208855768388112915)
    ·
      refine ⟨54963592813283652582169373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36642395208855768388112915 54963592813283652582169373)
      ·
        refine ⟨20611347304981369718313515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 54963592813283652582169373 20611347304981369718313515)
        ·
          refine ⟨30917020957472054577470273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20611347304981369718313515 30917020957472054577470273)
          ·
            refine ⟨23187765718104040933102705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30917020957472054577470273 23187765718104040933102705)
            ·
              refine ⟨17390824288578030699827029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23187765718104040933102705 17390824288578030699827029)
              ·
                refine ⟨101899361065886898631799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 17390824288578030699827029 101899361065886898631799)
                ·
                  rfl

theorem cell20_669763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 9].length) (baseStart_669763 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_669763 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_669763 prefixEnd_669763 := by exact prefixLift 669763
  have htrace : WordTrace (prefixWord ++ tailWord_669763) baseStart_669763 baseEnd_669763 := by
    simpa [prefixWord, tailWord_669763, baseEnd_669763] using wordTrace_append hprefix tailTrace_669763
  have hstable : (prefixWord ++ tailWord_669763).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_669763).length < 2 ^ (prefixWord ++ tailWord_669763).sum := by decide
  have hdescent : baseEnd_669763 < baseStart_669763 := by decide
  rcases family_descends (prefixWord ++ tailWord_669763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_669801 : List Nat := [1, 2, 1, 1, 1, 5, 9]
def baseStart_669801 : Nat := 118140960795 + 669801 * 2 ^ 59
def prefixEnd_669801 : Nat := 4983230072969 + 3 ^ 40 * 669801 * 2
def baseEnd_669801 : Nat := 33968380825900161403175

theorem tailTrace_669801 : CollatzResearch.WordTrace tailWord_669801 prefixEnd_669801 33968380825900161403175 := by
  unfold tailWord_669801
  simp only [CollatzResearch.WordTrace]
  refine ⟨24429649446432844748625257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16286432964288563165750171 24429649446432844748625257)
  ·
    refine ⟨18322237084824633561468943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24429649446432844748625257 18322237084824633561468943)
    ·
      refine ⟨27483355627236950342203415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18322237084824633561468943 27483355627236950342203415)
      ·
        refine ⟨41225033440855425513305123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27483355627236950342203415 41225033440855425513305123)
        ·
          refine ⟨61837550161283138269957685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41225033440855425513305123 61837550161283138269957685)
          ·
            refine ⟨5797270327620294212808533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 61837550161283138269957685 5797270327620294212808533)
            ·
              refine ⟨33968380825900161403175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 5797270327620294212808533 33968380825900161403175)
              ·
                rfl

theorem cell20_669801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 9].length) (baseStart_669801 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_669801 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_669801 prefixEnd_669801 := by exact prefixLift 669801
  have htrace : WordTrace (prefixWord ++ tailWord_669801) baseStart_669801 baseEnd_669801 := by
    simpa [prefixWord, tailWord_669801, baseEnd_669801] using wordTrace_append hprefix tailTrace_669801
  have hstable : (prefixWord ++ tailWord_669801).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_669801).length < 2 ^ (prefixWord ++ tailWord_669801).sum := by decide
  have hdescent : baseEnd_669801 < baseStart_669801 := by decide
  rcases family_descends (prefixWord ++ tailWord_669801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_669804 : List Nat := [2, 2, 1, 1, 3, 3, 3, 2, 3]
def baseStart_669804 : Nat := 118140960795 + 669804 * 2 ^ 59
def prefixEnd_669804 : Nat := 4983230072969 + 3 ^ 40 * 669804 * 2
def baseEnd_669804 : Nat := 305716796714846775528563

theorem tailTrace_669804 : CollatzResearch.WordTrace tailWord_669804 prefixEnd_669804 305716796714846775528563 := by
  unfold tailWord_669804
  simp only [CollatzResearch.WordTrace]
  refine ⟨12214879432710988130492233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16286505910281317507322977 12214879432710988130492233)
  ·
    refine ⟨9161159574533241097869175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12214879432710988130492233 9161159574533241097869175)
    ·
      refine ⟨13741739361799861646803763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9161159574533241097869175 13741739361799861646803763)
      ·
        refine ⟨20612609042699792470205645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13741739361799861646803763 20612609042699792470205645)
        ·
          refine ⟨7729728391012422176327117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20612609042699792470205645 7729728391012422176327117)
          ·
            refine ⟨2898648146629658316122669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7729728391012422176327117 2898648146629658316122669)
            ·
              refine ⟨1086993054986121868546001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2898648146629658316122669 1086993054986121868546001)
              ·
                refine ⟨815244791239591401409501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1086993054986121868546001 815244791239591401409501)
                ·
                  refine ⟨305716796714846775528563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 815244791239591401409501 305716796714846775528563)
                  ·
                    rfl

theorem cell20_669804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 3].length) (baseStart_669804 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_669804 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_669804 prefixEnd_669804 := by exact prefixLift 669804
  have htrace : WordTrace (prefixWord ++ tailWord_669804) baseStart_669804 baseEnd_669804 := by
    simpa [prefixWord, tailWord_669804, baseEnd_669804] using wordTrace_append hprefix tailTrace_669804
  have hstable : (prefixWord ++ tailWord_669804).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_669804).length < 2 ^ (prefixWord ++ tailWord_669804).sum := by decide
  have hdescent : baseEnd_669804 < baseStart_669804 := by decide
  rcases family_descends (prefixWord ++ tailWord_669804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_669821 : List Nat := [1, 4, 1, 1, 3, 3, 3, 1, 3]
def baseStart_669821 : Nat := 118140960795 + 669821 * 2 ^ 59
def prefixEnd_669821 : Nat := 4983230072969 + 3 ^ 40 * 669821 * 2
def baseEnd_669821 : Nat := 305724555978070271961827

theorem tailTrace_669821 : CollatzResearch.WordTrace tailWord_669821 prefixEnd_669821 305724555978070271961827 := by
  unfold tailWord_669821
  simp only [CollatzResearch.WordTrace]
  refine ⟨24430378906360388164353317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16286919270906925442902211 24430378906360388164353317)
  ·
    refine ⟨4580696044942572780816247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24430378906360388164353317 4580696044942572780816247)
    ·
      refine ⟨6871044067413859171224371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4580696044942572780816247 6871044067413859171224371)
      ·
        refine ⟨10306566101120788756836557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6871044067413859171224371 10306566101120788756836557)
        ·
          refine ⟨3864962287920295783813709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10306566101120788756836557 3864962287920295783813709)
          ·
            refine ⟨1449360857970110918930141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3864962287920295783813709 1449360857970110918930141)
            ·
              refine ⟨543510321738791594598803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1449360857970110918930141 543510321738791594598803)
              ·
                refine ⟨815265482608187391898205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 543510321738791594598803 815265482608187391898205)
                ·
                  refine ⟨305724555978070271961827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 815265482608187391898205 305724555978070271961827)
                  ·
                    rfl

theorem cell20_669821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 3, 3, 1, 3].length) (baseStart_669821 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_669821 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_669821 prefixEnd_669821 := by exact prefixLift 669821
  have htrace : WordTrace (prefixWord ++ tailWord_669821) baseStart_669821 baseEnd_669821 := by
    simpa [prefixWord, tailWord_669821, baseEnd_669821] using wordTrace_append hprefix tailTrace_669821
  have hstable : (prefixWord ++ tailWord_669821).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_669821).length < 2 ^ (prefixWord ++ tailWord_669821).sum := by decide
  have hdescent : baseEnd_669821 < baseStart_669821 := by decide
  rcases family_descends (prefixWord ++ tailWord_669821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_669856 : List Nat := [2, 1, 1, 4, 2, 4, 6]
def baseStart_669856 : Nat := 118140960795 + 669856 * 2 ^ 59
def prefixEnd_669856 : Nat := 4983230072969 + 3 ^ 40 * 669856 * 2
def baseEnd_669856 : Nat := 33971170103529522866113

theorem tailTrace_669856 : CollatzResearch.WordTrace tailWord_669856 prefixEnd_669856 33971170103529522866113 := by
  unfold tailWord_669856
  simp only [CollatzResearch.WordTrace]
  refine ⟨12215827730616794570938711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16287770307489059427918281 12215827730616794570938711)
  ·
    refine ⟨18323741595925191856408067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12215827730616794570938711 18323741595925191856408067)
    ·
      refine ⟨27485612393887787784612101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18323741595925191856408067 27485612393887787784612101)
      ·
        refine ⟨5153552323853960209614769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 27485612393887787784612101 5153552323853960209614769)
        ·
          refine ⟨3865164242890470157211077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5153552323853960209614769 3865164242890470157211077)
          ·
            refine ⟨724718295541963154477077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3865164242890470157211077 724718295541963154477077)
            ·
              refine ⟨33971170103529522866113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 724718295541963154477077 33971170103529522866113)
              ·
                rfl

theorem cell20_669856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 4, 6].length) (baseStart_669856 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_669856 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_669856 prefixEnd_669856 := by exact prefixLift 669856
  have htrace : WordTrace (prefixWord ++ tailWord_669856) baseStart_669856 baseEnd_669856 := by
    simpa [prefixWord, tailWord_669856, baseEnd_669856] using wordTrace_append hprefix tailTrace_669856
  have hstable : (prefixWord ++ tailWord_669856).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_669856).length < 2 ^ (prefixWord ++ tailWord_669856).sum := by decide
  have hdescent : baseEnd_669856 < baseStart_669856 := by decide
  rcases family_descends (prefixWord ++ tailWord_669856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_669873 : List Nat := [1, 2, 2, 5, 2, 1, 2, 5]
def baseStart_669873 : Nat := 118140960795 + 669873 * 2 ^ 59
def prefixEnd_669873 : Nat := 4983230072969 + 3 ^ 40 * 669873 * 2
def baseEnd_669873 : Nat := 101916096731663067409427

theorem tailTrace_669873 : CollatzResearch.WordTrace tailWord_669873 prefixEnd_669873 101916096731663067409427 := by
  unfold tailWord_669873
  simp only [CollatzResearch.WordTrace]
  refine ⟨24432275502172001045246273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16288183668114667363497515 24432275502172001045246273)
  ·
    refine ⟨18324206626629000783934705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24432275502172001045246273 18324206626629000783934705)
    ·
      refine ⟨13743154969971750587951029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18324206626629000783934705 13743154969971750587951029)
      ·
        refine ⟨1288420778434851617620409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 13743154969971750587951029 1288420778434851617620409)
        ·
          refine ⟨966315583826138713215307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1288420778434851617620409 966315583826138713215307)
          ·
            refine ⟨1449473375739208069822961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 966315583826138713215307 1449473375739208069822961)
            ·
              refine ⟨1087105031804406052367221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1449473375739208069822961 1087105031804406052367221)
              ·
                refine ⟨101916096731663067409427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1087105031804406052367221 101916096731663067409427)
                ·
                  rfl

theorem cell20_669873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 1, 2, 5].length) (baseStart_669873 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_669873 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_669873 prefixEnd_669873 := by exact prefixLift 669873
  have htrace : WordTrace (prefixWord ++ tailWord_669873) baseStart_669873 baseEnd_669873 := by
    simpa [prefixWord, tailWord_669873, baseEnd_669873] using wordTrace_append hprefix tailTrace_669873
  have hstable : (prefixWord ++ tailWord_669873).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_669873).length < 2 ^ (prefixWord ++ tailWord_669873).sum := by decide
  have hdescent : baseEnd_669873 < baseStart_669873 := by decide
  rcases family_descends (prefixWord ++ tailWord_669873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_669890 : List Nat := [3, 5, 1, 1, 1, 1, 2, 6]
def baseStart_669890 : Nat := 118140960795 + 669890 * 2 ^ 59
def prefixEnd_669890 : Nat := 4983230072969 + 3 ^ 40 * 669890 * 2
def baseEnd_669890 : Nat := 101918683152737566220515

theorem tailTrace_669890 : CollatzResearch.WordTrace tailWord_669890 prefixEnd_669890 101918683152737566220515 := by
  unfold tailWord_669890
  simp only [CollatzResearch.WordTrace]
  refine ⟨6108223885777603237153781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16288597028740275299076749 6108223885777603237153781)
  ·
    refine ⟨572645989291650303483167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 6108223885777603237153781 572645989291650303483167)
    ·
      refine ⟨858968983937475455224751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 572645989291650303483167 858968983937475455224751)
      ·
        refine ⟨1288453475906213182837127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 858968983937475455224751 1288453475906213182837127)
        ·
          refine ⟨1932680213859319774255691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1288453475906213182837127 1932680213859319774255691)
          ·
            refine ⟨2899020320788979661383537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1932680213859319774255691 2899020320788979661383537)
            ·
              refine ⟨2174265240591734746037653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2899020320788979661383537 2174265240591734746037653)
              ·
                refine ⟨101918683152737566220515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2174265240591734746037653 101918683152737566220515)
                ·
                  rfl

theorem cell20_669890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 2, 6].length) (baseStart_669890 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_669890 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_669890 prefixEnd_669890 := by exact prefixLift 669890
  have htrace : WordTrace (prefixWord ++ tailWord_669890) baseStart_669890 baseEnd_669890 := by
    simpa [prefixWord, tailWord_669890, baseEnd_669890] using wordTrace_append hprefix tailTrace_669890
  have hstable : (prefixWord ++ tailWord_669890).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_669890).length < 2 ^ (prefixWord ++ tailWord_669890).sum := by decide
  have hdescent : baseEnd_669890 < baseStart_669890 := by decide
  rcases family_descends (prefixWord ++ tailWord_669890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_669939 : List Nat := [1, 1, 1, 2, 2, 4, 1, 5, 3]
def baseStart_669939 : Nat := 118140960795 + 669939 * 2 ^ 59
def prefixEnd_669939 : Nat := 4983230072969 + 3 ^ 40 * 669939 * 2
def baseEnd_669939 : Nat := 305778414393386306028011

theorem tailTrace_669939 : CollatzResearch.WordTrace tailWord_669939 prefixEnd_669939 305778414393386306028011 := by
  unfold tailWord_669939
  simp only [CollatzResearch.WordTrace]
  refine ⟨24434682719932894317148871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16289788479955262878099247 24434682719932894317148871)
  ·
    refine ⟨36652024079899341475723307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24434682719932894317148871 36652024079899341475723307)
    ·
      refine ⟨54978036119849012213584961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36652024079899341475723307 54978036119849012213584961)
      ·
        refine ⟨41233527089886759160188721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54978036119849012213584961 41233527089886759160188721)
        ·
          refine ⟨30925145317415069370141541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41233527089886759160188721 30925145317415069370141541)
          ·
            refine ⟨5798464747015325506901539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 30925145317415069370141541 5798464747015325506901539)
            ·
              refine ⟨8697697120522988260352309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5798464747015325506901539 8697697120522988260352309)
              ·
                refine ⟨815409105049030149408029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8697697120522988260352309 815409105049030149408029)
                ·
                  refine ⟨305778414393386306028011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 815409105049030149408029 305778414393386306028011)
                  ·
                    rfl

theorem cell20_669939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 1, 5, 3].length) (baseStart_669939 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_669939 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_669939 prefixEnd_669939 := by exact prefixLift 669939
  have htrace : WordTrace (prefixWord ++ tailWord_669939) baseStart_669939 baseEnd_669939 := by
    simpa [prefixWord, tailWord_669939, baseEnd_669939] using wordTrace_append hprefix tailTrace_669939
  have hstable : (prefixWord ++ tailWord_669939).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_669939).length < 2 ^ (prefixWord ++ tailWord_669939).sum := by decide
  have hdescent : baseEnd_669939 < baseStart_669939 := by decide
  rcases family_descends (prefixWord ++ tailWord_669939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_669946 : List Nat := [3, 1, 1, 1, 1, 5, 1, 1, 6]
def baseStart_669946 : Nat := 118140960795 + 669946 * 2 ^ 59
def prefixEnd_669946 : Nat := 4983230072969 + 3 ^ 40 * 669946 * 2
def baseEnd_669946 : Nat := 305781609384125392794649

theorem tailTrace_669946 : CollatzResearch.WordTrace tailWord_669946 prefixEnd_669946 305781609384125392794649 := by
  unfold tailWord_669946
  simp only [CollatzResearch.WordTrace]
  refine ⟨6108734507726883628163423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16289958687271689675102461 6108734507726883628163423)
  ·
    refine ⟨9163101761590325442245135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6108734507726883628163423 9163101761590325442245135)
    ·
      refine ⟨13744652642385488163367703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9163101761590325442245135 13744652642385488163367703)
      ·
        refine ⟨20616978963578232245051555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13744652642385488163367703 20616978963578232245051555)
        ·
          refine ⟨30925468445367348367577333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20616978963578232245051555 30925468445367348367577333)
          ·
            refine ⟨2899262666753188909460375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 30925468445367348367577333 2899262666753188909460375)
            ·
              refine ⟨4348894000129783364190563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2899262666753188909460375 4348894000129783364190563)
              ·
                refine ⟨6523341000194675046285845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4348894000129783364190563 6523341000194675046285845)
                ·
                  refine ⟨305781609384125392794649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6523341000194675046285845 305781609384125392794649)
                  ·
                    rfl

theorem cell20_669946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 1, 1, 6].length) (baseStart_669946 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_669946 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_669946 prefixEnd_669946 := by exact prefixLift 669946
  have htrace : WordTrace (prefixWord ++ tailWord_669946) baseStart_669946 baseEnd_669946 := by
    simpa [prefixWord, tailWord_669946, baseEnd_669946] using wordTrace_append hprefix tailTrace_669946
  have hstable : (prefixWord ++ tailWord_669946).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_669946).length < 2 ^ (prefixWord ++ tailWord_669946).sum := by decide
  have hdescent : baseEnd_669946 < baseStart_669946 := by decide
  rcases family_descends (prefixWord ++ tailWord_669946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_670004 : List Nat := [2, 5, 1, 1, 1, 4, 2, 4]
def baseStart_670004 : Nat := 118140960795 + 670004 * 2 ^ 59
def prefixEnd_670004 : Nat := 4983230072969 + 3 ^ 40 * 670004 * 2
def baseEnd_670004 : Nat := 101936027388178322953693

theorem tailTrace_670004 : CollatzResearch.WordTrace tailWord_670004 prefixEnd_670004 101936027388178322953693 := by
  unfold tailWord_670004
  simp only [CollatzResearch.WordTrace]
  refine ⟨12218526732348705209132533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16291368976464940278843377 12218526732348705209132533)
  ·
    refine ⟨1145486881157691113356175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 12218526732348705209132533 1145486881157691113356175)
    ·
      refine ⟨1718230321736536670034263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1145486881157691113356175 1718230321736536670034263)
      ·
        refine ⟨2577345482604805005051395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1718230321736536670034263 2577345482604805005051395)
        ·
          refine ⟨3866018223907207507577093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2577345482604805005051395 3866018223907207507577093)
          ·
            refine ⟨724878416982601407670705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3866018223907207507577093 724878416982601407670705)
            ·
              refine ⟨543658812736951055753029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 724878416982601407670705 543658812736951055753029)
              ·
                refine ⟨101936027388178322953693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 543658812736951055753029 101936027388178322953693)
                ·
                  rfl

theorem cell20_670004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 4, 2, 4].length) (baseStart_670004 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_670004 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_670004 prefixEnd_670004 := by exact prefixLift 670004
  have htrace : WordTrace (prefixWord ++ tailWord_670004) baseStart_670004 baseEnd_670004 := by
    simpa [prefixWord, tailWord_670004, baseEnd_670004] using wordTrace_append hprefix tailTrace_670004
  have hstable : (prefixWord ++ tailWord_670004).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_670004).length < 2 ^ (prefixWord ++ tailWord_670004).sum := by decide
  have hdescent : baseEnd_670004 < baseStart_670004 := by decide
  rcases family_descends (prefixWord ++ tailWord_670004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_670008 : List Nat := [2, 1, 2, 1, 3, 1, 6, 4]
def baseStart_670008 : Nat := 118140960795 + 670008 * 2 ^ 59
def prefixEnd_670008 : Nat := 4983230072969 + 3 ^ 40 * 670008 * 2
def baseEnd_670008 : Nat := 101936635957842910909243

theorem tailTrace_670008 : CollatzResearch.WordTrace tailWord_670008 prefixEnd_670008 101936635957842910909243 := by
  unfold tailWord_670008
  simp only [CollatzResearch.WordTrace]
  refine ⟨12218599678341459550705339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16291466237788612734273785 12218599678341459550705339)
  ·
    refine ⟨18327899517512189326058009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12218599678341459550705339 18327899517512189326058009)
    ·
      refine ⟨13745924638134141994543507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18327899517512189326058009 13745924638134141994543507)
      ·
        refine ⟨20618886957201212991815261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13745924638134141994543507 20618886957201212991815261)
        ·
          refine ⟨7732082608950454871930723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20618886957201212991815261 7732082608950454871930723)
          ·
            refine ⟨11598123913425682307896085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7732082608950454871930723 11598123913425682307896085)
            ·
              refine ⟨543662058441828858182629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 11598123913425682307896085 543662058441828858182629)
              ·
                refine ⟨101936635957842910909243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 543662058441828858182629 101936635957842910909243)
                ·
                  rfl

theorem cell20_670008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 6, 4].length) (baseStart_670008 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_670008 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_670008 prefixEnd_670008 := by exact prefixLift 670008
  have htrace : WordTrace (prefixWord ++ tailWord_670008) baseStart_670008 baseEnd_670008 := by
    simpa [prefixWord, tailWord_670008, baseEnd_670008] using wordTrace_append hprefix tailTrace_670008
  have hstable : (prefixWord ++ tailWord_670008).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_670008).length < 2 ^ (prefixWord ++ tailWord_670008).sum := by decide
  have hdescent : baseEnd_670008 < baseStart_670008 := by decide
  rcases family_descends (prefixWord ++ tailWord_670008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_670091 : List Nat := [1, 1, 1, 1, 4, 4, 1, 4, 3]
def baseStart_670091 : Nat := 118140960795 + 670091 * 2 ^ 59
def prefixEnd_670091 : Nat := 4983230072969 + 3 ^ 40 * 670091 * 2
def baseEnd_670091 : Nat := 305847791335149332960723

theorem tailTrace_670091 : CollatzResearch.WordTrace tailWord_670091 prefixEnd_670091 305847791335149332960723 := by
  unfold tailWord_670091
  simp only [CollatzResearch.WordTrace]
  refine ⟨24440226615382224276682127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16293484410254816184454751 24440226615382224276682127)
  ·
    refine ⟨36660339923073336415023191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24440226615382224276682127 36660339923073336415023191)
    ·
      refine ⟨54990509884610004622534787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36660339923073336415023191 54990509884610004622534787)
      ·
        refine ⟨82485764826915006933802181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54990509884610004622534787 82485764826915006933802181)
        ·
          refine ⟨15466080905046563800087909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 82485764826915006933802181 15466080905046563800087909)
          ·
            refine ⟨2899890169696230712516483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15466080905046563800087909 2899890169696230712516483)
            ·
              refine ⟨4349835254544346068774725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2899890169696230712516483 4349835254544346068774725)
              ·
                refine ⟨815594110227064887895261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4349835254544346068774725 815594110227064887895261)
                ·
                  refine ⟨305847791335149332960723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 815594110227064887895261 305847791335149332960723)
                  ·
                    rfl

theorem cell20_670091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 1, 4, 3].length) (baseStart_670091 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_670091 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_670091 prefixEnd_670091 := by exact prefixLift 670091
  have htrace : WordTrace (prefixWord ++ tailWord_670091) baseStart_670091 baseEnd_670091 := by
    simpa [prefixWord, tailWord_670091, baseEnd_670091] using wordTrace_append hprefix tailTrace_670091
  have hstable : (prefixWord ++ tailWord_670091).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_670091).length < 2 ^ (prefixWord ++ tailWord_670091).sum := by decide
  have hdescent : baseEnd_670091 < baseStart_670091 := by decide
  rcases family_descends (prefixWord ++ tailWord_670091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_670153 : List Nat := [1, 2, 1, 1, 2, 1, 6, 4, 2]
def baseStart_670153 : Nat := 118140960795 + 670153 * 2 ^ 59
def prefixEnd_670153 : Nat := 4983230072969 + 3 ^ 40 * 670153 * 2
def baseEnd_670153 : Nat := 305876089824552672893803

theorem tailTrace_670153 : CollatzResearch.WordTrace tailWord_670153 prefixEnd_670153 305876089824552672893803 := by
  unfold tailWord_670153
  simp only [CollatzResearch.WordTrace]
  refine ⟨24442487941157608865439113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16294991960771739243626075 24442487941157608865439113)
  ·
    refine ⟨18331865955868206649079335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24442487941157608865439113 18331865955868206649079335)
    ·
      refine ⟨27497798933802309973619003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18331865955868206649079335 27497798933802309973619003)
      ·
        refine ⟨41246698400703464960428505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27497798933802309973619003 41246698400703464960428505)
        ·
          refine ⟨30935023800527598720321379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41246698400703464960428505 30935023800527598720321379)
          ·
            refine ⟨46402535700791398080482069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30935023800527598720321379 46402535700791398080482069)
            ·
              refine ⟨2175118860974596785022597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 46402535700791398080482069 2175118860974596785022597)
              ·
                refine ⟨407834786432736897191737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2175118860974596785022597 407834786432736897191737)
                ·
                  refine ⟨305876089824552672893803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 407834786432736897191737 305876089824552672893803)
                  ·
                    rfl

theorem cell20_670153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 6, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 6, 4, 2].length) (baseStart_670153 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_670153 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_670153 prefixEnd_670153 := by exact prefixLift 670153
  have htrace : WordTrace (prefixWord ++ tailWord_670153) baseStart_670153 baseEnd_670153 := by
    simpa [prefixWord, tailWord_670153, baseEnd_670153] using wordTrace_append hprefix tailTrace_670153
  have hstable : (prefixWord ++ tailWord_670153).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_670153).length < 2 ^ (prefixWord ++ tailWord_670153).sum := by decide
  have hdescent : baseEnd_670153 < baseStart_670153 := by decide
  rcases family_descends (prefixWord ++ tailWord_670153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_670188 : List Nat := [2, 2, 1, 1, 2, 1, 3, 1, 7]
def baseStart_670188 : Nat := 118140960795 + 670188 * 2 ^ 59
def prefixEnd_670188 : Nat := 4983230072969 + 3 ^ 40 * 670188 * 2
def baseEnd_670188 : Nat := 305892064778248106726993

theorem tailTrace_670188 : CollatzResearch.WordTrace tailWord_670188 prefixEnd_670188 305892064778248106726993 := by
  unfold tailWord_670188
  simp only [CollatzResearch.WordTrace]
  refine ⟨12221882248015404921481609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16295842997353873228642145 12221882248015404921481609)
  ·
    refine ⟨9166411686011553691111207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12221882248015404921481609 9166411686011553691111207)
    ·
      refine ⟨13749617529017330536666811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9166411686011553691111207 13749617529017330536666811)
      ·
        refine ⟨20624426293525995805000217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13749617529017330536666811 20624426293525995805000217)
        ·
          refine ⟨15468319720144496853750163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20624426293525995805000217 15468319720144496853750163)
          ·
            refine ⟨23202479580216745280625245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15468319720144496853750163 23202479580216745280625245)
            ·
              refine ⟨8700929842581279480234467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23202479580216745280625245 8700929842581279480234467)
              ·
                refine ⟨13051394763871919220351701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8700929842581279480234467 13051394763871919220351701)
                ·
                  refine ⟨305892064778248106726993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13051394763871919220351701 305892064778248106726993)
                  ·
                    rfl

theorem cell20_670188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 7].length) (baseStart_670188 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_670188 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_670188 prefixEnd_670188 := by exact prefixLift 670188
  have htrace : WordTrace (prefixWord ++ tailWord_670188) baseStart_670188 baseEnd_670188 := by
    simpa [prefixWord, tailWord_670188, baseEnd_670188] using wordTrace_append hprefix tailTrace_670188
  have hstable : (prefixWord ++ tailWord_670188).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_670188).length < 2 ^ (prefixWord ++ tailWord_670188).sum := by decide
  have hdescent : baseEnd_670188 < baseStart_670188 := by decide
  rcases family_descends (prefixWord ++ tailWord_670188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_670205 : List Nat := [1, 4, 1, 1, 1, 3, 2, 4, 3]
def baseStart_670205 : Nat := 118140960795 + 670205 * 2 ^ 59
def prefixEnd_670205 : Nat := 4983230072969 + 3 ^ 40 * 670205 * 2
def baseEnd_670205 : Nat := 305899824041471603160257

theorem tailTrace_670205 : CollatzResearch.WordTrace tailWord_670205 prefixEnd_670205 305899824041471603160257 := by
  unfold tailWord_670205
  simp only [CollatzResearch.WordTrace]
  refine ⟨24444384536969221746332069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16296256357979481164221379 24444384536969221746332069)
  ·
    refine ⟨4583322100681729077437263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24444384536969221746332069 4583322100681729077437263)
    ·
      refine ⟨6874983151022593616155895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4583322100681729077437263 6874983151022593616155895)
      ·
        refine ⟨10312474726533890424233843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6874983151022593616155895 10312474726533890424233843)
        ·
          refine ⟨15468712089800835636350765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10312474726533890424233843 15468712089800835636350765)
          ·
            refine ⟨5800767033675313363631537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15468712089800835636350765 5800767033675313363631537)
            ·
              refine ⟨4350575275256485022723653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5800767033675313363631537 4350575275256485022723653)
              ·
                refine ⟨815732864110590941760685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4350575275256485022723653 815732864110590941760685)
                ·
                  refine ⟨305899824041471603160257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 815732864110590941760685 305899824041471603160257)
                  ·
                    rfl

theorem cell20_670205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 2, 4, 3].length) (baseStart_670205 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_670205 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_670205 prefixEnd_670205 := by exact prefixLift 670205
  have htrace : WordTrace (prefixWord ++ tailWord_670205) baseStart_670205 baseEnd_670205 := by
    simpa [prefixWord, tailWord_670205, baseEnd_670205] using wordTrace_append hprefix tailTrace_670205
  have hstable : (prefixWord ++ tailWord_670205).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_670205).length < 2 ^ (prefixWord ++ tailWord_670205).sum := by decide
  have hdescent : baseEnd_670205 < baseStart_670205 := by decide
  rcases family_descends (prefixWord ++ tailWord_670205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_670214 : List Nat := [6, 2, 1, 1, 1, 3, 2, 1, 3]
def baseStart_670214 : Nat := 118140960795 + 670214 * 2 ^ 59
def prefixEnd_670214 : Nat := 4983230072969 + 3 ^ 40 * 670214 * 2
def baseEnd_670214 : Nat := 305903931886707571860221

theorem tailTrace_670214 : CollatzResearch.WordTrace tailWord_670214 prefixEnd_670214 305903931886707571860221 := by
  unfold tailWord_670214
  simp only [CollatzResearch.WordTrace]
  refine ⟨763897274810519258856553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 16296475195957744188939797 763897274810519258856553)
  ·
    refine ⟨572922956107889444142415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 763897274810519258856553 572922956107889444142415)
    ·
      refine ⟨859384434161834166213623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 572922956107889444142415 859384434161834166213623)
      ·
        refine ⟨1289076651242751249320435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 859384434161834166213623 1289076651242751249320435)
        ·
          refine ⟨1933614976864126873980653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1289076651242751249320435 1933614976864126873980653)
          ·
            refine ⟨725105616324047577742745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1933614976864126873980653 725105616324047577742745)
            ·
              refine ⟨543829212243035683307059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 725105616324047577742745 543829212243035683307059)
              ·
                refine ⟨815743818364553524960589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 543829212243035683307059 815743818364553524960589)
                ·
                  refine ⟨305903931886707571860221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 815743818364553524960589 305903931886707571860221)
                  ·
                    rfl

theorem cell20_670214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 3, 2, 1, 3].length) (baseStart_670214 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_670214 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_670214 prefixEnd_670214 := by exact prefixLift 670214
  have htrace : WordTrace (prefixWord ++ tailWord_670214) baseStart_670214 baseEnd_670214 := by
    simpa [prefixWord, tailWord_670214, baseEnd_670214] using wordTrace_append hprefix tailTrace_670214
  have hstable : (prefixWord ++ tailWord_670214).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_670214).length < 2 ^ (prefixWord ++ tailWord_670214).sum := by decide
  have hdescent : baseEnd_670214 < baseStart_670214 := by decide
  rcases family_descends (prefixWord ++ tailWord_670214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_670219 : List Nat := [1, 1, 1, 1, 7, 1, 1, 7]
def baseStart_670219 : Nat := 118140960795 + 670219 * 2 ^ 59
def prefixEnd_670219 : Nat := 4983230072969 + 3 ^ 40 * 670219 * 2
def baseEnd_670219 : Nat := 101968738007649925564511

theorem tailTrace_670219 : CollatzResearch.WordTrace tailWord_670219 prefixEnd_670219 101968738007649925564511 := by
  unfold tailWord_670219
  simp only [CollatzResearch.WordTrace]
  refine ⟨24444895158918502137341711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16296596772612334758227807 24444895158918502137341711)
  ·
    refine ⟨36667342738377753206012567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24444895158918502137341711 36667342738377753206012567)
    ·
      refine ⟨55001014107566629809018851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36667342738377753206012567 55001014107566629809018851)
      ·
        refine ⟨82501521161349944713528277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55001014107566629809018851 82501521161349944713528277)
        ·
          refine ⟨1933629402219139329223319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 82501521161349944713528277 1933629402219139329223319)
          ·
            refine ⟨2900444103328708993834979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1933629402219139329223319 2900444103328708993834979)
            ·
              refine ⟨4350666154993063490752469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2900444103328708993834979 4350666154993063490752469)
              ·
                refine ⟨101968738007649925564511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4350666154993063490752469 101968738007649925564511)
                ·
                  rfl

theorem cell20_670219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 1, 7].length) (baseStart_670219 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_670219 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_670219 prefixEnd_670219 := by exact prefixLift 670219
  have htrace : WordTrace (prefixWord ++ tailWord_670219) baseStart_670219 baseEnd_670219 := by
    simpa [prefixWord, tailWord_670219, baseEnd_670219] using wordTrace_append hprefix tailTrace_670219
  have hstable : (prefixWord ++ tailWord_670219).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_670219).length < 2 ^ (prefixWord ++ tailWord_670219).sum := by decide
  have hdescent : baseEnd_670219 < baseStart_670219 := by decide
  rcases family_descends (prefixWord ++ tailWord_670219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_670222 : List Nat := [4, 1, 1, 2, 3, 2, 1, 3, 3]
def baseStart_670222 : Nat := 118140960795 + 670222 * 2 ^ 59
def prefixEnd_670222 : Nat := 4983230072969 + 3 ^ 40 * 670222 * 2
def baseEnd_670222 : Nat := 305907583304695099593521

theorem tailTrace_670222 : CollatzResearch.WordTrace tailWord_670222 prefixEnd_670222 305907583304695099593521 := by
  unfold tailWord_670222
  simp only [CollatzResearch.WordTrace]
  refine ⟨3055625572238454206212615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16296669718605089099800613 3055625572238454206212615)
  ·
    refine ⟨4583438358357681309318923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3055625572238454206212615 4583438358357681309318923)
    ·
      refine ⟨6875157537536521963978385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4583438358357681309318923 6875157537536521963978385)
      ·
        refine ⟨5156368153152391472983789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6875157537536521963978385 5156368153152391472983789)
        ·
          refine ⟨1933638057432146802368921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5156368153152391472983789 1933638057432146802368921)
          ·
            refine ⟨1450228543074110101776691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1933638057432146802368921 1450228543074110101776691)
            ·
              refine ⟨2175342814611165152665037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1450228543074110101776691 2175342814611165152665037)
              ·
                refine ⟨815753555479186932249389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2175342814611165152665037 815753555479186932249389)
                ·
                  refine ⟨305907583304695099593521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 815753555479186932249389 305907583304695099593521)
                  ·
                    rfl

theorem cell20_670222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 2, 1, 3, 3].length) (baseStart_670222 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_670222 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_670222 prefixEnd_670222 := by exact prefixLift 670222
  have htrace : WordTrace (prefixWord ++ tailWord_670222) baseStart_670222 baseEnd_670222 := by
    simpa [prefixWord, tailWord_670222, baseEnd_670222] using wordTrace_append hprefix tailTrace_670222
  have hstable : (prefixWord ++ tailWord_670222).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_670222).length < 2 ^ (prefixWord ++ tailWord_670222).sum := by decide
  have hdescent : baseEnd_670222 < baseStart_670222 := by decide
  rcases family_descends (prefixWord ++ tailWord_670222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_670253 : List Nat := [1, 5, 4, 1, 9]
def baseStart_670253 : Nat := 118140960795 + 670253 * 2 ^ 59
def prefixEnd_670253 : Nat := 4983230072969 + 3 ^ 40 * 670253 * 2
def baseEnd_670253 : Nat := 3776811512955515673581

theorem tailTrace_670253 : CollatzResearch.WordTrace tailWord_670253 prefixEnd_670253 3776811512955515673581 := by
  unfold tailWord_670253
  simp only [CollatzResearch.WordTrace]
  refine ⟨24446135240795325944079413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16297423493863550629386275 24446135240795325944079413)
  ·
    refine ⟨2291825178824561807257445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 24446135240795325944079413 2291825178824561807257445)
    ·
      refine ⟨429717221029605338860771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2291825178824561807257445 429717221029605338860771)
      ·
        refine ⟨644575831544408008291157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 429717221029605338860771 644575831544408008291157)
        ·
          refine ⟨3776811512955515673581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 9 644575831544408008291157 3776811512955515673581)
          ·
            rfl

theorem cell20_670253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 9].length) (baseStart_670253 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_670253 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_670253 prefixEnd_670253 := by exact prefixLift 670253
  have htrace : WordTrace (prefixWord ++ tailWord_670253) baseStart_670253 baseEnd_670253 := by
    simpa [prefixWord, tailWord_670253, baseEnd_670253] using wordTrace_append hprefix tailTrace_670253
  have hstable : (prefixWord ++ tailWord_670253).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_670253).length < 2 ^ (prefixWord ++ tailWord_670253).sum := by decide
  have hdescent : baseEnd_670253 < baseStart_670253 := by decide
  rcases family_descends (prefixWord ++ tailWord_670253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_670270 : List Nat := [4, 2, 1, 4, 1, 2, 1, 5]
def baseStart_670270 : Nat := 118140960795 + 670270 * 2 ^ 59
def prefixEnd_670270 : Nat := 4983230072969 + 3 ^ 40 * 670270 * 2
def baseEnd_670270 : Nat := 101976497270873421997775

theorem tailTrace_670270 : CollatzResearch.WordTrace tailWord_670270 prefixEnd_670270 101976497270873421997775 := by
  unfold tailWord_670270
  simp only [CollatzResearch.WordTrace]
  refine ⟨3055844410216717230931033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16297836854489158564965509 3055844410216717230931033)
  ·
    refine ⟨2291883307662537923198275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3055844410216717230931033 2291883307662537923198275)
    ·
      refine ⟨3437824961493806884797413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2291883307662537923198275 3437824961493806884797413)
      ·
        refine ⟨644592180280088790899515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3437824961493806884797413 644592180280088790899515)
        ·
          refine ⟨966888270420133186349273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 644592180280088790899515 966888270420133186349273)
          ·
            refine ⟨725166202815099889761955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 966888270420133186349273 725166202815099889761955)
            ·
              refine ⟨1087749304222649834642933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 725166202815099889761955 1087749304222649834642933)
              ·
                refine ⟨101976497270873421997775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1087749304222649834642933 101976497270873421997775)
                ·
                  rfl

theorem cell20_670270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 2, 1, 5].length) (baseStart_670270 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_670270 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_670270 prefixEnd_670270 := by exact prefixLift 670270
  have htrace : WordTrace (prefixWord ++ tailWord_670270) baseStart_670270 baseEnd_670270 := by
    simpa [prefixWord, tailWord_670270, baseEnd_670270] using wordTrace_append hprefix tailTrace_670270
  have hstable : (prefixWord ++ tailWord_670270).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_670270).length < 2 ^ (prefixWord ++ tailWord_670270).sum := by decide
  have hdescent : baseEnd_670270 < baseStart_670270 := by decide
  rcases family_descends (prefixWord ++ tailWord_670270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_670305 : List Nat := [1, 2, 3, 1, 1, 4, 1, 5, 2]
def baseStart_670305 : Nat := 118140960795 + 670305 * 2 ^ 59
def prefixEnd_670305 : Nat := 4983230072969 + 3 ^ 40 * 670305 * 2
def baseEnd_670305 : Nat := 305945466766315699826515

theorem tailTrace_670305 : CollatzResearch.WordTrace tailWord_670305 prefixEnd_670305 305945466766315699826515 := by
  unfold tailWord_670305
  simp only [CollatzResearch.WordTrace]
  refine ⟨24448031836606938824972369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16298687891071292549981579 24448031836606938824972369)
  ·
    refine ⟨18336023877455204118729277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24448031836606938824972369 18336023877455204118729277)
    ·
      refine ⟨6876008954045701544523479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18336023877455204118729277 6876008954045701544523479)
      ·
        refine ⟨10314013431068552316785219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6876008954045701544523479 10314013431068552316785219)
        ·
          refine ⟨15471020146602828475177829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10314013431068552316785219 15471020146602828475177829)
          ·
            refine ⟨2900816277488030339095843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15471020146602828475177829 2900816277488030339095843)
            ·
              refine ⟨4351224416232045508643765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2900816277488030339095843 4351224416232045508643765)
              ·
                refine ⟨407927289021754266435353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4351224416232045508643765 407927289021754266435353)
                ·
                  refine ⟨305945466766315699826515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 407927289021754266435353 305945466766315699826515)
                  ·
                    rfl

theorem cell20_670305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 1, 5, 2].length) (baseStart_670305 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_670305 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_670305 prefixEnd_670305 := by exact prefixLift 670305
  have htrace : WordTrace (prefixWord ++ tailWord_670305) baseStart_670305 baseEnd_670305 := by
    simpa [prefixWord, tailWord_670305, baseEnd_670305] using wordTrace_append hprefix tailTrace_670305
  have hstable : (prefixWord ++ tailWord_670305).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_670305).length < 2 ^ (prefixWord ++ tailWord_670305).sum := by decide
  have hdescent : baseEnd_670305 < baseStart_670305 := by decide
  rcases family_descends (prefixWord ++ tailWord_670305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_670312 : List Nat := [2, 1, 4, 3, 2, 1, 7]
def baseStart_670312 : Nat := 118140960795 + 670312 * 2 ^ 59
def prefixEnd_670312 : Nat := 4983230072969 + 3 ^ 40 * 670312 * 2
def baseEnd_670312 : Nat := 33994295750783865177017

theorem tailTrace_670312 : CollatzResearch.WordTrace tailWord_670312 prefixEnd_670312 33994295750783865177017 := by
  unfold tailWord_670312
  simp only [CollatzResearch.WordTrace]
  refine ⟨12224143573790789510238595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16298858098387719346984793 12224143573790789510238595)
  ·
    refine ⟨18336215360686184265357893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12224143573790789510238595 18336215360686184265357893)
    ·
      refine ⟨3438040380128659549754605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18336215360686184265357893 3438040380128659549754605)
      ·
        refine ⟨1289265142548247331157977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3438040380128659549754605 1289265142548247331157977)
        ·
          refine ⟨966948856911185498368483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1289265142548247331157977 966948856911185498368483)
          ·
            refine ⟨1450423285366778247552725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 966948856911185498368483 1450423285366778247552725)
            ·
              refine ⟨33994295750783865177017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1450423285366778247552725 33994295750783865177017)
              ·
                rfl

theorem cell20_670312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 1, 7].length) (baseStart_670312 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_670312 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_670312 prefixEnd_670312 := by exact prefixLift 670312
  have htrace : WordTrace (prefixWord ++ tailWord_670312) baseStart_670312 baseEnd_670312 := by
    simpa [prefixWord, tailWord_670312, baseEnd_670312] using wordTrace_append hprefix tailTrace_670312
  have hstable : (prefixWord ++ tailWord_670312).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_670312).length < 2 ^ (prefixWord ++ tailWord_670312).sum := by decide
  have hdescent : baseEnd_670312 < baseStart_670312 := by decide
  rcases family_descends (prefixWord ++ tailWord_670312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_670319 : List Nat := [1, 1, 2, 1, 3, 2, 5, 2, 3]
def baseStart_670319 : Nat := 118140960795 + 670319 * 2 ^ 59
def prefixEnd_670319 : Nat := 4983230072969 + 3 ^ 40 * 670319 * 2
def baseEnd_670319 : Nat := 305951856747793873359791

theorem tailTrace_670319 : CollatzResearch.WordTrace tailWord_670319 prefixEnd_670319 305951856747793873359791 := by
  unfold tailWord_670319
  simp only [CollatzResearch.WordTrace]
  refine ⟨24448542458556219215982011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16299028305704146143988007 24448542458556219215982011)
  ·
    refine ⟨36672813687834328823973017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24448542458556219215982011 36672813687834328823973017)
    ·
      refine ⟨27504610265875746617979763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36672813687834328823973017 27504610265875746617979763)
      ·
        refine ⟨41256915398813619926969645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27504610265875746617979763 41256915398813619926969645)
        ·
          refine ⟨15471343274555107472613617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41256915398813619926969645 15471343274555107472613617)
          ·
            refine ⟨11603507455916330604460213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15471343274555107472613617 11603507455916330604460213)
            ·
              refine ⟨1087828823992155994168145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 11603507455916330604460213 1087828823992155994168145)
              ·
                refine ⟨815871617994116995626109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1087828823992155994168145 815871617994116995626109)
                ·
                  refine ⟨305951856747793873359791, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 815871617994116995626109 305951856747793873359791)
                  ·
                    rfl

theorem cell20_670319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 5, 2, 3].length) (baseStart_670319 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_670319 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_670319 prefixEnd_670319 := by exact prefixLift 670319
  have htrace : WordTrace (prefixWord ++ tailWord_670319) baseStart_670319 baseEnd_670319 := by
    simpa [prefixWord, tailWord_670319, baseEnd_670319] using wordTrace_append hprefix tailTrace_670319
  have hstable : (prefixWord ++ tailWord_670319).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_670319).length < 2 ^ (prefixWord ++ tailWord_670319).sum := by decide
  have hdescent : baseEnd_670319 < baseStart_670319 := by decide
  rcases family_descends (prefixWord ++ tailWord_670319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_670336 : List Nat := [2, 1, 1, 2, 1, 6, 3, 1, 3]
def baseStart_670336 : Nat := 118140960795 + 670336 * 2 ^ 59
def prefixEnd_670336 : Nat := 4983230072969 + 3 ^ 40 * 670336 * 2
def baseEnd_670336 : Nat := 305959616011017369793055

theorem tailTrace_670336 : CollatzResearch.WordTrace tailWord_670336 prefixEnd_670336 305959616011017369793055 := by
  unfold tailWord_670336
  simp only [CollatzResearch.WordTrace]
  refine ⟨12224581249747315559675431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16299441666329754079567241 12224581249747315559675431)
  ·
    refine ⟨18336871874620973339513147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12224581249747315559675431 18336871874620973339513147)
    ·
      refine ⟨27505307811931460009269721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18336871874620973339513147 27505307811931460009269721)
      ·
        refine ⟨20628980858948595006952291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27505307811931460009269721 20628980858948595006952291)
        ·
          refine ⟨30943471288422892510428437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20628980858948595006952291 30943471288422892510428437)
          ·
            refine ⟨1450475216644823086426333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 30943471288422892510428437 1450475216644823086426333)
            ·
              refine ⟨543928206241808657409875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1450475216644823086426333 543928206241808657409875)
              ·
                refine ⟨815892309362712986114813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 543928206241808657409875 815892309362712986114813)
                ·
                  refine ⟨305959616011017369793055, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 815892309362712986114813 305959616011017369793055)
                  ·
                    rfl

theorem cell20_670336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 6, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 6, 3, 1, 3].length) (baseStart_670336 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_670336 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_670336 prefixEnd_670336 := by exact prefixLift 670336
  have htrace : WordTrace (prefixWord ++ tailWord_670336) baseStart_670336 baseEnd_670336 := by
    simpa [prefixWord, tailWord_670336, baseEnd_670336] using wordTrace_append hprefix tailTrace_670336
  have hstable : (prefixWord ++ tailWord_670336).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_670336).length < 2 ^ (prefixWord ++ tailWord_670336).sum := by decide
  have hdescent : baseEnd_670336 < baseStart_670336 := by decide
  rcases family_descends (prefixWord ++ tailWord_670336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_670346 : List Nat := [3, 1, 2, 3, 4, 1, 2, 4]
def baseStart_670346 : Nat := 118140960795 + 670346 * 2 ^ 59
def prefixEnd_670346 : Nat := 4983230072969 + 3 ^ 40 * 670346 * 2
def baseEnd_670346 : Nat := 101988060094500593153227

theorem tailTrace_670346 : CollatzResearch.WordTrace tailWord_670346 prefixEnd_670346 101988060094500593153227 := by
  unfold tailWord_670346
  simp only [CollatzResearch.WordTrace]
  refine ⟨6112381807364600706803723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16299684819638935218143261 6112381807364600706803723)
  ·
    refine ⟨9168572711046901060205585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6112381807364600706803723 9168572711046901060205585)
    ·
      refine ⟨6876429533285175795154189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9168572711046901060205585 6876429533285175795154189)
      ·
        refine ⟨2578661074981940923182821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6876429533285175795154189 2578661074981940923182821)
        ·
          refine ⟨483498951559113923096779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2578661074981940923182821 483498951559113923096779)
          ·
            refine ⟨725248427338670884645169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 483498951559113923096779 725248427338670884645169)
            ·
              refine ⟨543936320504003163483877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 725248427338670884645169 543936320504003163483877)
              ·
                refine ⟨101988060094500593153227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 543936320504003163483877 101988060094500593153227)
                ·
                  rfl

theorem cell20_670346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 4, 1, 2, 4].length) (baseStart_670346 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_670346 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_670346 prefixEnd_670346 := by exact prefixLift 670346
  have htrace : WordTrace (prefixWord ++ tailWord_670346) baseStart_670346 baseEnd_670346 := by
    simpa [prefixWord, tailWord_670346, baseEnd_670346] using wordTrace_append hprefix tailTrace_670346
  have hstable : (prefixWord ++ tailWord_670346).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_670346).length < 2 ^ (prefixWord ++ tailWord_670346).sum := by decide
  have hdescent : baseEnd_670346 < baseStart_670346 := by decide
  rcases family_descends (prefixWord ++ tailWord_670346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_670347 : List Nat := [1, 1, 1, 1, 4, 1, 2, 3, 6]
def baseStart_670347 : Nat := 118140960795 + 670347 * 2 ^ 59
def prefixEnd_670347 : Nat := 4983230072969 + 3 ^ 40 * 670347 * 2
def baseEnd_670347 : Nat := 305964636710750220426343

theorem tailTrace_670347 : CollatzResearch.WordTrace tailWord_670347 prefixEnd_670347 305964636710750220426343 := by
  unfold tailWord_670347
  simp only [CollatzResearch.WordTrace]
  refine ⟨24449563702454779998001295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16299709134969853332000863 24449563702454779998001295)
  ·
    refine ⟨36674345553682169997001943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24449563702454779998001295 36674345553682169997001943)
    ·
      refine ⟨55011518330523254995502915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36674345553682169997001943 55011518330523254995502915)
      ·
        refine ⟨82517277495784882493254373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55011518330523254995502915 82517277495784882493254373)
        ·
          refine ⟨15471989530459665467485195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 82517277495784882493254373 15471989530459665467485195)
          ·
            refine ⟨23207984295689498201227793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15471989530459665467485195 23207984295689498201227793)
            ·
              refine ⟨17405988221767123650920845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23207984295689498201227793 17405988221767123650920845)
              ·
                refine ⟨6527245583162671369095317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17405988221767123650920845 6527245583162671369095317)
                ·
                  refine ⟨305964636710750220426343, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6527245583162671369095317 305964636710750220426343)
                  ·
                    rfl

theorem cell20_670347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 3, 6].length) (baseStart_670347 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_670347 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_670347 prefixEnd_670347 := by exact prefixLift 670347
  have htrace : WordTrace (prefixWord ++ tailWord_670347) baseStart_670347 baseEnd_670347 := by
    simpa [prefixWord, tailWord_670347, baseEnd_670347] using wordTrace_append hprefix tailTrace_670347
  have hstable : (prefixWord ++ tailWord_670347).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_670347).length < 2 ^ (prefixWord ++ tailWord_670347).sum := by decide
  have hdescent : baseEnd_670347 < baseStart_670347 := by decide
  rcases family_descends (prefixWord ++ tailWord_670347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_670381 : List Nat := [1, 5, 2, 1, 1, 2, 3, 1, 4]
def baseStart_670381 : Nat := 118140960795 + 670381 * 2 ^ 59
def prefixEnd_670381 : Nat := 4983230072969 + 3 ^ 40 * 670381 * 2
def baseEnd_670381 : Nat := 305980155237197213292871

theorem tailTrace_670381 : CollatzResearch.WordTrace tailWord_670381 prefixEnd_670381 305980155237197213292871 := by
  unfold tailWord_670381
  simp only [CollatzResearch.WordTrace]
  refine ⟨24450803784331603804738997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16300535856221069203159331 24450803784331603804738997)
  ·
    refine ⟨2292262854781087856694281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 24450803784331603804738997 2292262854781087856694281)
    ·
      refine ⟨1719197141085815892520711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2292262854781087856694281 1719197141085815892520711)
      ·
        refine ⟨2578795711628723838781067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1719197141085815892520711 2578795711628723838781067)
        ·
          refine ⟨3868193567443085758171601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2578795711628723838781067 3868193567443085758171601)
          ·
            refine ⟨2901145175582314318628701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3868193567443085758171601 2901145175582314318628701)
            ·
              refine ⟨1087929440843367869485763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2901145175582314318628701 1087929440843367869485763)
              ·
                refine ⟨1631894161265051804228645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1087929440843367869485763 1631894161265051804228645)
                ·
                  refine ⟨305980155237197213292871, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1631894161265051804228645 305980155237197213292871)
                  ·
                    rfl

theorem cell20_670381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 3, 1, 4].length) (baseStart_670381 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_670381 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_670381 prefixEnd_670381 := by exact prefixLift 670381
  have htrace : WordTrace (prefixWord ++ tailWord_670381) baseStart_670381 baseEnd_670381 := by
    simpa [prefixWord, tailWord_670381, baseEnd_670381] using wordTrace_append hprefix tailTrace_670381
  have hstable : (prefixWord ++ tailWord_670381).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_670381).length < 2 ^ (prefixWord ++ tailWord_670381).sum := by decide
  have hdescent : baseEnd_670381 < baseStart_670381 := by decide
  rcases family_descends (prefixWord ++ tailWord_670381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_670391 : List Nat := [1, 1, 3, 1, 6, 2, 2, 1, 3]
def baseStart_670391 : Nat := 118140960795 + 670391 * 2 ^ 59
def prefixEnd_670391 : Nat := 4983230072969 + 3 ^ 40 * 670391 * 2
def baseEnd_670391 : Nat := 305984719509681622959497

theorem tailTrace_670391 : CollatzResearch.WordTrace tailWord_670391 prefixEnd_670391 305984719509681622959497 := by
  unfold tailWord_670391
  simp only [CollatzResearch.WordTrace]
  refine ⟨24451168514295375512603027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16300779009530250341735351 24451168514295375512603027)
  ·
    refine ⟨36676752771443063268904541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24451168514295375512603027 36676752771443063268904541)
    ·
      refine ⟨13753782289291148725839203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36676752771443063268904541 13753782289291148725839203)
      ·
        refine ⟨20630673433936723088758805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13753782289291148725839203 20630673433936723088758805)
        ·
          refine ⟨967062817215783894785569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 20630673433936723088758805 967062817215783894785569)
          ·
            refine ⟨725297112911837921089177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 967062817215783894785569 725297112911837921089177)
            ·
              refine ⟨543972834683878440816883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 725297112911837921089177 543972834683878440816883)
              ·
                refine ⟨815959252025817661225325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 543972834683878440816883 815959252025817661225325)
                ·
                  refine ⟨305984719509681622959497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 815959252025817661225325 305984719509681622959497)
                  ·
                    rfl

theorem cell20_670391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 2, 2, 1, 3].length) (baseStart_670391 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_670391 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_670391 prefixEnd_670391 := by exact prefixLift 670391
  have htrace : WordTrace (prefixWord ++ tailWord_670391) baseStart_670391 baseEnd_670391 := by
    simpa [prefixWord, tailWord_670391, baseEnd_670391] using wordTrace_append hprefix tailTrace_670391
  have hstable : (prefixWord ++ tailWord_670391).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_670391).length < 2 ^ (prefixWord ++ tailWord_670391).sum := by decide
  have hdescent : baseEnd_670391 < baseStart_670391 := by decide
  rcases family_descends (prefixWord ++ tailWord_670391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_670433 : List Nat := [1, 2, 3, 1, 4, 1, 1, 4, 3]
def baseStart_670433 : Nat := 118140960795 + 670433 * 2 ^ 59
def prefixEnd_670433 : Nat := 4983230072969 + 3 ^ 40 * 670433 * 2
def baseEnd_670433 : Nat := 306003889454116143559325

theorem tailTrace_670433 : CollatzResearch.WordTrace tailWord_670433 prefixEnd_670433 306003889454116143559325 := by
  unfold tailWord_670433
  simp only [CollatzResearch.WordTrace]
  refine ⟨24452700380143216685631953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16301800253428811123754635 24452700380143216685631953)
  ·
    refine ⟨18339525285107412514223965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24452700380143216685631953 18339525285107412514223965)
    ·
      refine ⟨6877321981915279692833987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18339525285107412514223965 6877321981915279692833987)
      ·
        refine ⟨10315982972872919539250981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6877321981915279692833987 10315982972872919539250981)
        ·
          refine ⟨1934246807413672413609559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10315982972872919539250981 1934246807413672413609559)
          ·
            refine ⟨2901370211120508620414339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1934246807413672413609559 2901370211120508620414339)
            ·
              refine ⟨4352055316680762930621509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2901370211120508620414339 4352055316680762930621509)
              ·
                refine ⟨816010371877643049491533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4352055316680762930621509 816010371877643049491533)
                ·
                  refine ⟨306003889454116143559325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 816010371877643049491533 306003889454116143559325)
                  ·
                    rfl

theorem cell20_670433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 1, 4, 3].length) (baseStart_670433 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_670433 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_670433 prefixEnd_670433 := by exact prefixLift 670433
  have htrace : WordTrace (prefixWord ++ tailWord_670433) baseStart_670433 baseEnd_670433 := by
    simpa [prefixWord, tailWord_670433, baseEnd_670433] using wordTrace_append hprefix tailTrace_670433
  have hstable : (prefixWord ++ tailWord_670433).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_670433).length < 2 ^ (prefixWord ++ tailWord_670433).sum := by decide
  have hdescent : baseEnd_670433 < baseStart_670433 := by decide
  rcases family_descends (prefixWord ++ tailWord_670433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_670436 : List Nat := [2, 3, 1, 1, 1, 4, 4, 2, 2]
def baseStart_670436 : Nat := 118140960795 + 670436 * 2 ^ 59
def prefixEnd_670436 : Nat := 4983230072969 + 3 ^ 40 * 670436 * 2
def baseEnd_670436 : Nat := 306005258735861466459313

theorem tailTrace_670436 : CollatzResearch.WordTrace tailWord_670436 prefixEnd_670436 306005258735861466459313 := by
  unfold tailWord_670436
  simp only [CollatzResearch.WordTrace]
  refine ⟨12226404899566174098995581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16301873199421565465327441 12226404899566174098995581)
  ·
    refine ⟨4584901837337315287123343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12226404899566174098995581 4584901837337315287123343)
    ·
      refine ⟨6877352756005972930685015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4584901837337315287123343 6877352756005972930685015)
      ·
        refine ⟨10316029134008959396027523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6877352756005972930685015 10316029134008959396027523)
        ·
          refine ⟨15474043701013439094041285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10316029134008959396027523 15474043701013439094041285)
          ·
            refine ⟨2901383193940019830132741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15474043701013439094041285 2901383193940019830132741)
            ·
              refine ⟨544009348863753718149889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2901383193940019830132741 544009348863753718149889)
              ·
                refine ⟨408007011647815288612417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 544009348863753718149889 408007011647815288612417)
                ·
                  refine ⟨306005258735861466459313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 408007011647815288612417 306005258735861466459313)
                  ·
                    rfl

theorem cell20_670436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 4, 2, 2].length) (baseStart_670436 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_670436 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_670436 prefixEnd_670436 := by exact prefixLift 670436
  have htrace : WordTrace (prefixWord ++ tailWord_670436) baseStart_670436 baseEnd_670436 := by
    simpa [prefixWord, tailWord_670436, baseEnd_670436] using wordTrace_append hprefix tailTrace_670436
  have hstable : (prefixWord ++ tailWord_670436).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_670436).length < 2 ^ (prefixWord ++ tailWord_670436).sum := by decide
  have hdescent : baseEnd_670436 < baseStart_670436 := by decide
  rcases family_descends (prefixWord ++ tailWord_670436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_670447 : List Nat := [1, 1, 2, 1, 5, 2, 3, 5]
def baseStart_670447 : Nat := 118140960795 + 670447 * 2 ^ 59
def prefixEnd_670447 : Nat := 4983230072969 + 3 ^ 40 * 670447 * 2
def baseEnd_670447 : Nat := 102003426478531439030867

theorem tailTrace_670447 : CollatzResearch.WordTrace tailWord_670447 prefixEnd_670447 102003426478531439030867 := by
  unfold tailWord_670447
  simp only [CollatzResearch.WordTrace]
  refine ⟨24453211002092497076641595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16302140668061664717761063 24453211002092497076641595)
  ·
    refine ⟨36679816503138745614962393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24453211002092497076641595 36679816503138745614962393)
    ·
      refine ⟨27509862377354059211221795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36679816503138745614962393 27509862377354059211221795)
      ·
        refine ⟨41264793566031088816832693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27509862377354059211221795 41264793566031088816832693)
        ·
          refine ⟨3868574396815414576578065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 41264793566031088816832693 3868574396815414576578065)
          ·
            refine ⟨2901430797611560932433549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3868574396815414576578065 2901430797611560932433549)
            ·
              refine ⟨1088036549104335349662581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2901430797611560932433549 1088036549104335349662581)
              ·
                refine ⟨102003426478531439030867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1088036549104335349662581 102003426478531439030867)
                ·
                  rfl

theorem cell20_670447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 3, 5].length) (baseStart_670447 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_670447 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_670447 prefixEnd_670447 := by exact prefixLift 670447
  have htrace : WordTrace (prefixWord ++ tailWord_670447) baseStart_670447 baseEnd_670447 := by
    simpa [prefixWord, tailWord_670447, baseEnd_670447] using wordTrace_append hprefix tailTrace_670447
  have hstable : (prefixWord ++ tailWord_670447).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_670447).length < 2 ^ (prefixWord ++ tailWord_670447).sum := by decide
  have hdescent : baseEnd_670447 < baseStart_670447 := by decide
  rcases family_descends (prefixWord ++ tailWord_670447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_670453 : List Nat := [1, 3, 6, 1, 1, 1, 1, 2, 4]
def baseStart_670453 : Nat := 118140960795 + 670453 * 2 ^ 59
def prefixEnd_670453 : Nat := 4983230072969 + 3 ^ 40 * 670453 * 2
def baseEnd_670453 : Nat := 306013017999084962892577

theorem tailTrace_670453 : CollatzResearch.WordTrace tailWord_670453 prefixEnd_670453 306013017999084962892577 := by
  unfold tailWord_670453
  simp only [CollatzResearch.WordTrace]
  refine ⟨24453429840070760101360013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16302286560047173400906675 24453429840070760101360013)
  ·
    refine ⟨9170036190026535038010005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24453429840070760101360013 9170036190026535038010005)
    ·
      refine ⟨429845446407493829906719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 9170036190026535038010005 429845446407493829906719)
      ·
        refine ⟨644768169611240744860079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 429845446407493829906719 644768169611240744860079)
        ·
          refine ⟨967152254416861117290119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 644768169611240744860079 967152254416861117290119)
          ·
            refine ⟨1450728381625291675935179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 967152254416861117290119 1450728381625291675935179)
            ·
              refine ⟨2176092572437937513902769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1450728381625291675935179 2176092572437937513902769)
              ·
                refine ⟨1632069429328453135427077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2176092572437937513902769 1632069429328453135427077)
                ·
                  refine ⟨306013017999084962892577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1632069429328453135427077 306013017999084962892577)
                  ·
                    rfl

theorem cell20_670453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 1, 1, 2, 4].length) (baseStart_670453 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_670453 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_670453 prefixEnd_670453 := by exact prefixLift 670453
  have htrace : WordTrace (prefixWord ++ tailWord_670453) baseStart_670453 baseEnd_670453 := by
    simpa [prefixWord, tailWord_670453, baseEnd_670453] using wordTrace_append hprefix tailTrace_670453
  have hstable : (prefixWord ++ tailWord_670453).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_670453).length < 2 ^ (prefixWord ++ tailWord_670453).sum := by decide
  have hdescent : baseEnd_670453 < baseStart_670453 := by decide
  rcases family_descends (prefixWord ++ tailWord_670453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_670495 : List Nat := [1, 1, 2, 4, 2, 2, 2, 4, 2]
def baseStart_670495 : Nat := 118140960795 + 670495 * 2 ^ 59
def prefixEnd_670495 : Nat := 4983230072969 + 3 ^ 40 * 670495 * 2
def baseEnd_670495 : Nat := 306032187943519483492405

theorem tailTrace_670495 : CollatzResearch.WordTrace tailWord_670495 prefixEnd_670495 306032187943519483492405 := by
  unfold tailWord_670495
  simp only [CollatzResearch.WordTrace]
  refine ⟨24454961705918601274388939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16303307803945734182925959 24454961705918601274388939)
  ·
    refine ⟨36682442558877901911583409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24454961705918601274388939 36682442558877901911583409)
    ·
      refine ⟨27511831919158426433687557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36682442558877901911583409 27511831919158426433687557)
      ·
        refine ⟨5158468484842204956316417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 27511831919158426433687557 5158468484842204956316417)
        ·
          refine ⟨3868851363631653717237313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5158468484842204956316417 3868851363631653717237313)
          ·
            refine ⟨2901638522723740287927985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3868851363631653717237313 2901638522723740287927985)
            ·
              refine ⟨2176228892042805215945989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2901638522723740287927985 2176228892042805215945989)
              ·
                refine ⟨408042917258025977989873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2176228892042805215945989 408042917258025977989873)
                ·
                  refine ⟨306032187943519483492405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 408042917258025977989873 306032187943519483492405)
                  ·
                    rfl

theorem cell20_670495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 2, 4, 2].length) (baseStart_670495 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_670495 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_670495 prefixEnd_670495 := by exact prefixLift 670495
  have htrace : WordTrace (prefixWord ++ tailWord_670495) baseStart_670495 baseEnd_670495 := by
    simpa [prefixWord, tailWord_670495, baseEnd_670495] using wordTrace_append hprefix tailTrace_670495
  have hstable : (prefixWord ++ tailWord_670495).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_670495).length < 2 ^ (prefixWord ++ tailWord_670495).sum := by decide
  have hdescent : baseEnd_670495 < baseStart_670495 := by decide
  rcases family_descends (prefixWord ++ tailWord_670495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_670544 : List Nat := [2, 1, 1, 1, 1, 4, 10]
def baseStart_670544 : Nat := 118140960795 + 670544 * 2 ^ 59
def prefixEnd_670544 : Nat := 4983230072969 + 3 ^ 40 * 670544 * 2
def baseEnd_670544 : Nat := 34006061430965898984319

theorem tailTrace_670544 : CollatzResearch.WordTrace tailWord_670544 prefixEnd_670544 34006061430965898984319 := by
  unfold tailWord_670544
  simp only [CollatzResearch.WordTrace]
  refine ⟨12228374441370541321461343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16304499255160721761948457 12228374441370541321461343)
  ·
    refine ⟨18342561662055811982192015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12228374441370541321461343 18342561662055811982192015)
    ·
      refine ⟨27513842493083717973288023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18342561662055811982192015 27513842493083717973288023)
      ·
        refine ⟨41270763739625576959932035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27513842493083717973288023 41270763739625576959932035)
        ·
          refine ⟨61906145609438365439898053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41270763739625576959932035 61906145609438365439898053)
          ·
            refine ⟨11607402301769693519980885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 61906145609438365439898053 11607402301769693519980885)
            ·
              refine ⟨34006061430965898984319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 11607402301769693519980885 34006061430965898984319)
              ·
                rfl

theorem cell20_670544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 10].length) (baseStart_670544 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_670544 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_670544 prefixEnd_670544 := by exact prefixLift 670544
  have htrace : WordTrace (prefixWord ++ tailWord_670544) baseStart_670544 baseEnd_670544 := by
    simpa [prefixWord, tailWord_670544, baseEnd_670544] using wordTrace_append hprefix tailTrace_670544
  have hstable : (prefixWord ++ tailWord_670544).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_670544).length < 2 ^ (prefixWord ++ tailWord_670544).sum := by decide
  have hdescent : baseEnd_670544 < baseStart_670544 := by decide
  rcases family_descends (prefixWord ++ tailWord_670544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_670554 : List Nat := [3, 1, 1, 2, 1, 4, 3, 1, 4]
def baseStart_670554 : Nat := 118140960795 + 670554 * 2 ^ 59
def prefixEnd_670554 : Nat := 4983230072969 + 3 ^ 40 * 670554 * 2
def baseEnd_670554 : Nat := 306059117151177500525497

theorem tailTrace_670554 : CollatzResearch.WordTrace tailWord_670554 prefixEnd_670554 306059117151177500525497 := by
  unfold tailWord_670554
  simp only [CollatzResearch.WordTrace]
  refine ⟨6114278403176213587696679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16304742408469902900524477 6114278403176213587696679)
  ·
    refine ⟨9171417604764320381545019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6114278403176213587696679 9171417604764320381545019)
    ·
      refine ⟨13757126407146480572317529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9171417604764320381545019 13757126407146480572317529)
      ·
        refine ⟨10317844805359860429238147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13757126407146480572317529 10317844805359860429238147)
        ·
          refine ⟨15476767208039790643857221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10317844805359860429238147 15476767208039790643857221)
          ·
            refine ⟨2901893851507460745723229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15476767208039790643857221 2901893851507460745723229)
            ·
              refine ⟨1088210194315297779646211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2901893851507460745723229 1088210194315297779646211)
              ·
                refine ⟨1632315291472946669469317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1088210194315297779646211 1632315291472946669469317)
                ·
                  refine ⟨306059117151177500525497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1632315291472946669469317 306059117151177500525497)
                  ·
                    rfl

theorem cell20_670554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 3, 1, 4].length) (baseStart_670554 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_670554 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_670554 prefixEnd_670554 := by exact prefixLift 670554
  have htrace : WordTrace (prefixWord ++ tailWord_670554) baseStart_670554 baseEnd_670554 := by
    simpa [prefixWord, tailWord_670554, baseEnd_670554] using wordTrace_append hprefix tailTrace_670554
  have hstable : (prefixWord ++ tailWord_670554).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_670554).length < 2 ^ (prefixWord ++ tailWord_670554).sum := by decide
  have hdescent : baseEnd_670554 < baseStart_670554 := by decide
  rcases family_descends (prefixWord ++ tailWord_670554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_670564 : List Nat := [2, 3, 1, 1, 4, 1, 4, 1, 3]
def baseStart_670564 : Nat := 118140960795 + 670564 * 2 ^ 59
def prefixEnd_670564 : Nat := 4983230072969 + 3 ^ 40 * 670564 * 2
def baseEnd_670564 : Nat := 306063681423661910192123

theorem tailTrace_670564 : CollatzResearch.WordTrace tailWord_670564 prefixEnd_670564 306063681423661910192123 := by
  unfold tailWord_670564
  simp only [CollatzResearch.WordTrace]
  refine ⟨12228739171334313029325373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16304985561779084039100497 12228739171334313029325373)
  ·
    refine ⟨4585777189250367385997015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12228739171334313029325373 4585777189250367385997015)
    ·
      refine ⟨6878665783875551078995523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4585777189250367385997015 6878665783875551078995523)
      ·
        refine ⟨10317998675813326618493285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6878665783875551078995523 10317998675813326618493285)
        ·
          refine ⟨1934624751714998740967491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10317998675813326618493285 1934624751714998740967491)
          ·
            refine ⟨2901937127572498111451237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1934624751714998740967491 2901937127572498111451237)
            ·
              refine ⟨544113211419843395897107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2901937127572498111451237 544113211419843395897107)
              ·
                refine ⟨816169817129765093845661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 544113211419843395897107 816169817129765093845661)
                ·
                  refine ⟨306063681423661910192123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 816169817129765093845661 306063681423661910192123)
                  ·
                    rfl

theorem cell20_670564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 4, 1, 3].length) (baseStart_670564 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_670564 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_670564 prefixEnd_670564 := by exact prefixLift 670564
  have htrace : WordTrace (prefixWord ++ tailWord_670564) baseStart_670564 baseEnd_670564 := by
    simpa [prefixWord, tailWord_670564, baseEnd_670564] using wordTrace_append hprefix tailTrace_670564
  have hstable : (prefixWord ++ tailWord_670564).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_670564).length < 2 ^ (prefixWord ++ tailWord_670564).sum := by decide
  have hdescent : baseEnd_670564 < baseStart_670564 := by decide
  rcases family_descends (prefixWord ++ tailWord_670564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_670575 : List Nat := [1, 1, 2, 1, 3, 1, 1, 6, 4]
def baseStart_670575 : Nat := 118140960795 + 670575 * 2 ^ 59
def prefixEnd_670575 : Nat := 4983230072969 + 3 ^ 40 * 670575 * 2
def baseEnd_670575 : Nat := 306068702123394760825411

theorem tailTrace_670575 : CollatzResearch.WordTrace tailWord_670575 prefixEnd_670575 306068702123394760825411 := by
  unfold tailWord_670575
  simp only [CollatzResearch.WordTrace]
  refine ⟨24457879545628774937301179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16305253030419183291534119 24457879545628774937301179)
  ·
    refine ⟨36686819318443162405951769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24457879545628774937301179 36686819318443162405951769)
    ·
      refine ⟨27515114488832371804463827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36686819318443162405951769 27515114488832371804463827)
      ·
        refine ⟨41272671733248557706695741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27515114488832371804463827 41272671733248557706695741)
        ·
          refine ⟨15477251899968209140010903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41272671733248557706695741 15477251899968209140010903)
          ·
            refine ⟨23215877849952313710016355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15477251899968209140010903 23215877849952313710016355)
            ·
              refine ⟨34823816774928470565024533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23215877849952313710016355 34823816774928470565024533)
              ·
                refine ⟨1632366411324772057735525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 34823816774928470565024533 1632366411324772057735525)
                ·
                  refine ⟨306068702123394760825411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1632366411324772057735525 306068702123394760825411)
                  ·
                    rfl

theorem cell20_670575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 6, 4].length) (baseStart_670575 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_670575 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_670575 prefixEnd_670575 := by exact prefixLift 670575
  have htrace : WordTrace (prefixWord ++ tailWord_670575) baseStart_670575 baseEnd_670575 := by
    simpa [prefixWord, tailWord_670575, baseEnd_670575] using wordTrace_append hprefix tailTrace_670575
  have hstable : (prefixWord ++ tailWord_670575).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_670575).length < 2 ^ (prefixWord ++ tailWord_670575).sum := by decide
  have hdescent : baseEnd_670575 < baseStart_670575 := by decide
  rcases family_descends (prefixWord ++ tailWord_670575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_670602 : List Nat := [3, 1, 2, 4, 1, 2, 2, 2, 3]
def baseStart_670602 : Nat := 118140960795 + 670602 * 2 ^ 59
def prefixEnd_670602 : Nat := 4983230072969 + 3 ^ 40 * 670602 * 2
def baseEnd_670602 : Nat := 306081025659102666925301

theorem tailTrace_670602 : CollatzResearch.WordTrace tailWord_670602 prefixEnd_670602 306081025659102666925301 := by
  unfold tailWord_670602
  simp only [CollatzResearch.WordTrace]
  refine ⟨6114716079132739637133515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16305909544353972365689373 6114716079132739637133515)
  ·
    refine ⟨9172074118699109455700273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6114716079132739637133515 9172074118699109455700273)
    ·
      refine ⟨6879055589024332091775205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9172074118699109455700273 6879055589024332091775205)
      ·
        refine ⟨1289822922942062267207851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6879055589024332091775205 1289822922942062267207851)
        ·
          refine ⟨1934734384413093400811777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1289822922942062267207851 1934734384413093400811777)
          ·
            refine ⟨1451050788309820050608833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1934734384413093400811777 1451050788309820050608833)
            ·
              refine ⟨1088288091232365037956625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1451050788309820050608833 1088288091232365037956625)
              ·
                refine ⟨816216068424273778467469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1088288091232365037956625 816216068424273778467469)
                ·
                  refine ⟨306081025659102666925301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 816216068424273778467469 306081025659102666925301)
                  ·
                    rfl

theorem cell20_670602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 2, 2, 2, 3].length) (baseStart_670602 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_670602 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_670602 prefixEnd_670602 := by exact prefixLift 670602
  have htrace : WordTrace (prefixWord ++ tailWord_670602) baseStart_670602 baseEnd_670602 := by
    simpa [prefixWord, tailWord_670602, baseEnd_670602] using wordTrace_append hprefix tailTrace_670602
  have hstable : (prefixWord ++ tailWord_670602).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_670602).length < 2 ^ (prefixWord ++ tailWord_670602).sum := by decide
  have hdescent : baseEnd_670602 < baseStart_670602 := by decide
  rcases family_descends (prefixWord ++ tailWord_670602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_670623 : List Nat := [1, 1, 2, 5, 2, 1, 2, 3, 3]
def baseStart_670623 : Nat := 118140960795 + 670623 * 2 ^ 59
def prefixEnd_670623 : Nat := 4983230072969 + 3 ^ 40 * 670623 * 2
def baseEnd_670623 : Nat := 306090610631319927225215

theorem tailTrace_670623 : CollatzResearch.WordTrace tailWord_670623 prefixEnd_670623 306090610631319927225215 := by
  unfold tailWord_670623
  simp only [CollatzResearch.WordTrace]
  refine ⟨24459630249454879135048523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16306420166303252756699015 24459630249454879135048523)
  ·
    refine ⟨36689445374182318702572785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24459630249454879135048523 36689445374182318702572785)
    ·
      refine ⟨27517084030636739026929589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36689445374182318702572785 27517084030636739026929589)
      ·
        refine ⟨2579726627872194283774649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 27517084030636739026929589 2579726627872194283774649)
        ·
          refine ⟨1934794970904145712830987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2579726627872194283774649 1934794970904145712830987)
          ·
            refine ⟨2902192456356218569246481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1934794970904145712830987 2902192456356218569246481)
            ·
              refine ⟨2176644342267163926934861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2902192456356218569246481 2176644342267163926934861)
              ·
                refine ⟨816241628350186472600573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2176644342267163926934861 816241628350186472600573)
                ·
                  refine ⟨306090610631319927225215, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 816241628350186472600573 306090610631319927225215)
                  ·
                    rfl

theorem cell20_670623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 2, 3, 3].length) (baseStart_670623 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_670623 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_670623 prefixEnd_670623 := by exact prefixLift 670623
  have htrace : WordTrace (prefixWord ++ tailWord_670623) baseStart_670623 baseEnd_670623 := by
    simpa [prefixWord, tailWord_670623, baseEnd_670623] using wordTrace_append hprefix tailTrace_670623
  have hstable : (prefixWord ++ tailWord_670623).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_670623).length < 2 ^ (prefixWord ++ tailWord_670623).sum := by decide
  have hdescent : baseEnd_670623 < baseStart_670623 := by decide
  rcases family_descends (prefixWord ++ tailWord_670623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_670668 : List Nat := [2, 2, 1, 4, 1, 1, 4, 1, 4]
def baseStart_670668 : Nat := 118140960795 + 670668 * 2 ^ 59
def prefixEnd_670668 : Nat := 4983230072969 + 3 ^ 40 * 670668 * 2
def baseEnd_670668 : Nat := 306111149857499770725031

theorem tailTrace_670668 : CollatzResearch.WordTrace tailWord_670668 prefixEnd_670668 306111149857499770725031 := by
  unfold tailWord_670668
  simp only [CollatzResearch.WordTrace]
  refine ⟨12230635767145925910218329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16307514356194567880291105 12230635767145925910218329)
  ·
    refine ⟨9172976825359444432663747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12230635767145925910218329 9172976825359444432663747)
    ·
      refine ⟨13759465238039166648995621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9172976825359444432663747 13759465238039166648995621)
      ·
        refine ⟨2579899732132343746686679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13759465238039166648995621 2579899732132343746686679)
        ·
          refine ⟨3869849598198515620030019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2579899732132343746686679 3869849598198515620030019)
          ·
            refine ⟨5804774397297773430045029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3869849598198515620030019 5804774397297773430045029)
            ·
              refine ⟨1088395199493332518133443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5804774397297773430045029 1088395199493332518133443)
              ·
                refine ⟨1632592799239998777200165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1088395199493332518133443 1632592799239998777200165)
                ·
                  refine ⟨306111149857499770725031, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1632592799239998777200165 306111149857499770725031)
                  ·
                    rfl

theorem cell20_670668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 4, 1, 4].length) (baseStart_670668 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_670668 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_670668 prefixEnd_670668 := by exact prefixLift 670668
  have htrace : WordTrace (prefixWord ++ tailWord_670668) baseStart_670668 baseEnd_670668 := by
    simpa [prefixWord, tailWord_670668, baseEnd_670668] using wordTrace_append hprefix tailTrace_670668
  have hstable : (prefixWord ++ tailWord_670668).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_670668).length < 2 ^ (prefixWord ++ tailWord_670668).sum := by decide
  have hdescent : baseEnd_670668 < baseStart_670668 := by decide
  rcases family_descends (prefixWord ++ tailWord_670668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_670709 : List Nat := [1, 3, 5, 2, 1, 2, 6]
def baseStart_670709 : Nat := 118140960795 + 670709 * 2 ^ 59
def prefixEnd_670709 : Nat := 4983230072969 + 3 ^ 40 * 670709 * 2
def baseEnd_670709 : Nat := 34014429263853983373133

theorem tailTrace_670709 : CollatzResearch.WordTrace tailWord_670709 prefixEnd_670709 34014429263853983373133 := by
  unfold tailWord_670709
  simp only [CollatzResearch.WordTrace]
  refine ⟨24462766927143315822679181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16308511284762210548452787 24462766927143315822679181)
  ·
    refine ⟨9173537597678743433504693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24462766927143315822679181 9173537597678743433504693)
    ·
      refine ⟨860019149782382196891065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 9173537597678743433504693 860019149782382196891065)
      ·
        refine ⟨645014362336786647668299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 860019149782382196891065 645014362336786647668299)
        ·
          refine ⟨967521543505179971502449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 645014362336786647668299 967521543505179971502449)
          ·
            refine ⟨725641157628884978626837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 967521543505179971502449 725641157628884978626837)
            ·
              refine ⟨34014429263853983373133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 725641157628884978626837 34014429263853983373133)
              ·
                rfl

theorem cell20_670709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 2, 6].length) (baseStart_670709 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_670709 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_670709 prefixEnd_670709 := by exact prefixLift 670709
  have htrace : WordTrace (prefixWord ++ tailWord_670709) baseStart_670709 baseEnd_670709 := by
    simpa [prefixWord, tailWord_670709, baseEnd_670709] using wordTrace_append hprefix tailTrace_670709
  have hstable : (prefixWord ++ tailWord_670709).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_670709).length < 2 ^ (prefixWord ++ tailWord_670709).sum := by decide
  have hdescent : baseEnd_670709 < baseStart_670709 := by decide
  rcases family_descends (prefixWord ++ tailWord_670709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_670785 : List Nat := [1, 2, 5, 1, 4, 1, 1, 5]
def baseStart_670785 : Nat := 118140960795 + 670785 * 2 ^ 59
def prefixEnd_670785 : Nat := 4983230072969 + 3 ^ 40 * 670785 * 2
def baseEnd_670785 : Nat := 102054850615189121274851

theorem tailTrace_670785 : CollatzResearch.WordTrace tailWord_670785 prefixEnd_670785 102054850615189121274851 := by
  unfold tailWord_670785
  simp only [CollatzResearch.WordTrace]
  refine ⟨24465538874867980802445809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16310359249911987201630539 24465538874867980802445809)
  ·
    refine ⟨18349154156150985601834357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24465538874867980802445809 18349154156150985601834357)
    ·
      refine ⟨1720233202139154900171971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 18349154156150985601834357 1720233202139154900171971)
      ·
        refine ⟨2580349803208732350257957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1720233202139154900171971 2580349803208732350257957)
        ·
          refine ⟨483815588101637315673367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2580349803208732350257957 483815588101637315673367)
          ·
            refine ⟨725723382152455973510051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 483815588101637315673367 725723382152455973510051)
            ·
              refine ⟨1088585073228683960265077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 725723382152455973510051 1088585073228683960265077)
              ·
                refine ⟨102054850615189121274851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1088585073228683960265077 102054850615189121274851)
                ·
                  rfl

theorem cell20_670785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 4, 1, 1, 5].length) (baseStart_670785 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_670785 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_670785 prefixEnd_670785 := by exact prefixLift 670785
  have htrace : WordTrace (prefixWord ++ tailWord_670785) baseStart_670785 baseEnd_670785 := by
    simpa [prefixWord, tailWord_670785, baseEnd_670785] using wordTrace_append hprefix tailTrace_670785
  have hstable : (prefixWord ++ tailWord_670785).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_670785).length < 2 ^ (prefixWord ++ tailWord_670785).sum := by decide
  have hdescent : baseEnd_670785 < baseStart_670785 := by decide
  rcases family_descends (prefixWord ++ tailWord_670785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_670830 : List Nat := [4, 1, 2, 2, 1, 4, 1, 2, 3]
def baseStart_670830 : Nat := 118140960795 + 670830 * 2 ^ 59
def prefixEnd_670830 : Nat := 4983230072969 + 3 ^ 40 * 670830 * 2
def baseEnd_670830 : Nat := 306185091071747207324369

theorem tailTrace_670830 : CollatzResearch.WordTrace tailWord_670830 prefixEnd_670830 306185091071747207324369 := by
  unfold tailWord_670830
  simp only [CollatzResearch.WordTrace]
  refine ⟨3058397519963119185979243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16311453439803302325222629 3058397519963119185979243)
  ·
    refine ⟨4587596279944678778968865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3058397519963119185979243 4587596279944678778968865)
    ·
      refine ⟨3440697209958509084226649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4587596279944678778968865 3440697209958509084226649)
      ·
        refine ⟨2580522907468881813169987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3440697209958509084226649 2580522907468881813169987)
        ·
          refine ⟨3870784361203322719754981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2580522907468881813169987 3870784361203322719754981)
          ·
            refine ⟨725772067725623009954059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3870784361203322719754981 725772067725623009954059)
            ·
              refine ⟨1088658101588434514931089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 725772067725623009954059 1088658101588434514931089)
              ·
                refine ⟨816493576191325886198317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1088658101588434514931089 816493576191325886198317)
                ·
                  refine ⟨306185091071747207324369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 816493576191325886198317 306185091071747207324369)
                  ·
                    rfl

theorem cell20_670830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 4, 1, 2, 3].length) (baseStart_670830 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_670830 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_670830 prefixEnd_670830 := by exact prefixLift 670830
  have htrace : WordTrace (prefixWord ++ tailWord_670830) baseStart_670830 baseEnd_670830 := by
    simpa [prefixWord, tailWord_670830, baseEnd_670830] using wordTrace_append hprefix tailTrace_670830
  have hstable : (prefixWord ++ tailWord_670830).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_670830).length < 2 ^ (prefixWord ++ tailWord_670830).sum := by decide
  have hdescent : baseEnd_670830 < baseStart_670830 := by decide
  rcases family_descends (prefixWord ++ tailWord_670830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_670834 : List Nat := [3, 2, 1, 2, 2, 1, 3, 1, 5]
def baseStart_670834 : Nat := 118140960795 + 670834 * 2 ^ 59
def prefixEnd_670834 : Nat := 4983230072969 + 3 ^ 40 * 670834 * 2
def baseEnd_670834 : Nat := 306186916780740971191019

theorem tailTrace_670834 : CollatzResearch.WordTrace tailWord_670834 prefixEnd_670834 306186916780740971191019 := by
  unfold tailWord_670834
  simp only [CollatzResearch.WordTrace]
  refine ⟨6116831512922615542744889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16311550701126974780653037 6116831512922615542744889)
  ·
    refine ⟨4587623634691961657058667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6116831512922615542744889 4587623634691961657058667)
    ·
      refine ⟨6881435452037942485588001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4587623634691961657058667 6881435452037942485588001)
      ·
        refine ⟨5161076589028456864191001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6881435452037942485588001 5161076589028456864191001)
        ·
          refine ⟨3870807441771342648143251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5161076589028456864191001 3870807441771342648143251)
          ·
            refine ⟨5806211162657013972214877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3870807441771342648143251 5806211162657013972214877)
            ·
              refine ⟨2177329185996380239580579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5806211162657013972214877 2177329185996380239580579)
              ·
                refine ⟨3265993778994570359370869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2177329185996380239580579 3265993778994570359370869)
                ·
                  refine ⟨306186916780740971191019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3265993778994570359370869 306186916780740971191019)
                  ·
                    rfl

theorem cell20_670834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 3, 1, 5].length) (baseStart_670834 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_670834 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_670834 prefixEnd_670834 := by exact prefixLift 670834
  have htrace : WordTrace (prefixWord ++ tailWord_670834) baseStart_670834 baseEnd_670834 := by
    simpa [prefixWord, tailWord_670834, baseEnd_670834] using wordTrace_append hprefix tailTrace_670834
  have hstable : (prefixWord ++ tailWord_670834).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_670834).length < 2 ^ (prefixWord ++ tailWord_670834).sum := by decide
  have hdescent : baseEnd_670834 < baseStart_670834 := by decide
  rcases family_descends (prefixWord ++ tailWord_670834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_670851 : List Nat := [1, 1, 1, 3, 3, 2, 5, 1, 3]
def baseStart_670851 : Nat := 118140960795 + 670851 * 2 ^ 59
def prefixEnd_670851 : Nat := 4983230072969 + 3 ^ 40 * 670851 * 2
def baseEnd_670851 : Nat := 306194676043964467624283

theorem tailTrace_670851 : CollatzResearch.WordTrace tailWord_670851 prefixEnd_670851 306194676043964467624283 := by
  unfold tailWord_670851
  simp only [CollatzResearch.WordTrace]
  refine ⟨24467946092628874074348407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16311964061752582716232271 24467946092628874074348407)
  ·
    refine ⟨36701919138943311111522611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24467946092628874074348407 36701919138943311111522611)
    ·
      refine ⟨55052878708414966667283917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36701919138943311111522611 55052878708414966667283917)
      ·
        refine ⟨20644829515655612500231469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55052878708414966667283917 20644829515655612500231469)
        ·
          refine ⟨7741811068370854687586801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20644829515655612500231469 7741811068370854687586801)
          ·
            refine ⟨5806358301278141015690101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7741811068370854687586801 5806358301278141015690101)
            ·
              refine ⟨544346090744825720220947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5806358301278141015690101 544346090744825720220947)
              ·
                refine ⟨816519136117238580331421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 544346090744825720220947 816519136117238580331421)
                ·
                  refine ⟨306194676043964467624283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 816519136117238580331421 306194676043964467624283)
                  ·
                    rfl

theorem cell20_670851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 5, 1, 3].length) (baseStart_670851 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_670851 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_670851 prefixEnd_670851 := by exact prefixLift 670851
  have htrace : WordTrace (prefixWord ++ tailWord_670851) baseStart_670851 baseEnd_670851 := by
    simpa [prefixWord, tailWord_670851, baseEnd_670851] using wordTrace_append hprefix tailTrace_670851
  have hstable : (prefixWord ++ tailWord_670851).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_670851).length < 2 ^ (prefixWord ++ tailWord_670851).sum := by decide
  have hdescent : baseEnd_670851 < baseStart_670851 := by decide
  rcases family_descends (prefixWord ++ tailWord_670851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_670872 : List Nat := [2, 1, 2, 4, 2, 1, 1, 2, 5]
def baseStart_670872 : Nat := 118140960795 + 670872 * 2 ^ 59
def prefixEnd_670872 : Nat := 4983230072969 + 3 ^ 40 * 670872 * 2
def baseEnd_670872 : Nat := 306204261016181727924197

theorem tailTrace_670872 : CollatzResearch.WordTrace tailWord_670872 prefixEnd_670872 306204261016181727924197 := by
  unfold tailWord_670872
  simp only [CollatzResearch.WordTrace]
  refine ⟨12234356012776397330431435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16312474683701863107241913 12234356012776397330431435)
  ·
    refine ⟨18351534019164595995647153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12234356012776397330431435 18351534019164595995647153)
    ·
      refine ⟨13763650514373446996735365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18351534019164595995647153 13763650514373446996735365)
      ·
        refine ⟨2580684471445021311887881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13763650514373446996735365 2580684471445021311887881)
        ·
          refine ⟨1935513353583765983915911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2580684471445021311887881 1935513353583765983915911)
          ·
            refine ⟨2903270030375648975873867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1935513353583765983915911 2903270030375648975873867)
            ·
              refine ⟨4354905045563473463810801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2903270030375648975873867 4354905045563473463810801)
              ·
                refine ⟨3266178784172605097858101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4354905045563473463810801 3266178784172605097858101)
                ·
                  refine ⟨306204261016181727924197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3266178784172605097858101 306204261016181727924197)
                  ·
                    rfl

theorem cell20_670872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 1, 2, 5].length) (baseStart_670872 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_670872 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_670872 prefixEnd_670872 := by exact prefixLift 670872
  have htrace : WordTrace (prefixWord ++ tailWord_670872) baseStart_670872 baseEnd_670872 := by
    simpa [prefixWord, tailWord_670872, baseEnd_670872] using wordTrace_append hprefix tailTrace_670872
  have hstable : (prefixWord ++ tailWord_670872).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_670872).length < 2 ^ (prefixWord ++ tailWord_670872).sum := by decide
  have hdescent : baseEnd_670872 < baseStart_670872 := by decide
  rcases family_descends (prefixWord ++ tailWord_670872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_670882 : List Nat := [3, 3, 1, 3, 2, 2, 6]
def baseStart_670882 : Nat := 118140960795 + 670882 * 2 ^ 59
def prefixEnd_670882 : Nat := 4983230072969 + 3 ^ 40 * 670882 * 2
def baseEnd_670882 : Nat := 34023202809851793065647

theorem tailTrace_670882 : CollatzResearch.WordTrace tailWord_670882 prefixEnd_670882 34023202809851793065647 := by
  unfold tailWord_670882
  simp only [CollatzResearch.WordTrace]
  refine ⟨6117269188879141592181725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16312717837011044245817933 6117269188879141592181725)
  ·
    refine ⟨2293975945829678097068147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6117269188879141592181725 2293975945829678097068147)
    ·
      refine ⟨3440963918744517145602221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2293975945829678097068147 3440963918744517145602221)
      ·
        refine ⟨1290361469529193929600833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3440963918744517145602221 1290361469529193929600833)
        ·
          refine ⟨967771102146895447200625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1290361469529193929600833 967771102146895447200625)
          ·
            refine ⟨725828326610171585400469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 967771102146895447200625 725828326610171585400469)
            ·
              refine ⟨34023202809851793065647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 725828326610171585400469 34023202809851793065647)
              ·
                rfl

theorem cell20_670882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 2, 6].length) (baseStart_670882 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_670882 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_670882 prefixEnd_670882 := by exact prefixLift 670882
  have htrace : WordTrace (prefixWord ++ tailWord_670882) baseStart_670882 baseEnd_670882 := by
    simpa [prefixWord, tailWord_670882, baseEnd_670882] using wordTrace_append hprefix tailTrace_670882
  have hstable : (prefixWord ++ tailWord_670882).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_670882).length < 2 ^ (prefixWord ++ tailWord_670882).sum := by decide
  have hdescent : baseEnd_670882 < baseStart_670882 := by decide
  rcases family_descends (prefixWord ++ tailWord_670882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_670941 : List Nat := [1, 4, 3, 2, 2, 8]
def baseStart_670941 : Nat := 118140960795 + 670941 * 2 ^ 59
def prefixEnd_670941 : Nat := 4983230072969 + 3 ^ 40 * 670941 * 2
def baseEnd_670941 : Nat := 11342064981345339060145

theorem tailTrace_670941 : CollatzResearch.WordTrace tailWord_670941 prefixEnd_670941 11342064981345339060145 := by
  unfold tailWord_670941
  simp only [CollatzResearch.WordTrace]
  refine ⟨24471228662302819445124677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16314152441535212963416451 24471228662302819445124677)
  ·
    refine ⟨4588355374181778645960877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24471228662302819445124677 4588355374181778645960877)
    ·
      refine ⟨1720633265318166992235329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4588355374181778645960877 1720633265318166992235329)
      ·
        refine ⟨1290474948988625244176497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1720633265318166992235329 1290474948988625244176497)
        ·
          refine ⟨967856211741468933132373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1290474948988625244176497 967856211741468933132373)
          ·
            refine ⟨11342064981345339060145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 967856211741468933132373 11342064981345339060145)
            ·
              rfl

theorem cell20_670941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 8].length) (baseStart_670941 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_670941 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_670941 prefixEnd_670941 := by exact prefixLift 670941
  have htrace : WordTrace (prefixWord ++ tailWord_670941) baseStart_670941 baseEnd_670941 := by
    simpa [prefixWord, tailWord_670941, baseEnd_670941] using wordTrace_append hprefix tailTrace_670941
  have hstable : (prefixWord ++ tailWord_670941).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_670941).length < 2 ^ (prefixWord ++ tailWord_670941).sum := by decide
  have hdescent : baseEnd_670941 < baseStart_670941 := by decide
  rcases family_descends (prefixWord ++ tailWord_670941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_670948 : List Nat := [2, 3, 1, 1, 1, 2, 3, 4, 3]
def baseStart_670948 : Nat := 118140960795 + 670948 * 2 ^ 59
def prefixEnd_670948 : Nat := 4983230072969 + 3 ^ 40 * 670948 * 2
def baseEnd_670948 : Nat := 306238949487063241390553

theorem tailTrace_670948 : CollatzResearch.WordTrace tailWord_670948 prefixEnd_670948 306238949487063241390553 := by
  unfold tailWord_670948
  simp only [CollatzResearch.WordTrace]
  refine ⟨12235741986638729820314749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16314322648851639760419665 12235741986638729820314749)
  ·
    refine ⟨4588403244989523682618031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12235741986638729820314749 4588403244989523682618031)
    ·
      refine ⟨6882604867484285523927047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4588403244989523682618031 6882604867484285523927047)
      ·
        refine ⟨10323907301226428285890571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6882604867484285523927047 10323907301226428285890571)
        ·
          refine ⟨15485860951839642428835857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10323907301226428285890571 15485860951839642428835857)
          ·
            refine ⟨11614395713879731821626893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15485860951839642428835857 11614395713879731821626893)
            ·
              refine ⟨4355398392704899433110085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11614395713879731821626893 4355398392704899433110085)
              ·
                refine ⟨816637198632168643708141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4355398392704899433110085 816637198632168643708141)
                ·
                  refine ⟨306238949487063241390553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 816637198632168643708141 306238949487063241390553)
                  ·
                    rfl

theorem cell20_670948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 3, 4, 3].length) (baseStart_670948 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_670948 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_670948 prefixEnd_670948 := by exact prefixLift 670948
  have htrace : WordTrace (prefixWord ++ tailWord_670948) baseStart_670948 baseEnd_670948 := by
    simpa [prefixWord, tailWord_670948, baseEnd_670948] using wordTrace_append hprefix tailTrace_670948
  have hstable : (prefixWord ++ tailWord_670948).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_670948).length < 2 ^ (prefixWord ++ tailWord_670948).sum := by decide
  have hdescent : baseEnd_670948 < baseStart_670948 := by decide
  rcases family_descends (prefixWord ++ tailWord_670948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_670972 : List Nat := [2, 2, 2, 1, 5, 1, 1, 2, 4]
def baseStart_670972 : Nat := 118140960795 + 670972 * 2 ^ 59
def prefixEnd_670972 : Nat := 4983230072969 + 3 ^ 40 * 670972 * 2
def baseEnd_670972 : Nat := 306249903741025824590455

theorem tailTrace_670972 : CollatzResearch.WordTrace tailWord_670972 prefixEnd_670972 306249903741025824590455 := by
  unfold tailWord_670972
  simp only [CollatzResearch.WordTrace]
  refine ⟨12236179662595255869751585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16314906216793674493002113 12236179662595255869751585)
  ·
    refine ⟨9177134746946441902313689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12236179662595255869751585 9177134746946441902313689)
    ·
      refine ⟨6882851060209831426735267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9177134746946441902313689 6882851060209831426735267)
      ·
        refine ⟨10324276590314747140102901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6882851060209831426735267 10324276590314747140102901)
        ·
          refine ⟨967900930342007544384647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 10324276590314747140102901 967900930342007544384647)
          ·
            refine ⟨1451851395513011316576971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 967900930342007544384647 1451851395513011316576971)
            ·
              refine ⟨2177777093269516974865457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1451851395513011316576971 2177777093269516974865457)
              ·
                refine ⟨1633332819952137731149093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2177777093269516974865457 1633332819952137731149093)
                ·
                  refine ⟨306249903741025824590455, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1633332819952137731149093 306249903741025824590455)
                  ·
                    rfl

theorem cell20_670972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 1, 1, 2, 4].length) (baseStart_670972 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_670972 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_670972 prefixEnd_670972 := by exact prefixLift 670972
  have htrace : WordTrace (prefixWord ++ tailWord_670972) baseStart_670972 baseEnd_670972 := by
    simpa [prefixWord, tailWord_670972, baseEnd_670972] using wordTrace_append hprefix tailTrace_670972
  have hstable : (prefixWord ++ tailWord_670972).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_670972).length < 2 ^ (prefixWord ++ tailWord_670972).sum := by decide
  have hdescent : baseEnd_670972 < baseStart_670972 := by decide
  rcases family_descends (prefixWord ++ tailWord_670972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_670979 : List Nat := [1, 1, 1, 3, 2, 5, 3, 4]
def baseStart_670979 : Nat := 118140960795 + 670979 * 2 ^ 59
def prefixEnd_670979 : Nat := 4983230072969 + 3 ^ 40 * 670979 * 2
def baseEnd_670979 : Nat := 102084366243921637119031

theorem tailTrace_670979 : CollatzResearch.WordTrace tailWord_670979 prefixEnd_670979 102084366243921637119031 := by
  unfold tailWord_670979
  simp only [CollatzResearch.WordTrace]
  refine ⟨24472614636165151935007991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16315076424110101290005327 24472614636165151935007991)
  ·
    refine ⟨36708921954247727902511987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24472614636165151935007991 36708921954247727902511987)
    ·
      refine ⟨55063382931371591853767981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36708921954247727902511987 55063382931371591853767981)
      ·
        refine ⟨20648768599264346945162993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55063382931371591853767981 20648768599264346945162993)
        ·
          refine ⟨15486576449448260208872245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20648768599264346945162993 15486576449448260208872245)
          ·
            refine ⟨1451866542135774394581773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 15486576449448260208872245 1451866542135774394581773)
            ·
              refine ⟨544449953300915397968165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1451866542135774394581773 544449953300915397968165)
              ·
                refine ⟨102084366243921637119031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 544449953300915397968165 102084366243921637119031)
                ·
                  rfl

theorem cell20_670979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 5, 3, 4].length) (baseStart_670979 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_670979 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_670979 prefixEnd_670979 := by exact prefixLift 670979
  have htrace : WordTrace (prefixWord ++ tailWord_670979) baseStart_670979 baseEnd_670979 := by
    simpa [prefixWord, tailWord_670979, baseEnd_670979] using wordTrace_append hprefix tailTrace_670979
  have hstable : (prefixWord ++ tailWord_670979).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_670979).length < 2 ^ (prefixWord ++ tailWord_670979).sum := by decide
  have hdescent : baseEnd_670979 < baseStart_670979 := by decide
  rcases family_descends (prefixWord ++ tailWord_670979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_671000 : List Nat := [2, 1, 2, 3, 1, 4, 7]
def baseStart_671000 : Nat := 118140960795 + 671000 * 2 ^ 59
def prefixEnd_671000 : Nat := 4983230072969 + 3 ^ 40 * 671000 * 2
def baseEnd_671000 : Nat := 34029187078220241295223

theorem tailTrace_671000 : CollatzResearch.WordTrace tailWord_671000 prefixEnd_671000 34029187078220241295223 := by
  unfold tailWord_671000
  simp only [CollatzResearch.WordTrace]
  refine ⟨12236690284544536260761227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16315587046059381681014969 12236690284544536260761227)
  ·
    refine ⟨18355035426816804391141841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12236690284544536260761227 18355035426816804391141841)
    ·
      refine ⟨13766276570112603293356381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18355035426816804391141841 13766276570112603293356381)
      ·
        refine ⟨5162353713792226235008643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13766276570112603293356381 5162353713792226235008643)
        ·
          refine ⟨7743530570688339352512965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5162353713792226235008643 7743530570688339352512965)
          ·
            refine ⟨1451911982004063628596181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7743530570688339352512965 1451911982004063628596181)
            ·
              refine ⟨34029187078220241295223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1451911982004063628596181 34029187078220241295223)
              ·
                rfl

theorem cell20_671000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 4, 7].length) (baseStart_671000 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_671000 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_671000 prefixEnd_671000 := by exact prefixLift 671000
  have htrace : WordTrace (prefixWord ++ tailWord_671000) baseStart_671000 baseEnd_671000 := by
    simpa [prefixWord, tailWord_671000, baseEnd_671000] using wordTrace_append hprefix tailTrace_671000
  have hstable : (prefixWord ++ tailWord_671000).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_671000).length < 2 ^ (prefixWord ++ tailWord_671000).sum := by decide
  have hdescent : baseEnd_671000 < baseStart_671000 := by decide
  rcases family_descends (prefixWord ++ tailWord_671000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_671006 : List Nat := [4, 3, 2, 1, 2, 1, 2, 1, 4]
def baseStart_671006 : Nat := 118140960795 + 671006 * 2 ^ 59
def prefixEnd_671006 : Nat := 4983230072969 + 3 ^ 40 * 671006 * 2
def baseEnd_671006 : Nat := 306265422267472817456983

theorem tailTrace_671006 : CollatzResearch.WordTrace tailWord_671006 prefixEnd_671006 306265422267472817456983 := by
  unfold tailWord_671006
  simp only [CollatzResearch.WordTrace]
  refine ⟨3059199925883416943280109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16315732938044890364160581 3059199925883416943280109)
  ·
    refine ⟨1147199972206281353730041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3059199925883416943280109 1147199972206281353730041)
    ·
      refine ⟨860399979154711015297531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1147199972206281353730041 860399979154711015297531)
      ·
        refine ⟨1290599968732066522946297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 860399979154711015297531 1290599968732066522946297)
        ·
          refine ⟨967949976549049892209723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1290599968732066522946297 967949976549049892209723)
          ·
            refine ⟨1451924964823574838314585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 967949976549049892209723 1451924964823574838314585)
            ·
              refine ⟨1088943723617681128735939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1451924964823574838314585 1088943723617681128735939)
              ·
                refine ⟨1633415585426521693103909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1088943723617681128735939 1633415585426521693103909)
                ·
                  refine ⟨306265422267472817456983, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1633415585426521693103909 306265422267472817456983)
                  ·
                    rfl

theorem cell20_671006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 1, 2, 1, 4].length) (baseStart_671006 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_671006 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_671006 prefixEnd_671006 := by exact prefixLift 671006
  have htrace : WordTrace (prefixWord ++ tailWord_671006) baseStart_671006 baseEnd_671006 := by
    simpa [prefixWord, tailWord_671006, baseEnd_671006] using wordTrace_append hprefix tailTrace_671006
  have hstable : (prefixWord ++ tailWord_671006).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_671006).length < 2 ^ (prefixWord ++ tailWord_671006).sum := by decide
  have hdescent : baseEnd_671006 < baseStart_671006 := by decide
  rcases family_descends (prefixWord ++ tailWord_671006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_671030 : List Nat := [5, 1, 2, 3, 1, 2, 2, 4]
def baseStart_671030 : Nat := 118140960795 + 671030 * 2 ^ 59
def prefixEnd_671030 : Nat := 4983230072969 + 3 ^ 40 * 671030 * 2
def baseEnd_671030 : Nat := 102092125507145133552295

theorem tailTrace_671030 : CollatzResearch.WordTrace tailWord_671030 prefixEnd_671030 102092125507145133552295 := by
  unfold tailWord_671030
  simp only [CollatzResearch.WordTrace]
  refine ⟨1529654672436274227819659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 16316316505986925096743029 1529654672436274227819659)
  ·
    refine ⟨2294482008654411341729489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1529654672436274227819659 2294482008654411341729489)
    ·
      refine ⟨1720861506490808506297117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2294482008654411341729489 1720861506490808506297117)
      ·
        refine ⟨645323064934053189861419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1720861506490808506297117 645323064934053189861419)
        ·
          refine ⟨967984597401079784792129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 645323064934053189861419 967984597401079784792129)
          ·
            refine ⟨725988448050809838594097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 967984597401079784792129 725988448050809838594097)
            ·
              refine ⟨544491336038107378945573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 725988448050809838594097 544491336038107378945573)
              ·
                refine ⟨102092125507145133552295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 544491336038107378945573 102092125507145133552295)
                ·
                  rfl

theorem cell20_671030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 2, 2, 4].length) (baseStart_671030 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_671030 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_671030 prefixEnd_671030 := by exact prefixLift 671030
  have htrace : WordTrace (prefixWord ++ tailWord_671030) baseStart_671030 baseEnd_671030 := by
    simpa [prefixWord, tailWord_671030, baseEnd_671030] using wordTrace_append hprefix tailTrace_671030
  have hstable : (prefixWord ++ tailWord_671030).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_671030).length < 2 ^ (prefixWord ++ tailWord_671030).sum := by decide
  have hdescent : baseEnd_671030 < baseStart_671030 := by decide
  rcases family_descends (prefixWord ++ tailWord_671030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_671044 : List Nat := [2, 3, 4, 1, 1, 1, 3, 3, 2]
def baseStart_671044 : Nat := 118140960795 + 671044 * 2 ^ 59
def prefixEnd_671044 : Nat := 4983230072969 + 3 ^ 40 * 671044 * 2
def baseEnd_671044 : Nat := 306282766502913574190161

theorem tailTrace_671044 : CollatzResearch.WordTrace tailWord_671044 prefixEnd_671044 306282766502913574190161 := by
  unfold tailWord_671044
  simp only [CollatzResearch.WordTrace]
  refine ⟨12237492690464834018062093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16316656920619778690749457 12237492690464834018062093)
  ·
    refine ⟨4589059758924312756773285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12237492690464834018062093 4589059758924312756773285)
    ·
      refine ⟨860448704798308641894991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4589059758924312756773285 860448704798308641894991)
      ·
        refine ⟨1290673057197462962842487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 860448704798308641894991 1290673057197462962842487)
        ·
          refine ⟨1936009585796194444263731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1290673057197462962842487 1936009585796194444263731)
          ·
            refine ⟨2904014378694291666395597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1936009585796194444263731 2904014378694291666395597)
            ·
              refine ⟨1089005392010359374898349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2904014378694291666395597 1089005392010359374898349)
              ·
                refine ⟨408377022003884765586881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1089005392010359374898349 408377022003884765586881)
                ·
                  refine ⟨306282766502913574190161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 408377022003884765586881 306282766502913574190161)
                  ·
                    rfl

theorem cell20_671044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 3, 3, 2].length) (baseStart_671044 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_671044 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_671044 prefixEnd_671044 := by exact prefixLift 671044
  have htrace : WordTrace (prefixWord ++ tailWord_671044) baseStart_671044 baseEnd_671044 := by
    simpa [prefixWord, tailWord_671044, baseEnd_671044] using wordTrace_append hprefix tailTrace_671044
  have hstable : (prefixWord ++ tailWord_671044).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_671044).length < 2 ^ (prefixWord ++ tailWord_671044).sum := by decide
  have hdescent : baseEnd_671044 < baseStart_671044 := by decide
  rcases family_descends (prefixWord ++ tailWord_671044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_671076 : List Nat := [2, 3, 1, 1, 3, 2, 1, 7]
def baseStart_671076 : Nat := 118140960795 + 671076 * 2 ^ 59
def prefixEnd_671076 : Nat := 4983230072969 + 3 ^ 40 * 671076 * 2
def baseEnd_671076 : Nat := 102099124058287895041121

theorem tailTrace_671076 : CollatzResearch.WordTrace tailWord_671076 prefixEnd_671076 102099124058287895041121 := by
  unfold tailWord_671076
  simp only [CollatzResearch.WordTrace]
  refine ⟨12238076258406868750644541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16317435011209158334192721 12238076258406868750644541)
  ·
    refine ⟨4589278596902575781491703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12238076258406868750644541 4589278596902575781491703)
    ·
      refine ⟨6883917895353863672237555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4589278596902575781491703 6883917895353863672237555)
      ·
        refine ⟨10325876843030795508356333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6883917895353863672237555 10325876843030795508356333)
        ·
          refine ⟨3872203816136548315633625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10325876843030795508356333 3872203816136548315633625)
          ·
            refine ⟨2904152862102411236725219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3872203816136548315633625 2904152862102411236725219)
            ·
              refine ⟨4356229293153616855087829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2904152862102411236725219 4356229293153616855087829)
              ·
                refine ⟨102099124058287895041121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4356229293153616855087829 102099124058287895041121)
                ·
                  rfl

theorem cell20_671076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 1, 7].length) (baseStart_671076 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_671076 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_671076 prefixEnd_671076 := by exact prefixLift 671076
  have htrace : WordTrace (prefixWord ++ tailWord_671076) baseStart_671076 baseEnd_671076 := by
    simpa [prefixWord, tailWord_671076, baseEnd_671076] using wordTrace_append hprefix tailTrace_671076
  have hstable : (prefixWord ++ tailWord_671076).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_671076).length < 2 ^ (prefixWord ++ tailWord_671076).sum := by decide
  have hdescent : baseEnd_671076 < baseStart_671076 := by decide
  rcases family_descends (prefixWord ++ tailWord_671076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_671079 : List Nat := [1, 1, 5, 1, 4, 1, 1, 3, 3]
def baseStart_671079 : Nat := 118140960795 + 671079 * 2 ^ 59
def prefixEnd_671079 : Nat := 4983230072969 + 3 ^ 40 * 671079 * 2
def baseEnd_671079 : Nat := 306298741456609008023351

theorem tailTrace_671079 : CollatzResearch.WordTrace tailWord_671079 prefixEnd_671079 306298741456609008023351 := by
  unfold tailWord_671079
  simp only [CollatzResearch.WordTrace]
  refine ⟨24476261935802869013648291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16317507957201912675765527 24476261935802869013648291)
  ·
    refine ⟨36714392903704303520472437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24476261935802869013648291 36714392903704303520472437)
    ·
      refine ⟨3441974334722278455044291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 36714392903704303520472437 3441974334722278455044291)
      ·
        refine ⟨5162961502083417682566437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3441974334722278455044291 5162961502083417682566437)
        ·
          refine ⟨968055281640640815481207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5162961502083417682566437 968055281640640815481207)
          ·
            refine ⟨1452082922460961223221811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 968055281640640815481207 1452082922460961223221811)
            ·
              refine ⟨2178124383691441834832717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1452082922460961223221811 2178124383691441834832717)
              ·
                refine ⟨816796643884290688062269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2178124383691441834832717 816796643884290688062269)
                ·
                  refine ⟨306298741456609008023351, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 816796643884290688062269 306298741456609008023351)
                  ·
                    rfl

theorem cell20_671079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 1, 1, 3, 3].length) (baseStart_671079 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_671079 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_671079 prefixEnd_671079 := by exact prefixLift 671079
  have htrace : WordTrace (prefixWord ++ tailWord_671079) baseStart_671079 baseEnd_671079 := by
    simpa [prefixWord, tailWord_671079, baseEnd_671079] using wordTrace_append hprefix tailTrace_671079
  have hstable : (prefixWord ++ tailWord_671079).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_671079).length < 2 ^ (prefixWord ++ tailWord_671079).sum := by decide
  have hdescent : baseEnd_671079 < baseStart_671079 := by decide
  rcases family_descends (prefixWord ++ tailWord_671079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_671159 : List Nat := [1, 1, 3, 1, 3, 2, 2, 2, 5]
def baseStart_671159 : Nat := 118140960795 + 671159 * 2 ^ 59
def prefixEnd_671159 : Nat := 4983230072969 + 3 ^ 40 * 671159 * 2
def baseEnd_671159 : Nat := 306335255636484285356357

theorem tailTrace_671159 : CollatzResearch.WordTrace tailWord_671159 prefixEnd_671159 306335255636484285356357 := by
  unfold tailWord_671159
  simp only [CollatzResearch.WordTrace]
  refine ⟨24479179775513042676560531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16319453183675361784373687 24479179775513042676560531)
  ·
    refine ⟨36718769663269564014840797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24479179775513042676560531 36718769663269564014840797)
    ·
      refine ⟨13769538623726086505565299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36718769663269564014840797 13769538623726086505565299)
      ·
        refine ⟨20654307935589129758347949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13769538623726086505565299 20654307935589129758347949)
        ·
          refine ⟨7745365475845923659380481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20654307935589129758347949 7745365475845923659380481)
          ·
            refine ⟨5809024106884442744535361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7745365475845923659380481 5809024106884442744535361)
            ·
              refine ⟨4356768080163332058401521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5809024106884442744535361 4356768080163332058401521)
              ·
                refine ⟨3267576060122499043801141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4356768080163332058401521 3267576060122499043801141)
                ·
                  refine ⟨306335255636484285356357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3267576060122499043801141 306335255636484285356357)
                  ·
                    rfl

theorem cell20_671159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 2, 2, 5].length) (baseStart_671159 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_671159 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_671159 prefixEnd_671159 := by exact prefixLift 671159
  have htrace : WordTrace (prefixWord ++ tailWord_671159) baseStart_671159 baseEnd_671159 := by
    simpa [prefixWord, tailWord_671159, baseEnd_671159] using wordTrace_append hprefix tailTrace_671159
  have hstable : (prefixWord ++ tailWord_671159).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_671159).length < 2 ^ (prefixWord ++ tailWord_671159).sum := by decide
  have hdescent : baseEnd_671159 < baseStart_671159 := by decide
  rcases family_descends (prefixWord ++ tailWord_671159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_671172 : List Nat := [2, 3, 3, 2, 1, 3, 1, 2, 3]
def baseStart_671172 : Nat := 118140960795 + 671172 * 2 ^ 59
def prefixEnd_671172 : Nat := 4983230072969 + 3 ^ 40 * 671172 * 2
def baseEnd_671172 : Nat := 306341189190714017922971

theorem tailTrace_671172 : CollatzResearch.WordTrace tailWord_671172 prefixEnd_671172 306341189190714017922971 := by
  unfold tailWord_671172
  simp only [CollatzResearch.WordTrace]
  refine ⟨12239826962232972948391885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16319769282977297264522513 12239826962232972948391885)
  ·
    refine ⟨4589935110837364855646957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12239826962232972948391885 4589935110837364855646957)
    ·
      refine ⟨1721225666564011820867609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4589935110837364855646957 1721225666564011820867609)
      ·
        refine ⟨1290919249923008865650707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1721225666564011820867609 1290919249923008865650707)
        ·
          refine ⟨1936378874884513298476061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1290919249923008865650707 1936378874884513298476061)
          ·
            refine ⟨726142078081692486928523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1936378874884513298476061 726142078081692486928523)
            ·
              refine ⟨1089213117122538730392785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 726142078081692486928523 1089213117122538730392785)
              ·
                refine ⟨816909837841904047794589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1089213117122538730392785 816909837841904047794589)
                ·
                  refine ⟨306341189190714017922971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 816909837841904047794589 306341189190714017922971)
                  ·
                    rfl

theorem cell20_671172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 3, 1, 2, 3].length) (baseStart_671172 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_671172 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_671172 prefixEnd_671172 := by exact prefixLift 671172
  have htrace : WordTrace (prefixWord ++ tailWord_671172) baseStart_671172 baseEnd_671172 := by
    simpa [prefixWord, tailWord_671172, baseEnd_671172] using wordTrace_append hprefix tailTrace_671172
  have hstable : (prefixWord ++ tailWord_671172).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_671172).length < 2 ^ (prefixWord ++ tailWord_671172).sum := by decide
  have hdescent : baseEnd_671172 < baseStart_671172 := by decide
  rcases family_descends (prefixWord ++ tailWord_671172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_671193 : List Nat := [1, 2, 1, 2, 4, 3, 3, 1, 3]
def baseStart_671193 : Nat := 118140960795 + 671193 * 2 ^ 59
def prefixEnd_671193 : Nat := 4983230072969 + 3 ^ 40 * 671193 * 2
def baseEnd_671193 : Nat := 306350774162931278222885

theorem tailTrace_671193 : CollatzResearch.WordTrace tailWord_671193 prefixEnd_671193 306350774162931278222885 := by
  unfold tailWord_671193
  simp only [CollatzResearch.WordTrace]
  refine ⟨24480419857389866483298233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16320279904926577655532155 24480419857389866483298233)
  ·
    refine ⟨18360314893042399862473675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24480419857389866483298233 18360314893042399862473675)
    ·
      refine ⟨27540472339563599793710513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18360314893042399862473675 27540472339563599793710513)
      ·
        refine ⟨20655354254672699845282885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27540472339563599793710513 20655354254672699845282885)
        ·
          refine ⟨3872878922751131220990541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20655354254672699845282885 3872878922751131220990541)
          ·
            refine ⟨1452329596031674207871453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3872878922751131220990541 1452329596031674207871453)
            ·
              refine ⟨544623598511877827951795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1452329596031674207871453 544623598511877827951795)
              ·
                refine ⟨816935397767816741927693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 544623598511877827951795 816935397767816741927693)
                ·
                  refine ⟨306350774162931278222885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 816935397767816741927693 306350774162931278222885)
                  ·
                    rfl

theorem cell20_671193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 3, 3, 1, 3].length) (baseStart_671193 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_671193 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_671193 prefixEnd_671193 := by exact prefixLift 671193
  have htrace : WordTrace (prefixWord ++ tailWord_671193) baseStart_671193 baseEnd_671193 := by
    simpa [prefixWord, tailWord_671193, baseEnd_671193] using wordTrace_append hprefix tailTrace_671193
  have hstable : (prefixWord ++ tailWord_671193).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_671193).length < 2 ^ (prefixWord ++ tailWord_671193).sum := by decide
  have hdescent : baseEnd_671193 < baseStart_671193 := by decide
  rcases family_descends (prefixWord ++ tailWord_671193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_671207 : List Nat := [1, 1, 5, 2, 1, 2, 4, 4]
def baseStart_671207 : Nat := 118140960795 + 671207 * 2 ^ 59
def prefixEnd_671207 : Nat := 4983230072969 + 3 ^ 40 * 671207 * 2
def baseEnd_671207 : Nat := 102119054714803150585387

theorem tailTrace_671207 : CollatzResearch.WordTrace tailWord_671207 prefixEnd_671207 102119054714803150585387 := by
  unfold tailWord_671207
  simp only [CollatzResearch.WordTrace]
  refine ⟨24480930479339146874307875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16320620319559431249538583 24480930479339146874307875)
  ·
    refine ⟨36721395719008720311461813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24480930479339146874307875 36721395719008720311461813)
    ·
      refine ⟨3442630848657067529199545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 36721395719008720311461813 3442630848657067529199545)
      ·
        refine ⟨2581973136492800646899659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3442630848657067529199545 2581973136492800646899659)
        ·
          refine ⟨3872959704739200970349489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2581973136492800646899659 3872959704739200970349489)
          ·
            refine ⟨2904719778554400727762117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3872959704739200970349489 2904719778554400727762117)
            ·
              refine ⟨544634958478950136455397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2904719778554400727762117 544634958478950136455397)
              ·
                refine ⟨102119054714803150585387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 544634958478950136455397 102119054714803150585387)
                ·
                  rfl

theorem cell20_671207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 4, 4].length) (baseStart_671207 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_671207 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_671207 prefixEnd_671207 := by exact prefixLift 671207
  have htrace : WordTrace (prefixWord ++ tailWord_671207) baseStart_671207 baseEnd_671207 := by
    simpa [prefixWord, tailWord_671207, baseEnd_671207] using wordTrace_append hprefix tailTrace_671207
  have hstable : (prefixWord ++ tailWord_671207).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_671207).length < 2 ^ (prefixWord ++ tailWord_671207).sum := by decide
  have hdescent : baseEnd_671207 < baseStart_671207 := by decide
  rcases family_descends (prefixWord ++ tailWord_671207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_671213 : List Nat := [1, 5, 1, 3, 3, 1, 1, 3, 2]
def baseStart_671213 : Nat := 118140960795 + 671213 * 2 ^ 59
def prefixEnd_671213 : Nat := 4983230072969 + 3 ^ 40 * 671213 * 2
def baseEnd_671213 : Nat := 306359902707900097556137

theorem tailTrace_671213 : CollatzResearch.WordTrace tailWord_671213 prefixEnd_671213 306359902707900097556137 := by
  unfold tailWord_671213
  simp only [CollatzResearch.WordTrace]
  refine ⟨24481149317317409899026293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16320766211544939932684195 24481149317317409899026293)
  ·
    refine ⟨2295107748498507178033715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 24481149317317409899026293 2295107748498507178033715)
    ·
      refine ⟨3442661622747760767050573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2295107748498507178033715 3442661622747760767050573)
      ·
        refine ⟨1290998108530410287643965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3442661622747760767050573 1290998108530410287643965)
        ·
          refine ⟨484124290698903857866487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1290998108530410287643965 484124290698903857866487)
          ·
            refine ⟨726186436048355786799731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 484124290698903857866487 726186436048355786799731)
            ·
              refine ⟨1089279654072533680199597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 726186436048355786799731 1089279654072533680199597)
              ·
                refine ⟨408479870277200130074849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1089279654072533680199597 408479870277200130074849)
                ·
                  refine ⟨306359902707900097556137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 408479870277200130074849 306359902707900097556137)
                  ·
                    rfl

theorem cell20_671213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 3, 1, 1, 3, 2].length) (baseStart_671213 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_671213 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_671213 prefixEnd_671213 := by exact prefixLift 671213
  have htrace : WordTrace (prefixWord ++ tailWord_671213) baseStart_671213 baseEnd_671213 := by
    simpa [prefixWord, tailWord_671213, baseEnd_671213] using wordTrace_append hprefix tailTrace_671213
  have hstable : (prefixWord ++ tailWord_671213).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_671213).length < 2 ^ (prefixWord ++ tailWord_671213).sum := by decide
  have hdescent : baseEnd_671213 < baseStart_671213 := by decide
  rcases family_descends (prefixWord ++ tailWord_671213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_671217 : List Nat := [1, 2, 2, 2, 3, 4, 1, 3, 2]
def baseStart_671217 : Nat := 118140960795 + 671217 * 2 ^ 59
def prefixEnd_671217 : Nat := 4983230072969 + 3 ^ 40 * 671217 * 2
def baseEnd_671217 : Nat := 306361728416893861422787

theorem tailTrace_671217 : CollatzResearch.WordTrace tailWord_671217 prefixEnd_671217 306361728416893861422787 := by
  unfold tailWord_671217
  simp only [CollatzResearch.WordTrace]
  refine ⟨24481295209302918582171905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16320863472868612388114603 24481295209302918582171905)
  ·
    refine ⟨18360971406977188936628929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24481295209302918582171905 18360971406977188936628929)
    ·
      refine ⟨13770728555232891702471697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18360971406977188936628929 13770728555232891702471697)
      ·
        refine ⟨10328046416424668776853773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13770728555232891702471697 10328046416424668776853773)
        ·
          refine ⟨3873017406159250791320165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10328046416424668776853773 3873017406159250791320165)
          ·
            refine ⟨726190763654859523372531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3873017406159250791320165 726190763654859523372531)
            ·
              refine ⟨1089286145482289285058797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 726190763654859523372531 1089286145482289285058797)
              ·
                refine ⟨408482304555858481897049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1089286145482289285058797 408482304555858481897049)
                ·
                  refine ⟨306361728416893861422787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 408482304555858481897049 306361728416893861422787)
                  ·
                    rfl

theorem cell20_671217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 4, 1, 3, 2].length) (baseStart_671217 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_671217 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_671217 prefixEnd_671217 := by exact prefixLift 671217
  have htrace : WordTrace (prefixWord ++ tailWord_671217) baseStart_671217 baseEnd_671217 := by
    simpa [prefixWord, tailWord_671217, baseEnd_671217] using wordTrace_append hprefix tailTrace_671217
  have hstable : (prefixWord ++ tailWord_671217).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_671217).length < 2 ^ (prefixWord ++ tailWord_671217).sum := by decide
  have hdescent : baseEnd_671217 < baseStart_671217 := by decide
  rcases family_descends (prefixWord ++ tailWord_671217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_671266 : List Nat := [3, 3, 1, 1, 1, 1, 4, 6]
def baseStart_671266 : Nat := 118140960795 + 671266 * 2 ^ 59
def prefixEnd_671266 : Nat := 4983230072969 + 3 ^ 40 * 671266 * 2
def baseEnd_671266 : Nat := 102128031117355822929751

theorem tailTrace_671266 : CollatzResearch.WordTrace tailWord_671266 prefixEnd_671266 102128031117355822929751 := by
  unfold tailWord_671266
  simp only [CollatzResearch.WordTrace]
  refine ⟨6120770596531349987676413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16322054924083599967137101 6120770596531349987676413)
  ·
    refine ⟨2295288973699256245378655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6120770596531349987676413 2295288973699256245378655)
    ·
      refine ⟨3442933460548884368067983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2295288973699256245378655 3442933460548884368067983)
      ·
        refine ⟨5164400190823326552101975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3442933460548884368067983 5164400190823326552101975)
        ·
          refine ⟨7746600286234989828152963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5164400190823326552101975 7746600286234989828152963)
          ·
            refine ⟨11619900429352484742229445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7746600286234989828152963 11619900429352484742229445)
            ·
              refine ⟨2178731330503590889168021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11619900429352484742229445 2178731330503590889168021)
              ·
                refine ⟨102128031117355822929751, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2178731330503590889168021 102128031117355822929751)
                ·
                  rfl

theorem cell20_671266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 4, 6].length) (baseStart_671266 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_671266 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_671266 prefixEnd_671266 := by exact prefixLift 671266
  have htrace : WordTrace (prefixWord ++ tailWord_671266) baseStart_671266 baseEnd_671266 := by
    simpa [prefixWord, tailWord_671266, baseEnd_671266] using wordTrace_append hprefix tailTrace_671266
  have hstable : (prefixWord ++ tailWord_671266).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_671266).length < 2 ^ (prefixWord ++ tailWord_671266).sum := by decide
  have hdescent : baseEnd_671266 < baseStart_671266 := by decide
  rcases family_descends (prefixWord ++ tailWord_671266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_671286 : List Nat := [5, 1, 2, 1, 3, 1, 2, 2, 3]
def baseStart_671286 : Nat := 118140960795 + 671286 * 2 ^ 59
def prefixEnd_671286 : Nat := 4983230072969 + 3 ^ 40 * 671286 * 2
def baseEnd_671286 : Nat := 306393221897036288122505

theorem tailTrace_671286 : CollatzResearch.WordTrace tailWord_671286 prefixEnd_671286 306393221897036288122505 := by
  unfold tailWord_671286
  simp only [CollatzResearch.WordTrace]
  refine ⟨1530238240378308960402107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 16322541230701962244289141 1530238240378308960402107)
  ·
    refine ⟨2295357360567463440603161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1530238240378308960402107 2295357360567463440603161)
    ·
      refine ⟨1721518020425597580452371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2295357360567463440603161 1721518020425597580452371)
      ·
        refine ⟨2582277030638396370678557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1721518020425597580452371 2582277030638396370678557)
        ·
          refine ⟨968353886489398639004459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2582277030638396370678557 968353886489398639004459)
          ·
            refine ⟨1452530829734097958506689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 968353886489398639004459 1452530829734097958506689)
            ·
              refine ⟨1089398122300573468880017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1452530829734097958506689 1089398122300573468880017)
              ·
                refine ⟨817048591725430101660013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1089398122300573468880017 817048591725430101660013)
                ·
                  refine ⟨306393221897036288122505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 817048591725430101660013 306393221897036288122505)
                  ·
                    rfl

theorem cell20_671286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 1, 2, 2, 3].length) (baseStart_671286 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_671286 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_671286 prefixEnd_671286 := by exact prefixLift 671286
  have htrace : WordTrace (prefixWord ++ tailWord_671286) baseStart_671286 baseEnd_671286 := by
    simpa [prefixWord, tailWord_671286, baseEnd_671286] using wordTrace_append hprefix tailTrace_671286
  have hstable : (prefixWord ++ tailWord_671286).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_671286).length < 2 ^ (prefixWord ++ tailWord_671286).sum := by decide
  have hdescent : baseEnd_671286 < baseStart_671286 := by decide
  rcases family_descends (prefixWord ++ tailWord_671286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_671287 : List Nat := [1, 1, 3, 1, 2, 12]
def baseStart_671287 : Nat := 118140960795 + 671287 * 2 ^ 59
def prefixEnd_671287 : Nat := 4983230072969 + 3 ^ 40 * 671287 * 2
def baseEnd_671287 : Nat := 11347914012010545521821

theorem tailTrace_671287 : CollatzResearch.WordTrace tailWord_671287 prefixEnd_671287 11347914012010545521821 := by
  unfold tailWord_671287
  simp only [CollatzResearch.WordTrace]
  refine ⟨24483848319049320537220115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16322565546032880358146743 24483848319049320537220115)
  ·
    refine ⟨36725772478573980805830173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24483848319049320537220115 36725772478573980805830173)
    ·
      refine ⟨13772164679465242802186315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36725772478573980805830173 13772164679465242802186315)
      ·
        refine ⟨20658247019197864203279473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13772164679465242802186315 20658247019197864203279473)
        ·
          refine ⟨15493685264398398152459605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20658247019197864203279473 15493685264398398152459605)
          ·
            refine ⟨11347914012010545521821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 15493685264398398152459605 11347914012010545521821)
            ·
              rfl

theorem cell20_671287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 12].length) (baseStart_671287 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_671287 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_671287 prefixEnd_671287 := by exact prefixLift 671287
  have htrace : WordTrace (prefixWord ++ tailWord_671287) baseStart_671287 baseEnd_671287 := by
    simpa [prefixWord, tailWord_671287, baseEnd_671287] using wordTrace_append hprefix tailTrace_671287
  have hstable : (prefixWord ++ tailWord_671287).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_671287).length < 2 ^ (prefixWord ++ tailWord_671287).sum := by decide
  have hdescent : baseEnd_671287 < baseStart_671287 := by decide
  rcases family_descends (prefixWord ++ tailWord_671287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_671290 : List Nat := [3, 1, 1, 1, 3, 2, 4, 2, 3]
def baseStart_671290 : Nat := 118140960795 + 671290 * 2 ^ 59
def prefixEnd_671290 : Nat := 4983230072969 + 3 ^ 40 * 671290 * 2
def baseEnd_671290 : Nat := 306395047606030051989155

theorem tailTrace_671290 : CollatzResearch.WordTrace tailWord_671290 prefixEnd_671290 306395047606030051989155 := by
  unfold tailWord_671290
  simp only [CollatzResearch.WordTrace]
  refine ⟨6120989434509613012394831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16322638492025634699719549 6120989434509613012394831)
  ·
    refine ⟨9181484151764419518592247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6120989434509613012394831 9181484151764419518592247)
    ·
      refine ⟨13772226227646629277888371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9181484151764419518592247 13772226227646629277888371)
      ·
        refine ⟨20658339341469943916832557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13772226227646629277888371 20658339341469943916832557)
        ·
          refine ⟨7746877253051228968812209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20658339341469943916832557 7746877253051228968812209)
          ·
            refine ⟨5810157939788421726609157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7746877253051228968812209 5810157939788421726609157)
            ·
              refine ⟨1089404613710329073739217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5810157939788421726609157 1089404613710329073739217)
              ·
                refine ⟨817053460282746805304413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1089404613710329073739217 817053460282746805304413)
                ·
                  refine ⟨306395047606030051989155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 817053460282746805304413 306395047606030051989155)
                  ·
                    rfl

theorem cell20_671290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 4, 2, 3].length) (baseStart_671290 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_671290 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_671290 prefixEnd_671290 := by exact prefixLift 671290
  have htrace : WordTrace (prefixWord ++ tailWord_671290) baseStart_671290 baseEnd_671290 := by
    simpa [prefixWord, tailWord_671290, baseEnd_671290] using wordTrace_append hprefix tailTrace_671290
  have hstable : (prefixWord ++ tailWord_671290).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_671290).length < 2 ^ (prefixWord ++ tailWord_671290).sum := by decide
  have hdescent : baseEnd_671290 < baseStart_671290 := by decide
  rcases family_descends (prefixWord ++ tailWord_671290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_671293 : List Nat := [1, 4, 1, 3, 3, 1, 1, 4, 2]
def baseStart_671293 : Nat := 118140960795 + 671293 * 2 ^ 59
def prefixEnd_671293 : Nat := 4983230072969 + 3 ^ 40 * 671293 * 2
def baseEnd_671293 : Nat := 306396416887775374889143

theorem tailTrace_671293 : CollatzResearch.WordTrace tailWord_671293 prefixEnd_671293 306396416887775374889143 := by
  unfold tailWord_671293
  simp only [CollatzResearch.WordTrace]
  refine ⟨24484067157027583561938533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16322711438018389041292355 24484067157027583561938533)
  ·
    refine ⟨4590762591942671917863475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24484067157027583561938533 4590762591942671917863475)
    ·
      refine ⟨6886143887914007876795213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4590762591942671917863475 6886143887914007876795213)
      ·
        refine ⟨2582303957967752953798205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6886143887914007876795213 2582303957967752953798205)
        ·
          refine ⟨968363984237907357674327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2582303957967752953798205 968363984237907357674327)
          ·
            refine ⟨1452545976356861036511491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 968363984237907357674327 1452545976356861036511491)
            ·
              refine ⟨2178818964535291554767237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1452545976356861036511491 2178818964535291554767237)
              ·
                refine ⟨408528555850367166518857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2178818964535291554767237 408528555850367166518857)
                ·
                  refine ⟨306396416887775374889143, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 408528555850367166518857 306396416887775374889143)
                  ·
                    rfl

theorem cell20_671293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 1, 1, 4, 2].length) (baseStart_671293 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_671293 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_671293 prefixEnd_671293 := by exact prefixLift 671293
  have htrace : WordTrace (prefixWord ++ tailWord_671293) baseStart_671293 baseEnd_671293 := by
    simpa [prefixWord, tailWord_671293, baseEnd_671293] using wordTrace_append hprefix tailTrace_671293
  have hstable : (prefixWord ++ tailWord_671293).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_671293).length < 2 ^ (prefixWord ++ tailWord_671293).sum := by decide
  have hdescent : baseEnd_671293 < baseStart_671293 := by decide
  rcases family_descends (prefixWord ++ tailWord_671293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_671297 : List Nat := [1, 2, 5, 1, 1, 1, 2, 3, 4]
def baseStart_671297 : Nat := 118140960795 + 671297 * 2 ^ 59
def prefixEnd_671297 : Nat := 4983230072969 + 3 ^ 40 * 671297 * 2
def baseEnd_671297 : Nat := 306398242596769138755793

theorem tailTrace_671297 : CollatzResearch.WordTrace tailWord_671297 prefixEnd_671297 306398242596769138755793 := by
  unfold tailWord_671297
  simp only [CollatzResearch.WordTrace]
  refine ⟨24484213049013092245084145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16322808699342061496722763 24484213049013092245084145)
  ·
    refine ⟨18363159786759819183813109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24484213049013092245084145 18363159786759819183813109)
    ·
      refine ⟨1721546230008733048482479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 18363159786759819183813109 1721546230008733048482479)
      ·
        refine ⟨2582319345013099572723719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1721546230008733048482479 2582319345013099572723719)
        ·
          refine ⟨3873479017519649359085579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2582319345013099572723719 3873479017519649359085579)
          ·
            refine ⟨5810218526279474038628369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3873479017519649359085579 5810218526279474038628369)
            ·
              refine ⟨4357663894709605528971277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5810218526279474038628369 4357663894709605528971277)
              ·
                refine ⟨1634123960516102073364229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4357663894709605528971277 1634123960516102073364229)
                ·
                  refine ⟨306398242596769138755793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1634123960516102073364229 306398242596769138755793)
                  ·
                    rfl

theorem cell20_671297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 2, 3, 4].length) (baseStart_671297 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_671297 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_671297 prefixEnd_671297 := by exact prefixLift 671297
  have htrace : WordTrace (prefixWord ++ tailWord_671297) baseStart_671297 baseEnd_671297 := by
    simpa [prefixWord, tailWord_671297, baseEnd_671297] using wordTrace_append hprefix tailTrace_671297
  have hstable : (prefixWord ++ tailWord_671297).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_671297).length < 2 ^ (prefixWord ++ tailWord_671297).sum := by decide
  have hdescent : baseEnd_671297 < baseStart_671297 := by decide
  rcases family_descends (prefixWord ++ tailWord_671297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_671363 : List Nat := [1, 1, 1, 3, 3, 1, 1, 9]
def baseStart_671363 : Nat := 118140960795 + 671363 * 2 ^ 59
def prefixEnd_671363 : Nat := 4983230072969 + 3 ^ 40 * 671363 * 2
def baseEnd_671363 : Nat := 102142788931722080851841

theorem tailTrace_671363 : CollatzResearch.WordTrace tailWord_671363 prefixEnd_671363 102142788931722080851841 := by
  unfold tailWord_671363
  simp only [CollatzResearch.WordTrace]
  refine ⟨24486620266773985516986743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16324413511182657011324495 24486620266773985516986743)
  ·
    refine ⟨36729930400160978275480115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24486620266773985516986743 36729930400160978275480115)
    ·
      refine ⟨55094895600241467413220173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36729930400160978275480115 55094895600241467413220173)
      ·
        refine ⟨20660585850090550279957565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55094895600241467413220173 20660585850090550279957565)
        ·
          refine ⟨7747719693783956354984087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20660585850090550279957565 7747719693783956354984087)
          ·
            refine ⟨11621579540675934532476131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7747719693783956354984087 11621579540675934532476131)
            ·
              refine ⟨17432369311013901798714197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11621579540675934532476131 17432369311013901798714197)
              ·
                refine ⟨102142788931722080851841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 17432369311013901798714197 102142788931722080851841)
                ·
                  rfl

theorem cell20_671363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 9].length) (baseStart_671363 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_671363 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_671363 prefixEnd_671363 := by exact prefixLift 671363
  have htrace : WordTrace (prefixWord ++ tailWord_671363) baseStart_671363 baseEnd_671363 := by
    simpa [prefixWord, tailWord_671363, baseEnd_671363] using wordTrace_append hprefix tailTrace_671363
  have hstable : (prefixWord ++ tailWord_671363).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_671363).length < 2 ^ (prefixWord ++ tailWord_671363).sum := by decide
  have hdescent : baseEnd_671363 < baseStart_671363 := by decide
  rcases family_descends (prefixWord ++ tailWord_671363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_671414 : List Nat := [5, 1, 3, 1, 1, 2, 2, 5]
def baseStart_671414 : Nat := 118140960795 + 671414 * 2 ^ 59
def prefixEnd_671414 : Nat := 4983230072969 + 3 ^ 40 * 671414 * 2
def baseEnd_671414 : Nat := 102150548194945577285105

theorem tailTrace_671414 : CollatzResearch.WordTrace tailWord_671414 prefixEnd_671414 102150548194945577285105 := by
  unfold tailWord_671414
  simp only [CollatzResearch.WordTrace]
  refine ⟨1530530024349326326693331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 16325653593059480818062197 1530530024349326326693331)
  ·
    refine ⟨2295795036523989490039997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1530530024349326326693331 2295795036523989490039997)
    ·
      refine ⟨860923138696496058764999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2295795036523989490039997 860923138696496058764999)
      ·
        refine ⟨1291384708044744088147499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 860923138696496058764999 1291384708044744088147499)
        ·
          refine ⟨1937077062067116132221249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1291384708044744088147499 1937077062067116132221249)
          ·
            refine ⟨1452807796550337099165937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1937077062067116132221249 1452807796550337099165937)
            ·
              refine ⟨1089605847412752824374453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1452807796550337099165937 1089605847412752824374453)
              ·
                refine ⟨102150548194945577285105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1089605847412752824374453 102150548194945577285105)
                ·
                  rfl

theorem cell20_671414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 2, 2, 5].length) (baseStart_671414 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_671414 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_671414 prefixEnd_671414 := by exact prefixLift 671414
  have htrace : WordTrace (prefixWord ++ tailWord_671414) baseStart_671414 baseEnd_671414 := by
    simpa [prefixWord, tailWord_671414, baseEnd_671414] using wordTrace_append hprefix tailTrace_671414
  have hstable : (prefixWord ++ tailWord_671414).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_671414).length < 2 ^ (prefixWord ++ tailWord_671414).sum := by decide
  have hdescent : baseEnd_671414 < baseStart_671414 := by decide
  rcases family_descends (prefixWord ++ tailWord_671414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_671418 : List Nat := [3, 1, 1, 1, 2, 5, 2, 5]
def baseStart_671418 : Nat := 118140960795 + 671418 * 2 ^ 59
def prefixEnd_671418 : Nat := 4983230072969 + 3 ^ 40 * 671418 * 2
def baseEnd_671418 : Nat := 102151156764610165240655

theorem tailTrace_671418 : CollatzResearch.WordTrace tailWord_671418 prefixEnd_671418 102151156764610165240655 := by
  unfold tailWord_671418
  simp only [CollatzResearch.WordTrace]
  refine ⟨6122156570393682477559727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16325750854383153273492605 6122156570393682477559727)
  ·
    refine ⟨9183234855590523716339591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6122156570393682477559727 9183234855590523716339591)
    ·
      refine ⟨13774852283385785574509387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9183234855590523716339591 13774852283385785574509387)
      ·
        refine ⟨20662278425078678361764081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13774852283385785574509387 20662278425078678361764081)
        ·
          refine ⟨15496708818809008771323061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20662278425078678361764081 15496708818809008771323061)
          ·
            refine ⟨1452816451763344572311537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 15496708818809008771323061 1452816451763344572311537)
            ·
              refine ⟨1089612338822508429233653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1452816451763344572311537 1089612338822508429233653)
              ·
                refine ⟨102151156764610165240655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1089612338822508429233653 102151156764610165240655)
                ·
                  rfl

theorem cell20_671418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 5, 2, 5].length) (baseStart_671418 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_671418 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_671418 prefixEnd_671418 := by exact prefixLift 671418
  have htrace : WordTrace (prefixWord ++ tailWord_671418) baseStart_671418 baseEnd_671418 := by
    simpa [prefixWord, tailWord_671418, baseEnd_671418] using wordTrace_append hprefix tailTrace_671418
  have hstable : (prefixWord ++ tailWord_671418).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_671418).length < 2 ^ (prefixWord ++ tailWord_671418).sum := by decide
  have hdescent : baseEnd_671418 < baseStart_671418 := by decide
  rcases family_descends (prefixWord ++ tailWord_671418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_671432 : List Nat := [2, 1, 3, 1, 2, 2, 2, 1, 6]
def baseStart_671432 : Nat := 118140960795 + 671432 * 2 ^ 59
def prefixEnd_671432 : Nat := 4983230072969 + 3 ^ 40 * 671432 * 2
def baseEnd_671432 : Nat := 306459860275308669255241

theorem tailTrace_671432 : CollatzResearch.WordTrace tailWord_671432 prefixEnd_671432 306459860275308669255241 := by
  unfold tailWord_671432
  simp only [CollatzResearch.WordTrace]
  refine ⟨12244568451762005150624275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16326091269016006867499033 12244568451762005150624275)
  ·
    refine ⟨18366852677643007725936413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12244568451762005150624275 18366852677643007725936413)
    ·
      refine ⟨6887569754116127897226155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18366852677643007725936413 6887569754116127897226155)
      ·
        refine ⟨10331354631174191845839233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6887569754116127897226155 10331354631174191845839233)
        ·
          refine ⟨7748515973380643884379425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10331354631174191845839233 7748515973380643884379425)
          ·
            refine ⟨5811386980035482913284569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7748515973380643884379425 5811386980035482913284569)
            ·
              refine ⟨4358540235026612184963427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5811386980035482913284569 4358540235026612184963427)
              ·
                refine ⟨6537810352539918277445141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4358540235026612184963427 6537810352539918277445141)
                ·
                  refine ⟨306459860275308669255241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6537810352539918277445141 306459860275308669255241)
                  ·
                    rfl

theorem cell20_671432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 2, 1, 6].length) (baseStart_671432 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_671432 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_671432 prefixEnd_671432 := by exact prefixLift 671432
  have htrace : WordTrace (prefixWord ++ tailWord_671432) baseStart_671432 baseEnd_671432 := by
    simpa [prefixWord, tailWord_671432, baseEnd_671432] using wordTrace_append hprefix tailTrace_671432
  have hstable : (prefixWord ++ tailWord_671432).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_671432).length < 2 ^ (prefixWord ++ tailWord_671432).sum := by decide
  have hdescent : baseEnd_671432 < baseStart_671432 := by decide
  rcases family_descends (prefixWord ++ tailWord_671432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_671459 : List Nat := [1, 1, 1, 7, 2, 1, 2, 2, 3]
def baseStart_671459 : Nat := 118140960795 + 671459 * 2 ^ 59
def prefixEnd_671459 : Nat := 4983230072969 + 3 ^ 40 * 671459 * 2
def baseEnd_671459 : Nat := 306472183811016575355131

theorem tailTrace_671459 : CollatzResearch.WordTrace tailWord_671459 prefixEnd_671459 306472183811016575355131 := by
  unfold tailWord_671459
  simp only [CollatzResearch.WordTrace]
  refine ⟨24490121674426193912481431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16326747782950795941654287 24490121674426193912481431)
  ·
    refine ⟨36735182511639290868722147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24490121674426193912481431 36735182511639290868722147)
    ·
      refine ⟨55102773767458936303083221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36735182511639290868722147 55102773767458936303083221)
      ·
        refine ⟨1291471260174818819603513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 55102773767458936303083221 1291471260174818819603513)
        ·
          refine ⟨968603445131114114702635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1291471260174818819603513 968603445131114114702635)
          ·
            refine ⟨1452905167696671172053953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 968603445131114114702635 1452905167696671172053953)
            ·
              refine ⟨1089678875772503379040465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1452905167696671172053953 1089678875772503379040465)
              ·
                refine ⟨817259156829377534280349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1089678875772503379040465 817259156829377534280349)
                ·
                  refine ⟨306472183811016575355131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 817259156829377534280349 306472183811016575355131)
                  ·
                    rfl

theorem cell20_671459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 1, 2, 2, 3].length) (baseStart_671459 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_671459 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_671459 prefixEnd_671459 := by exact prefixLift 671459
  have htrace : WordTrace (prefixWord ++ tailWord_671459) baseStart_671459 baseEnd_671459 := by
    simpa [prefixWord, tailWord_671459, baseEnd_671459] using wordTrace_append hprefix tailTrace_671459
  have hstable : (prefixWord ++ tailWord_671459).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_671459).length < 2 ^ (prefixWord ++ tailWord_671459).sum := by decide
  have hdescent : baseEnd_671459 < baseStart_671459 := by decide
  rcases family_descends (prefixWord ++ tailWord_671459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_671476 : List Nat := [2, 6, 1, 1, 1, 1, 2, 3, 3]
def baseStart_671476 : Nat := 118140960795 + 671476 * 2 ^ 59
def prefixEnd_671476 : Nat := 4983230072969 + 3 ^ 40 * 671476 * 2
def baseEnd_671476 : Nat := 306479943074240071788395

theorem tailTrace_671476 : CollatzResearch.WordTrace tailWord_671476 prefixEnd_671476 306479943074240071788395 := by
  unfold tailWord_671476
  simp only [CollatzResearch.WordTrace]
  refine ⟨12245370857682302907925141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16327161143576403877233521 12245370857682302907925141)
  ·
    refine ⟨574001758953857948808991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 12245370857682302907925141 574001758953857948808991)
    ·
      refine ⟨861002638430786923213487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 574001758953857948808991 861002638430786923213487)
      ·
        refine ⟨1291503957646180384820231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 861002638430786923213487 1291503957646180384820231)
        ·
          refine ⟨1937255936469270577230347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1291503957646180384820231 1937255936469270577230347)
          ·
            refine ⟨2905883904703905865845521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1937255936469270577230347 2905883904703905865845521)
            ·
              refine ⟨2179412928527929399384141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2905883904703905865845521 2179412928527929399384141)
              ·
                refine ⟨817279848197973524769053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2179412928527929399384141 817279848197973524769053)
                ·
                  refine ⟨306479943074240071788395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 817279848197973524769053 306479943074240071788395)
                  ·
                    rfl

theorem cell20_671476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 2, 3, 3].length) (baseStart_671476 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_671476 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_671476 prefixEnd_671476 := by exact prefixLift 671476
  have htrace : WordTrace (prefixWord ++ tailWord_671476) baseStart_671476 baseEnd_671476 := by
    simpa [prefixWord, tailWord_671476, baseEnd_671476] using wordTrace_append hprefix tailTrace_671476
  have hstable : (prefixWord ++ tailWord_671476).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_671476).length < 2 ^ (prefixWord ++ tailWord_671476).sum := by decide
  have hdescent : baseEnd_671476 < baseStart_671476 := by decide
  rcases family_descends (prefixWord ++ tailWord_671476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_671525 : List Nat := [1, 3, 1, 2, 3, 3, 2, 1, 4]
def baseStart_671525 : Nat := 118140960795 + 671525 * 2 ^ 59
def prefixEnd_671525 : Nat := 4983230072969 + 3 ^ 40 * 671525 * 2
def baseEnd_671525 : Nat := 306502308009413679154861

theorem tailTrace_671525 : CollatzResearch.WordTrace tailWord_671525 prefixEnd_671525 306502308009413679154861 := by
  unfold tailWord_671525
  simp only [CollatzResearch.WordTrace]
  refine ⟨24492528892187087184384029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16328352594791391456256019 24492528892187087184384029)
  ·
    refine ⟨9184698334570157694144011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24492528892187087184384029 9184698334570157694144011)
    ·
      refine ⟨13777047501855236541216017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9184698334570157694144011 13777047501855236541216017)
      ·
        refine ⟨10332785626391427405912013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13777047501855236541216017 10332785626391427405912013)
        ·
          refine ⟨3874794609896785277217005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10332785626391427405912013 3874794609896785277217005)
          ·
            refine ⟨1453047978711294478956377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3874794609896785277217005 1453047978711294478956377)
            ·
              refine ⟨1089785984033470859217283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1453047978711294478956377 1089785984033470859217283)
              ·
                refine ⟨1634678976050206288825925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1089785984033470859217283 1634678976050206288825925)
                ·
                  refine ⟨306502308009413679154861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1634678976050206288825925 306502308009413679154861)
                  ·
                    rfl

theorem cell20_671525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 3, 2, 1, 4].length) (baseStart_671525 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_671525 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_671525 prefixEnd_671525 := by exact prefixLift 671525
  have htrace : WordTrace (prefixWord ++ tailWord_671525) baseStart_671525 baseEnd_671525 := by
    simpa [prefixWord, tailWord_671525, baseEnd_671525] using wordTrace_append hprefix tailTrace_671525
  have hstable : (prefixWord ++ tailWord_671525).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_671525).length < 2 ^ (prefixWord ++ tailWord_671525).sum := by decide
  have hdescent : baseEnd_671525 < baseStart_671525 := by decide
  rcases family_descends (prefixWord ++ tailWord_671525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_671542 : List Nat := [5, 1, 2, 2, 1, 1, 2, 2, 4]
def baseStart_671542 : Nat := 118140960795 + 671542 * 2 ^ 59
def prefixEnd_671542 : Nat := 4983230072969 + 3 ^ 40 * 671542 * 2
def baseEnd_671542 : Nat := 306510067272637175588125

theorem tailTrace_671542 : CollatzResearch.WordTrace tailWord_671542 prefixEnd_671542 306510067272637175588125 := by
  unfold tailWord_671542
  simp only [CollatzResearch.WordTrace]
  refine ⟨1530821808320343692984555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 16328765955416999391835253 1530821808320343692984555)
  ·
    refine ⟨2296232712480515539476833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1530821808320343692984555 2296232712480515539476833)
    ·
      refine ⟨1722174534360386654607625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2296232712480515539476833 1722174534360386654607625)
      ·
        refine ⟨1291630900770289990955719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1722174534360386654607625 1291630900770289990955719)
        ·
          refine ⟨1937446351155434986433579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1291630900770289990955719 1937446351155434986433579)
          ·
            refine ⟨2906169526733152479650369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1937446351155434986433579 2906169526733152479650369)
            ·
              refine ⟨2179627145049864359737777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2906169526733152479650369 2179627145049864359737777)
              ·
                refine ⟨1634720358787398269803333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2179627145049864359737777 1634720358787398269803333)
                ·
                  refine ⟨306510067272637175588125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1634720358787398269803333 306510067272637175588125)
                  ·
                    rfl

theorem cell20_671542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 2, 2, 4].length) (baseStart_671542 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_671542 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_671542 prefixEnd_671542 := by exact prefixLift 671542
  have htrace : WordTrace (prefixWord ++ tailWord_671542) baseStart_671542 baseEnd_671542 := by
    simpa [prefixWord, tailWord_671542, baseEnd_671542] using wordTrace_append hprefix tailTrace_671542
  have hstable : (prefixWord ++ tailWord_671542).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_671542).length < 2 ^ (prefixWord ++ tailWord_671542).sum := by decide
  have hdescent : baseEnd_671542 < baseStart_671542 := by decide
  rcases family_descends (prefixWord ++ tailWord_671542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_671545 : List Nat := [1, 2, 1, 7, 2, 1, 2, 4]
def baseStart_671545 : Nat := 118140960795 + 671545 * 2 ^ 59
def prefixEnd_671545 : Nat := 4983230072969 + 3 ^ 40 * 671545 * 2
def baseEnd_671545 : Nat := 102170478851460832829371

theorem tailTrace_671545 : CollatzResearch.WordTrace tailWord_671545 prefixEnd_671545 102170478851460832829371 := by
  unfold tailWord_671545
  simp only [CollatzResearch.WordTrace]
  refine ⟨24493258352114630600112089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16328838901409753733408059 24493258352114630600112089)
  ·
    refine ⟨18369943764085972950084067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24493258352114630600112089 18369943764085972950084067)
    ·
      refine ⟨27554915646128959425126101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18369943764085972950084067 27554915646128959425126101)
      ·
        refine ⟨645818335456147486526393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 27554915646128959425126101 645818335456147486526393)
        ·
          refine ⟨484363751592110614894795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 645818335456147486526393 484363751592110614894795)
          ·
            refine ⟨726545627388165922342193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 484363751592110614894795 726545627388165922342193)
            ·
              refine ⟨544909220541124441756645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 726545627388165922342193 544909220541124441756645)
              ·
                refine ⟨102170478851460832829371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 544909220541124441756645 102170478851460832829371)
                ·
                  rfl

theorem cell20_671545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 2, 1, 2, 4].length) (baseStart_671545 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_671545 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_671545 prefixEnd_671545 := by exact prefixLift 671545
  have htrace : WordTrace (prefixWord ++ tailWord_671545) baseStart_671545 baseEnd_671545 := by
    simpa [prefixWord, tailWord_671545, baseEnd_671545] using wordTrace_append hprefix tailTrace_671545
  have hstable : (prefixWord ++ tailWord_671545).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_671545).length < 2 ^ (prefixWord ++ tailWord_671545).sum := by decide
  have hdescent : baseEnd_671545 < baseStart_671545 := by decide
  rcases family_descends (prefixWord ++ tailWord_671545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_671549 : List Nat := [1, 4, 1, 4, 1, 1, 4, 4]
def baseStart_671549 : Nat := 118140960795 + 671549 * 2 ^ 59
def prefixEnd_671549 : Nat := 4983230072969 + 3 ^ 40 * 671549 * 2
def baseEnd_671549 : Nat := 102171087421125420784921

theorem tailTrace_671549 : CollatzResearch.WordTrace tailWord_671549 prefixEnd_671549 102171087421125420784921 := by
  unfold tailWord_671549
  simp only [CollatzResearch.WordTrace]
  refine ⟨24493404244100139283257701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16328936162733426188838467 24493404244100139283257701)
  ·
    refine ⟨4592513295768776115610819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24493404244100139283257701 4592513295768776115610819)
    ·
      refine ⟨6888769943653164173416229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4592513295768776115610819 6888769943653164173416229)
      ·
        refine ⟨1291644364434968282515543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6888769943653164173416229 1291644364434968282515543)
        ·
          refine ⟨1937466546652452423773315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1291644364434968282515543 1937466546652452423773315)
          ·
            refine ⟨2906199819978678635659973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1937466546652452423773315 2906199819978678635659973)
            ·
              refine ⟨544912466246002244186245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2906199819978678635659973 544912466246002244186245)
              ·
                refine ⟨102171087421125420784921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 544912466246002244186245 102171087421125420784921)
                ·
                  rfl

theorem cell20_671549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 4, 4].length) (baseStart_671549 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_671549 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_671549 prefixEnd_671549 := by exact prefixLift 671549
  have htrace : WordTrace (prefixWord ++ tailWord_671549) baseStart_671549 baseEnd_671549 := by
    simpa [prefixWord, tailWord_671549, baseEnd_671549] using wordTrace_append hprefix tailTrace_671549
  have hstable : (prefixWord ++ tailWord_671549).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_671549).length < 2 ^ (prefixWord ++ tailWord_671549).sum := by decide
  have hdescent : baseEnd_671549 < baseStart_671549 := by decide
  rcases family_descends (prefixWord ++ tailWord_671549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_671570 : List Nat := [3, 2, 2, 1, 1, 5, 6]
def baseStart_671570 : Nat := 118140960795 + 671570 * 2 ^ 59
def prefixEnd_671570 : Nat := 4983230072969 + 3 ^ 40 * 671570 * 2
def baseEnd_671570 : Nat := 34058094137288169183853

theorem tailTrace_671570 : CollatzResearch.WordTrace tailWord_671570 prefixEnd_671570 34058094137288169183853 := by
  unfold tailWord_671570
  simp only [CollatzResearch.WordTrace]
  refine ⟨6123542544256014967443041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16329446784682706579848109 6123542544256014967443041)
  ·
    refine ⟨4592656908192011225582281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6123542544256014967443041 4592656908192011225582281)
    ·
      refine ⟨3444492681144008419186711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4592656908192011225582281 3444492681144008419186711)
      ·
        refine ⟨5166739021716012628780067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3444492681144008419186711 5166739021716012628780067)
        ·
          refine ⟨7750108532574018943170101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5166739021716012628780067 7750108532574018943170101)
          ·
            refine ⟨726572674928814275922197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 7750108532574018943170101 726572674928814275922197)
            ·
              refine ⟨34058094137288169183853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 726572674928814275922197 34058094137288169183853)
              ·
                rfl

theorem cell20_671570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 5, 6].length) (baseStart_671570 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_671570 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_671570 prefixEnd_671570 := by exact prefixLift 671570
  have htrace : WordTrace (prefixWord ++ tailWord_671570) baseStart_671570 baseEnd_671570 := by
    simpa [prefixWord, tailWord_671570, baseEnd_671570] using wordTrace_append hprefix tailTrace_671570
  have hstable : (prefixWord ++ tailWord_671570).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_671570).length < 2 ^ (prefixWord ++ tailWord_671570).sum := by decide
  have hdescent : baseEnd_671570 < baseStart_671570 := by decide
  rcases family_descends (prefixWord ++ tailWord_671570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_671577 : List Nat := [1, 2, 1, 2, 2, 3, 2, 4, 3]
def baseStart_671577 : Nat := 118140960795 + 671577 * 2 ^ 59
def prefixEnd_671577 : Nat := 4983230072969 + 3 ^ 40 * 671577 * 2
def baseEnd_671577 : Nat := 306526042226332609421315

theorem tailTrace_671577 : CollatzResearch.WordTrace tailWord_671577 prefixEnd_671577 306526042226332609421315 := by
  unfold tailWord_671577
  simp only [CollatzResearch.WordTrace]
  refine ⟨24494425487998700065276985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16329616991999133376851323 24494425487998700065276985)
  ·
    refine ⟨18370819115999025048957739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24494425487998700065276985 18370819115999025048957739)
    ·
      refine ⟨27556228673998537573436609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18370819115999025048957739 27556228673998537573436609)
      ·
        refine ⟨20667171505498903180077457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27556228673998537573436609 20667171505498903180077457)
        ·
          refine ⟨15500378629124177385058093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20667171505498903180077457 15500378629124177385058093)
          ·
            refine ⟨5812641985921566519396785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15500378629124177385058093 5812641985921566519396785)
            ·
              refine ⟨4359481489441174889547589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5812641985921566519396785 4359481489441174889547589)
              ·
                refine ⟨817402779270220291790173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4359481489441174889547589 817402779270220291790173)
                ·
                  refine ⟨306526042226332609421315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 817402779270220291790173 306526042226332609421315)
                  ·
                    rfl

theorem cell20_671577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 2, 4, 3].length) (baseStart_671577 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_671577 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_671577 prefixEnd_671577 := by exact prefixLift 671577
  have htrace : WordTrace (prefixWord ++ tailWord_671577) baseStart_671577 baseEnd_671577 := by
    simpa [prefixWord, tailWord_671577, baseEnd_671577] using wordTrace_append hprefix tailTrace_671577
  have hstable : (prefixWord ++ tailWord_671577).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_671577).length < 2 ^ (prefixWord ++ tailWord_671577).sum := by decide
  have hdescent : baseEnd_671577 < baseStart_671577 := by decide
  rcases family_descends (prefixWord ++ tailWord_671577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_671638 : List Nat := [5, 3, 1, 1, 3, 1, 1, 5]
def baseStart_671638 : Nat := 118140960795 + 671638 * 2 ^ 59
def prefixEnd_671638 : Nat := 4983230072969 + 3 ^ 40 * 671638 * 2
def baseEnd_671638 : Nat := 102184628096162502795911

theorem tailTrace_671638 : CollatzResearch.WordTrace tailWord_671638 prefixEnd_671638 102184628096162502795911 := by
  unfold tailWord_671638
  simp only [CollatzResearch.WordTrace]
  refine ⟨1531040646298606717702973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 16331100227185138322165045 1531040646298606717702973)
  ·
    refine ⟨574140242361977519138615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1531040646298606717702973 574140242361977519138615)
    ·
      refine ⟨861210363542966278707923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 574140242361977519138615 861210363542966278707923)
      ·
        refine ⟨1291815545314449418061885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 861210363542966278707923 1291815545314449418061885)
        ·
          refine ⟨484430829492918531773207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1291815545314449418061885 484430829492918531773207)
          ·
            refine ⟨726646244239377797659811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 484430829492918531773207 726646244239377797659811)
            ·
              refine ⟨1089969366359066696489717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 726646244239377797659811 1089969366359066696489717)
              ·
                refine ⟨102184628096162502795911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1089969366359066696489717 102184628096162502795911)
                ·
                  rfl

theorem cell20_671638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 3, 1, 1, 5].length) (baseStart_671638 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_671638 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_671638 prefixEnd_671638 := by exact prefixLift 671638
  have htrace : WordTrace (prefixWord ++ tailWord_671638) baseStart_671638 baseEnd_671638 := by
    simpa [prefixWord, tailWord_671638, baseEnd_671638] using wordTrace_append hprefix tailTrace_671638
  have hstable : (prefixWord ++ tailWord_671638).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_671638).length < 2 ^ (prefixWord ++ tailWord_671638).sum := by decide
  have hdescent : baseEnd_671638 < baseStart_671638 := by decide
  rcases family_descends (prefixWord ++ tailWord_671638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_671781 : List Nat := [1, 3, 1, 2, 2, 3, 2, 6]
def baseStart_671781 : Nat := 118140960795 + 671781 * 2 ^ 59
def prefixEnd_671781 : Nat := 4983230072969 + 3 ^ 40 * 671781 * 2
def baseEnd_671781 : Nat := 102206384461671522206827

theorem tailTrace_671781 : CollatzResearch.WordTrace tailWord_671781 prefixEnd_671781 102206384461671522206827 := by
  unfold tailWord_671781
  simp only [CollatzResearch.WordTrace]
  refine ⟨24501865979259642905703197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16334577319506428603802131 24501865979259642905703197)
  ·
    refine ⟨9188199742222366089638699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24501865979259642905703197 9188199742222366089638699)
    ·
      refine ⟨13782299613333549134458049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9188199742222366089638699 13782299613333549134458049)
      ·
        refine ⟨10336724710000161850843537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13782299613333549134458049 10336724710000161850843537)
        ·
          refine ⟨7752543532500121388132653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10336724710000161850843537 7752543532500121388132653)
          ·
            refine ⟨2907203824687545520549745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7752543532500121388132653 2907203824687545520549745)
            ·
              refine ⟨2180402868515659140412309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2907203824687545520549745 2180402868515659140412309)
              ·
                refine ⟨102206384461671522206827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2180402868515659140412309 102206384461671522206827)
                ·
                  rfl

theorem cell20_671781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 2, 6].length) (baseStart_671781 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_671781 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_671781 prefixEnd_671781 := by exact prefixLift 671781
  have htrace : WordTrace (prefixWord ++ tailWord_671781) baseStart_671781 baseEnd_671781 := by
    simpa [prefixWord, tailWord_671781, baseEnd_671781] using wordTrace_append hprefix tailTrace_671781
  have hstable : (prefixWord ++ tailWord_671781).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_671781).length < 2 ^ (prefixWord ++ tailWord_671781).sum := by decide
  have hdescent : baseEnd_671781 < baseStart_671781 := by decide
  rcases family_descends (prefixWord ++ tailWord_671781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_671788 : List Nat := [2, 2, 1, 1, 1, 2, 2, 4, 5]
def baseStart_671788 : Nat := 118140960795 + 671788 * 2 ^ 59
def prefixEnd_671788 : Nat := 4983230072969 + 3 ^ 40 * 671788 * 2
def baseEnd_671788 : Nat := 306622348375753653387119

theorem tailTrace_671788 : CollatzResearch.WordTrace tailWord_671788 prefixEnd_671788 306622348375753653387119 := by
  unfold tailWord_671788
  simp only [CollatzResearch.WordTrace]
  refine ⟨12251060645117141550604009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16334747526822855400805345 12251060645117141550604009)
  ·
    refine ⟨9188295483837856162953007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12251060645117141550604009 9188295483837856162953007)
    ·
      refine ⟨13782443225756784244429511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9188295483837856162953007 13782443225756784244429511)
      ·
        refine ⟨20673664838635176366644267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13782443225756784244429511 20673664838635176366644267)
        ·
          refine ⟨31010497257952764549966401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20673664838635176366644267 31010497257952764549966401)
          ·
            refine ⟨23257872943464573412474801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31010497257952764549966401 23257872943464573412474801)
            ·
              refine ⟨17443404707598430059356101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23257872943464573412474801 17443404707598430059356101)
              ·
                refine ⟨3270638382674705636129269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17443404707598430059356101 3270638382674705636129269)
                ·
                  refine ⟨306622348375753653387119, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3270638382674705636129269 306622348375753653387119)
                  ·
                    rfl

theorem cell20_671788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 5].length) (baseStart_671788 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_671788 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_671788 prefixEnd_671788 := by exact prefixLift 671788
  have htrace : WordTrace (prefixWord ++ tailWord_671788) baseStart_671788 baseEnd_671788 := by
    simpa [prefixWord, tailWord_671788, baseEnd_671788] using wordTrace_append hprefix tailTrace_671788
  have hstable : (prefixWord ++ tailWord_671788).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_671788).length < 2 ^ (prefixWord ++ tailWord_671788).sum := by decide
  have hdescent : baseEnd_671788 < baseStart_671788 := by decide
  rcases family_descends (prefixWord ++ tailWord_671788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_671808 : List Nat := [2, 1, 1, 2, 2, 4, 4, 2, 2]
def baseStart_671808 : Nat := 118140960795 + 671808 * 2 ^ 59
def prefixEnd_671808 : Nat := 4983230072969 + 3 ^ 40 * 671808 * 2
def baseEnd_671808 : Nat := 306631476920722472720371

theorem tailTrace_671808 : CollatzResearch.WordTrace tailWord_671808 prefixEnd_671808 306631476920722472720371 := by
  unfold tailWord_671808
  simp only [CollatzResearch.WordTrace]
  refine ⟨12251425375080913258468039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16335233833441217677957385 12251425375080913258468039)
  ·
    refine ⟨18377138062621369887702059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12251425375080913258468039 18377138062621369887702059)
    ·
      refine ⟨27565707093932054831553089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18377138062621369887702059 27565707093932054831553089)
      ·
        refine ⟨20674280320449041123664817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27565707093932054831553089 20674280320449041123664817)
        ·
          refine ⟨15505710240336780842748613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20674280320449041123664817 15505710240336780842748613)
          ·
            refine ⟨2907320670063146408015365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15505710240336780842748613 2907320670063146408015365)
            ·
              refine ⟨545122625636839951502881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2907320670063146408015365 545122625636839951502881)
              ·
                refine ⟨408841969227629963627161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 545122625636839951502881 408841969227629963627161)
                ·
                  refine ⟨306631476920722472720371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 408841969227629963627161 306631476920722472720371)
                  ·
                    rfl

theorem cell20_671808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 4, 2, 2].length) (baseStart_671808 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_671808 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_671808 prefixEnd_671808 := by exact prefixLift 671808
  have htrace : WordTrace (prefixWord ++ tailWord_671808) baseStart_671808 baseEnd_671808 := by
    simpa [prefixWord, tailWord_671808, baseEnd_671808] using wordTrace_append hprefix tailTrace_671808
  have hstable : (prefixWord ++ tailWord_671808).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_671808).length < 2 ^ (prefixWord ++ tailWord_671808).sum := by decide
  have hdescent : baseEnd_671808 < baseStart_671808 := by decide
  rcases family_descends (prefixWord ++ tailWord_671808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_671918 : List Nat := [4, 1, 4, 2, 2, 1, 1, 1, 4]
def baseStart_671918 : Nat := 118140960795 + 671918 * 2 ^ 59
def prefixEnd_671918 : Nat := 4983230072969 + 3 ^ 40 * 671918 * 2
def baseEnd_671918 : Nat := 306681683918050979053255

theorem tailTrace_671918 : CollatzResearch.WordTrace tailWord_671918 prefixEnd_671918 306681683918050979053255 := by
  unfold tailWord_671918
  simp only [CollatzResearch.WordTrace]
  refine ⟨3063357847470414412930051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16337908519842210202293605 3063357847470414412930051)
  ·
    refine ⟨4595036771205621619395077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3063357847470414412930051 4595036771205621619395077)
    ·
      refine ⟨861569394601054053636577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4595036771205621619395077 861569394601054053636577)
      ·
        refine ⟨646177045950790540227433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 861569394601054053636577 646177045950790540227433)
        ·
          refine ⟨484632784463092905170575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 646177045950790540227433 484632784463092905170575)
          ·
            refine ⟨726949176694639357755863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 484632784463092905170575 726949176694639357755863)
            ·
              refine ⟨1090423765041959036633795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 726949176694639357755863 1090423765041959036633795)
              ·
                refine ⟨1635635647562938554950693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1090423765041959036633795 1635635647562938554950693)
                ·
                  refine ⟨306681683918050979053255, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1635635647562938554950693 306681683918050979053255)
                  ·
                    rfl

theorem cell20_671918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 2, 1, 1, 1, 4].length) (baseStart_671918 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_671918 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_671918 prefixEnd_671918 := by exact prefixLift 671918
  have htrace : WordTrace (prefixWord ++ tailWord_671918) baseStart_671918 baseEnd_671918 := by
    simpa [prefixWord, tailWord_671918, baseEnd_671918] using wordTrace_append hprefix tailTrace_671918
  have hstable : (prefixWord ++ tailWord_671918).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_671918).length < 2 ^ (prefixWord ++ tailWord_671918).sum := by decide
  have hdescent : baseEnd_671918 < baseStart_671918 := by decide
  rcases family_descends (prefixWord ++ tailWord_671918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_671922 : List Nat := [3, 2, 1, 1, 1, 3, 5, 2, 2]
def baseStart_671922 : Nat := 118140960795 + 671922 * 2 ^ 59
def prefixEnd_671922 : Nat := 4983230072969 + 3 ^ 40 * 671922 * 2
def baseEnd_671922 : Nat := 306683509627044742919905

theorem tailTrace_671922 : CollatzResearch.WordTrace tailWord_671922 prefixEnd_671922 306683509627044742919905 := by
  unfold tailWord_671922
  simp only [CollatzResearch.WordTrace]
  refine ⟨6126752167937205996646505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16338005781165882657724013 6126752167937205996646505)
  ·
    refine ⟨4595064125952904497484879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6126752167937205996646505 4595064125952904497484879)
    ·
      refine ⟨6892596188929356746227319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4595064125952904497484879 6892596188929356746227319)
      ·
        refine ⟨10338894283394035119340979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6892596188929356746227319 10338894283394035119340979)
        ·
          refine ⟨15508341425091052679011469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10338894283394035119340979 15508341425091052679011469)
          ·
            refine ⟨5815628034409144754629301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15508341425091052679011469 5815628034409144754629301)
            ·
              refine ⟨545215128225857320746497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5815628034409144754629301 545215128225857320746497)
              ·
                refine ⟨408911346169392990559873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 545215128225857320746497 408911346169392990559873)
                ·
                  refine ⟨306683509627044742919905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 408911346169392990559873 306683509627044742919905)
                  ·
                    rfl

theorem cell20_671922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 5, 2, 2].length) (baseStart_671922 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_671922 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_671922 prefixEnd_671922 := by exact prefixLift 671922
  have htrace : WordTrace (prefixWord ++ tailWord_671922) baseStart_671922 baseEnd_671922 := by
    simpa [prefixWord, tailWord_671922, baseEnd_671922] using wordTrace_append hprefix tailTrace_671922
  have hstable : (prefixWord ++ tailWord_671922).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_671922).length < 2 ^ (prefixWord ++ tailWord_671922).sum := by decide
  have hdescent : baseEnd_671922 < baseStart_671922 := by decide
  rcases family_descends (prefixWord ++ tailWord_671922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_671932 : List Nat := [2, 2, 2, 3, 4, 1, 2, 1, 3]
def baseStart_671932 : Nat := 118140960795 + 671932 * 2 ^ 59
def prefixEnd_671932 : Nat := 4983230072969 + 3 ^ 40 * 671932 * 2
def baseEnd_671932 : Nat := 306688073899529152586531

theorem tailTrace_671932 : CollatzResearch.WordTrace tailWord_671932 prefixEnd_671932 306688073899529152586531 := by
  unfold tailWord_671932
  simp only [CollatzResearch.WordTrace]
  refine ⟨12253686700856297847225025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16338248934475063796300033 12253686700856297847225025)
  ·
    refine ⟨9190265025642223385418769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12253686700856297847225025 9190265025642223385418769)
    ·
      refine ⟨6892698769231667539064077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9190265025642223385418769 6892698769231667539064077)
      ·
        refine ⟨2584762038461875327149029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6892698769231667539064077 2584762038461875327149029)
        ·
          refine ⟨484642882211601623840443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2584762038461875327149029 484642882211601623840443)
          ·
            refine ⟨726964323317402435760665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 484642882211601623840443 726964323317402435760665)
            ·
              refine ⟨545223242488051826820499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 726964323317402435760665 545223242488051826820499)
              ·
                refine ⟨817834863732077740230749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 545223242488051826820499 817834863732077740230749)
                ·
                  refine ⟨306688073899529152586531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 817834863732077740230749 306688073899529152586531)
                  ·
                    rfl

theorem cell20_671932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 4, 1, 2, 1, 3].length) (baseStart_671932 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_671932 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_671932 prefixEnd_671932 := by exact prefixLift 671932
  have htrace : WordTrace (prefixWord ++ tailWord_671932) baseStart_671932 baseEnd_671932 := by
    simpa [prefixWord, tailWord_671932, baseEnd_671932] using wordTrace_append hprefix tailTrace_671932
  have hstable : (prefixWord ++ tailWord_671932).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_671932).length < 2 ^ (prefixWord ++ tailWord_671932).sum := by decide
  have hdescent : baseEnd_671932 < baseStart_671932 := by decide
  rcases family_descends (prefixWord ++ tailWord_671932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_671936 : List Nat := [2, 1, 1, 2, 5, 1, 4, 1, 3]
def baseStart_671936 : Nat := 118140960795 + 671936 * 2 ^ 59
def prefixEnd_671936 : Nat := 4983230072969 + 3 ^ 40 * 671936 * 2
def baseEnd_671936 : Nat := 306689899608522916453181

theorem tailTrace_671936 : CollatzResearch.WordTrace tailWord_671936 prefixEnd_671936 306689899608522916453181 := by
  unfold tailWord_671936
  simp only [CollatzResearch.WordTrace]
  refine ⟨12253759646849052188797831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16338346195798736251730441 12253759646849052188797831)
  ·
    refine ⟨18380639470273578283196747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12253759646849052188797831 18380639470273578283196747)
    ·
      refine ⟨27570959205410367424795121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18380639470273578283196747 27570959205410367424795121)
      ·
        refine ⟨20678219404057775568596341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27570959205410367424795121 20678219404057775568596341)
        ·
          refine ⟨1938583069130416459555907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 20678219404057775568596341 1938583069130416459555907)
          ·
            refine ⟨2907874603695624689333861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1938583069130416459555907 2907874603695624689333861)
            ·
              refine ⟨545226488192929629250099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2907874603695624689333861 545226488192929629250099)
              ·
                refine ⟨817839732289394443875149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 545226488192929629250099 817839732289394443875149)
                ·
                  refine ⟨306689899608522916453181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 817839732289394443875149 306689899608522916453181)
                  ·
                    rfl

theorem cell20_671936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 4, 1, 3].length) (baseStart_671936 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_671936 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_671936 prefixEnd_671936 := by exact prefixLift 671936
  have htrace : WordTrace (prefixWord ++ tailWord_671936) baseStart_671936 baseEnd_671936 := by
    simpa [prefixWord, tailWord_671936, baseEnd_671936] using wordTrace_append hprefix tailTrace_671936
  have hstable : (prefixWord ++ tailWord_671936).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_671936).length < 2 ^ (prefixWord ++ tailWord_671936).sum := by decide
  have hdescent : baseEnd_671936 < baseStart_671936 := by decide
  rcases family_descends (prefixWord ++ tailWord_671936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_671947 : List Nat := [1, 1, 1, 1, 3, 2, 4, 1, 6]
def baseStart_671947 : Nat := 118140960795 + 671947 * 2 ^ 59
def prefixEnd_671947 : Nat := 4983230072969 + 3 ^ 40 * 671947 * 2
def baseEnd_671947 : Nat := 306694920308255767086469

theorem tailTrace_671947 : CollatzResearch.WordTrace tailWord_671947 prefixEnd_671947 306694920308255767086469 := by
  unfold tailWord_671947
  simp only [CollatzResearch.WordTrace]
  refine ⟨24507920496658253256246095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16338613664438835504164063 24507920496658253256246095)
  ·
    refine ⟨36761880744987379884369143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24507920496658253256246095 36761880744987379884369143)
    ·
      refine ⟨55142821117481069826553715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36761880744987379884369143 55142821117481069826553715)
      ·
        refine ⟨82714231676221604739830573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55142821117481069826553715 82714231676221604739830573)
        ·
          refine ⟨31017836878583101777436465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 82714231676221604739830573 31017836878583101777436465)
          ·
            refine ⟨23263377658937326333077349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31017836878583101777436465 23263377658937326333077349)
            ·
              refine ⟨4361883311050748687452003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23263377658937326333077349 4361883311050748687452003)
              ·
                refine ⟨6542824966576123031178005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4361883311050748687452003 6542824966576123031178005)
                ·
                  refine ⟨306694920308255767086469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6542824966576123031178005 306694920308255767086469)
                  ·
                    rfl

theorem cell20_671947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 4, 1, 6].length) (baseStart_671947 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_671947 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_671947 prefixEnd_671947 := by exact prefixLift 671947
  have htrace : WordTrace (prefixWord ++ tailWord_671947) baseStart_671947 baseEnd_671947 := by
    simpa [prefixWord, tailWord_671947, baseEnd_671947] using wordTrace_append hprefix tailTrace_671947
  have hstable : (prefixWord ++ tailWord_671947).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_671947).length < 2 ^ (prefixWord ++ tailWord_671947).sum := by decide
  have hdescent : baseEnd_671947 < baseStart_671947 := by decide
  rcases family_descends (prefixWord ++ tailWord_671947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_671971 : List Nat := [1, 1, 1, 8, 9]
def baseStart_671971 : Nat := 118140960795 + 671971 * 2 ^ 59
def prefixEnd_671971 : Nat := 4983230072969 + 3 ^ 40 * 671971 * 2
def baseEnd_671971 : Nat := 3786492278545905559091

theorem tailTrace_671971 : CollatzResearch.WordTrace tailWord_671971 prefixEnd_671971 3786492278545905559091 := by
  unfold tailWord_671971
  simp only [CollatzResearch.WordTrace]
  refine ⟨24508795848571305355119767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16339197232380870236746511 24508795848571305355119767)
  ·
    refine ⟨36763193772856958032679651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24508795848571305355119767 36763193772856958032679651)
    ·
      refine ⟨55144790659285437049019477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36763193772856958032679651 55144790659285437049019477)
      ·
        refine ⟨646228015538501215418197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 55144790659285437049019477 646228015538501215418197)
        ·
          refine ⟨3786492278545905559091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 9 646228015538501215418197 3786492278545905559091)
          ·
            rfl

theorem cell20_671971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 9].length) (baseStart_671971 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_671971 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_671971 prefixEnd_671971 := by exact prefixLift 671971
  have htrace : WordTrace (prefixWord ++ tailWord_671971) baseStart_671971 baseEnd_671971 := by
    simpa [prefixWord, tailWord_671971, baseEnd_671971] using wordTrace_append hprefix tailTrace_671971
  have hstable : (prefixWord ++ tailWord_671971).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_671971).length < 2 ^ (prefixWord ++ tailWord_671971).sum := by decide
  have hdescent : baseEnd_671971 < baseStart_671971 := by decide
  rcases family_descends (prefixWord ++ tailWord_671971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_672029 : List Nat := [1, 4, 2, 3, 2, 2, 1, 2, 3]
def baseStart_672029 : Nat := 118140960795 + 672029 * 2 ^ 59
def prefixEnd_672029 : Nat := 4983230072969 + 3 ^ 40 * 672029 * 2
def baseEnd_672029 : Nat := 306732347342627926352801

theorem tailTrace_672029 : CollatzResearch.WordTrace tailWord_672029 prefixEnd_672029 306732347342627926352801 := by
  unfold tailWord_672029
  simp only [CollatzResearch.WordTrace]
  refine ⟨24510911282361181260731141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16340607521574120840487427 24510911282361181260731141)
  ·
    refine ⟨4595795865442721486387089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24510911282361181260731141 4595795865442721486387089)
    ·
      refine ⟨3446846899082041114790317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4595795865442721486387089 3446846899082041114790317)
      ·
        refine ⟨1292567587155765418046369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3446846899082041114790317 1292567587155765418046369)
        ·
          refine ⟨969425690366824063534777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1292567587155765418046369 969425690366824063534777)
          ·
            refine ⟨727069267775118047651083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 969425690366824063534777 727069267775118047651083)
            ·
              refine ⟨1090603901662677071476625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 727069267775118047651083 1090603901662677071476625)
              ·
                refine ⟨817952926247007803607469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1090603901662677071476625 817952926247007803607469)
                ·
                  refine ⟨306732347342627926352801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 817952926247007803607469 306732347342627926352801)
                  ·
                    rfl

theorem cell20_672029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 2, 1, 2, 3].length) (baseStart_672029 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_672029 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_672029 prefixEnd_672029 := by exact prefixLift 672029
  have htrace : WordTrace (prefixWord ++ tailWord_672029) baseStart_672029 baseEnd_672029 := by
    simpa [prefixWord, tailWord_672029, baseEnd_672029] using wordTrace_append hprefix tailTrace_672029
  have hstable : (prefixWord ++ tailWord_672029).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_672029).length < 2 ^ (prefixWord ++ tailWord_672029).sum := by decide
  have hdescent : baseEnd_672029 < baseStart_672029 := by decide
  rcases family_descends (prefixWord ++ tailWord_672029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_672033 : List Nat := [1, 2, 3, 2, 1, 1, 5, 2, 3]
def baseStart_672033 : Nat := 118140960795 + 672033 * 2 ^ 59
def prefixEnd_672033 : Nat := 4983230072969 + 3 ^ 40 * 672033 * 2
def baseEnd_672033 : Nat := 306734173051621690219451

theorem tailTrace_672033 : CollatzResearch.WordTrace tailWord_672033 prefixEnd_672033 306734173051621690219451 := by
  unfold tailWord_672033
  simp only [CollatzResearch.WordTrace]
  refine ⟨24511057174346689943876753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16340704782897793295917835 24511057174346689943876753)
  ·
    refine ⟨18383292880760017457907565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24511057174346689943876753 18383292880760017457907565)
    ·
      refine ⟨6893734830285006546715337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18383292880760017457907565 6893734830285006546715337)
      ·
        refine ⟨5170301122713754910036503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6893734830285006546715337 5170301122713754910036503)
        ·
          refine ⟨7755451684070632365054755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5170301122713754910036503 7755451684070632365054755)
          ·
            refine ⟨11633177526105948547582133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7755451684070632365054755 11633177526105948547582133)
            ·
              refine ⟨1090610393072432676335825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 11633177526105948547582133 1090610393072432676335825)
              ·
                refine ⟨817957794804324507251869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1090610393072432676335825 817957794804324507251869)
                ·
                  refine ⟨306734173051621690219451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 817957794804324507251869 306734173051621690219451)
                  ·
                    rfl

theorem cell20_672033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 5, 2, 3].length) (baseStart_672033 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_672033 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_672033 prefixEnd_672033 := by exact prefixLift 672033
  have htrace : WordTrace (prefixWord ++ tailWord_672033) baseStart_672033 baseEnd_672033 := by
    simpa [prefixWord, tailWord_672033, baseEnd_672033] using wordTrace_append hprefix tailTrace_672033
  have hstable : (prefixWord ++ tailWord_672033).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_672033).length < 2 ^ (prefixWord ++ tailWord_672033).sum := by decide
  have hdescent : baseEnd_672033 < baseStart_672033 := by decide
  rcases family_descends (prefixWord ++ tailWord_672033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_672046 : List Nat := [4, 1, 3, 3, 1, 1, 3, 1, 3]
def baseStart_672046 : Nat := 118140960795 + 672046 * 2 ^ 59
def prefixEnd_672046 : Nat := 4983230072969 + 3 ^ 40 * 672046 * 2
def baseEnd_672046 : Nat := 306740106605851422786065

theorem tailTrace_672046 : CollatzResearch.WordTrace tailWord_672046 prefixEnd_672046 306740106605851422786065 := by
  unfold tailWord_672046
  simp only [CollatzResearch.WordTrace]
  refine ⟨3063941415412449145512499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16341020882199728776066661 3063941415412449145512499)
  ·
    refine ⟨4595912123118673718268749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3063941415412449145512499 4595912123118673718268749)
    ·
      refine ⟨1723467046169502644350781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4595912123118673718268749 1723467046169502644350781)
      ·
        refine ⟨646300142313563491631543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1723467046169502644350781 646300142313563491631543)
        ·
          refine ⟨969450213470345237447315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 646300142313563491631543 969450213470345237447315)
          ·
            refine ⟨1454175320205517856170973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 969450213470345237447315 1454175320205517856170973)
            ·
              refine ⟨545315745077069196064115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1454175320205517856170973 545315745077069196064115)
              ·
                refine ⟨817973617615603794096173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 545315745077069196064115 817973617615603794096173)
                ·
                  refine ⟨306740106605851422786065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 817973617615603794096173 306740106605851422786065)
                  ·
                    rfl

theorem cell20_672046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 1, 3, 1, 3].length) (baseStart_672046 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_672046 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_672046 prefixEnd_672046 := by exact prefixLift 672046
  have htrace : WordTrace (prefixWord ++ tailWord_672046) baseStart_672046 baseEnd_672046 := by
    simpa [prefixWord, tailWord_672046, baseEnd_672046] using wordTrace_append hprefix tailTrace_672046
  have hstable : (prefixWord ++ tailWord_672046).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_672046).length < 2 ^ (prefixWord ++ tailWord_672046).sum := by decide
  have hdescent : baseEnd_672046 < baseStart_672046 := by decide
  rcases family_descends (prefixWord ++ tailWord_672046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_672109 : List Nat := [1, 5, 1, 1, 1, 2, 3, 3, 3]
def baseStart_672109 : Nat := 118140960795 + 672109 * 2 ^ 59
def prefixEnd_672109 : Nat := 4983230072969 + 3 ^ 40 * 672109 * 2
def baseEnd_672109 : Nat := 306768861522503203685807

theorem tailTrace_672109 : CollatzResearch.WordTrace tailWord_672109 prefixEnd_672109 306768861522503203685807 := by
  unfold tailWord_672109
  simp only [CollatzResearch.WordTrace]
  refine ⟨24513829122071354923643381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16342552748047569949095587 24513829122071354923643381)
  ·
    refine ⟨2298171480194189524091567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 24513829122071354923643381 2298171480194189524091567)
    ·
      refine ⟨3447257220291284286137351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2298171480194189524091567 3447257220291284286137351)
      ·
        refine ⟨5170885830436926429206027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3447257220291284286137351 5170885830436926429206027)
        ·
          refine ⟨7756328745655389643809041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5170885830436926429206027 7756328745655389643809041)
          ·
            refine ⟨5817246559241542232856781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7756328745655389643809041 5817246559241542232856781)
            ·
              refine ⟨2181467459715578337321293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5817246559241542232856781 2181467459715578337321293)
              ·
                refine ⟨818050297393341876495485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2181467459715578337321293 818050297393341876495485)
                ·
                  refine ⟨306768861522503203685807, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 818050297393341876495485 306768861522503203685807)
                  ·
                    rfl

theorem cell20_672109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 3, 3, 3].length) (baseStart_672109 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_672109 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_672109 prefixEnd_672109 := by exact prefixLift 672109
  have htrace : WordTrace (prefixWord ++ tailWord_672109) baseStart_672109 baseEnd_672109 := by
    simpa [prefixWord, tailWord_672109, baseEnd_672109] using wordTrace_append hprefix tailTrace_672109
  have hstable : (prefixWord ++ tailWord_672109).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_672109).length < 2 ^ (prefixWord ++ tailWord_672109).sum := by decide
  have hdescent : baseEnd_672109 < baseStart_672109 := by decide
  rcases family_descends (prefixWord ++ tailWord_672109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_672157 : List Nat := [1, 4, 2, 1, 5, 1, 1, 5]
def baseStart_672157 : Nat := 118140960795 + 672157 * 2 ^ 59
def prefixEnd_672157 : Nat := 4983230072969 + 3 ^ 40 * 672157 * 2
def baseEnd_672157 : Nat := 102263590010142790028537

theorem tailTrace_672157 : CollatzResearch.WordTrace tailWord_672157 prefixEnd_672157 102263590010142790028537 := by
  unfold tailWord_672157
  simp only [CollatzResearch.WordTrace]
  refine ⟨24515579825897459121390725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16343719883931639414260483 24515579825897459121390725)
  ·
    refine ⟨4596671217355773585260761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24515579825897459121390725 4596671217355773585260761)
    ·
      refine ⟨3447503413016830188945571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4596671217355773585260761 3447503413016830188945571)
      ·
        refine ⟨5171255119525245283418357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3447503413016830188945571 5171255119525245283418357)
        ·
          refine ⟨484805167455491745320471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 5171255119525245283418357 484805167455491745320471)
          ·
            refine ⟨727207751183237617980707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 484805167455491745320471 727207751183237617980707)
            ·
              refine ⟨1090811626774856426971061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 727207751183237617980707 1090811626774856426971061)
              ·
                refine ⟨102263590010142790028537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1090811626774856426971061 102263590010142790028537)
                ·
                  rfl

theorem cell20_672157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 5, 1, 1, 5].length) (baseStart_672157 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_672157 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_672157 prefixEnd_672157 := by exact prefixLift 672157
  have htrace : WordTrace (prefixWord ++ tailWord_672157) baseStart_672157 baseEnd_672157 := by
    simpa [prefixWord, tailWord_672157, baseEnd_672157] using wordTrace_append hprefix tailTrace_672157
  have hstable : (prefixWord ++ tailWord_672157).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_672157).length < 2 ^ (prefixWord ++ tailWord_672157).sum := by decide
  have hdescent : baseEnd_672157 < baseStart_672157 := by decide
  rcases family_descends (prefixWord ++ tailWord_672157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_672188 : List Nat := [2, 2, 2, 4, 1, 2, 2, 3, 2]
def baseStart_672188 : Nat := 118140960795 + 672188 * 2 ^ 59
def prefixEnd_672188 : Nat := 4983230072969 + 3 ^ 40 * 672188 * 2
def baseEnd_672188 : Nat := 306804919275130040052151

theorem tailTrace_672188 : CollatzResearch.WordTrace tailWord_672188 prefixEnd_672188 306804919275130040052151 := by
  unfold tailWord_672188
  simp only [CollatzResearch.WordTrace]
  refine ⟨12258355244392575707884609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16344473659190100943846145 12258355244392575707884609)
  ·
    refine ⟨9193766433294431780913457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12258355244392575707884609 9193766433294431780913457)
    ·
      refine ⟨6895324824970823835685093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9193766433294431780913457 6895324824970823835685093)
      ·
        refine ⟨1292873404682029469190955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6895324824970823835685093 1292873404682029469190955)
        ·
          refine ⟨1939310107023044203786433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1292873404682029469190955 1939310107023044203786433)
          ·
            refine ⟨1454482580267283152839825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1939310107023044203786433 1454482580267283152839825)
            ·
              refine ⟨1090861935200462364629869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1454482580267283152839825 1090861935200462364629869)
              ·
                refine ⟨409073225700173386736201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1090861935200462364629869 409073225700173386736201)
                ·
                  refine ⟨306804919275130040052151, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 409073225700173386736201 306804919275130040052151)
                  ·
                    rfl

theorem cell20_672188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 2, 2, 3, 2].length) (baseStart_672188 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_672188 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_672188 prefixEnd_672188 := by exact prefixLift 672188
  have htrace : WordTrace (prefixWord ++ tailWord_672188) baseStart_672188 baseEnd_672188 := by
    simpa [prefixWord, tailWord_672188, baseEnd_672188] using wordTrace_append hprefix tailTrace_672188
  have hstable : (prefixWord ++ tailWord_672188).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_672188).length < 2 ^ (prefixWord ++ tailWord_672188).sum := by decide
  have hdescent : baseEnd_672188 < baseStart_672188 := by decide
  rcases family_descends (prefixWord ++ tailWord_672188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_672268 : List Nat := [2, 2, 1, 2, 4, 1, 3, 1, 4]
def baseStart_672268 : Nat := 118140960795 + 672268 * 2 ^ 59
def prefixEnd_672268 : Nat := 4983230072969 + 3 ^ 40 * 672268 * 2
def baseEnd_672268 : Nat := 306841433455005317385157

theorem tailTrace_672268 : CollatzResearch.WordTrace tailWord_672268 prefixEnd_672268 306841433455005317385157 := by
  unfold tailWord_672268
  simp only [CollatzResearch.WordTrace]
  refine ⟨12259814164247662539340729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16346418885663550052454305 12259814164247662539340729)
  ·
    refine ⟨9194860623185746904505547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12259814164247662539340729 9194860623185746904505547)
    ·
      refine ⟨13792290934778620356758321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9194860623185746904505547 13792290934778620356758321)
      ·
        refine ⟨10344218201083965267568741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13792290934778620356758321 10344218201083965267568741)
        ·
          refine ⟨1939540912703243487669139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10344218201083965267568741 1939540912703243487669139)
          ·
            refine ⟨2909311369054865231503709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1939540912703243487669139 2909311369054865231503709)
            ·
              refine ⟨1090991763395574461813891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2909311369054865231503709 1090991763395574461813891)
              ·
                refine ⟨1636487645093361692720837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1090991763395574461813891 1636487645093361692720837)
                ·
                  refine ⟨306841433455005317385157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1636487645093361692720837 306841433455005317385157)
                  ·
                    rfl

theorem cell20_672268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 3, 1, 4].length) (baseStart_672268 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_672268 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_672268 prefixEnd_672268 := by exact prefixLift 672268
  have htrace : WordTrace (prefixWord ++ tailWord_672268) baseStart_672268 baseEnd_672268 := by
    simpa [prefixWord, tailWord_672268, baseEnd_672268] using wordTrace_append hprefix tailTrace_672268
  have hstable : (prefixWord ++ tailWord_672268).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_672268).length < 2 ^ (prefixWord ++ tailWord_672268).sum := by decide
  have hdescent : baseEnd_672268 < baseStart_672268 := by decide
  rcases family_descends (prefixWord ++ tailWord_672268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_672289 : List Nat := [1, 2, 3, 2, 2, 1, 2, 1, 6]
def baseStart_672289 : Nat := 118140960795 + 672289 * 2 ^ 59
def prefixEnd_672289 : Nat := 4983230072969 + 3 ^ 40 * 672289 * 2
def baseEnd_672289 : Nat := 306851018427222577685071

theorem tailTrace_672289 : CollatzResearch.WordTrace tailWord_672289 prefixEnd_672289 306851018427222577685071 := by
  unfold tailWord_672289
  simp only [CollatzResearch.WordTrace]
  refine ⟨24520394261419245665195921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16346929507612830443463947 24520394261419245665195921)
  ·
    refine ⟨18390295696064434248896941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24520394261419245665195921 18390295696064434248896941)
    ·
      refine ⟨6896360886024162843336353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18390295696064434248896941 6896360886024162843336353)
      ·
        refine ⟨5172270664518122132502265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6896360886024162843336353 5172270664518122132502265)
        ·
          refine ⟨3879202998388591599376699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5172270664518122132502265 3879202998388591599376699)
          ·
            refine ⟨5818804497582887399065049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3879202998388591599376699 5818804497582887399065049)
            ·
              refine ⟨4364103373187165549298787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5818804497582887399065049 4364103373187165549298787)
              ·
                refine ⟨6546155059780748323948181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4364103373187165549298787 6546155059780748323948181)
                ·
                  refine ⟨306851018427222577685071, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6546155059780748323948181 306851018427222577685071)
                  ·
                    rfl

theorem cell20_672289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 2, 1, 6].length) (baseStart_672289 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_672289 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_672289 prefixEnd_672289 := by exact prefixLift 672289
  have htrace : WordTrace (prefixWord ++ tailWord_672289) baseStart_672289 baseEnd_672289 := by
    simpa [prefixWord, tailWord_672289, baseEnd_672289] using wordTrace_append hprefix tailTrace_672289
  have hstable : (prefixWord ++ tailWord_672289).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_672289).length < 2 ^ (prefixWord ++ tailWord_672289).sum := by decide
  have hdescent : baseEnd_672289 < baseStart_672289 := by decide
  rcases family_descends (prefixWord ++ tailWord_672289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_672320 : List Nat := [2, 1, 1, 2, 2, 2, 3, 4, 3]
def baseStart_672320 : Nat := 118140960795 + 672320 * 2 ^ 59
def prefixEnd_672320 : Nat := 4983230072969 + 3 ^ 40 * 672320 * 2
def baseEnd_672320 : Nat := 306865167671924247651611

theorem tailTrace_672320 : CollatzResearch.WordTrace tailWord_672320 prefixEnd_672320 306865167671924247651611 := by
  unfold tailWord_672320
  simp only [CollatzResearch.WordTrace]
  refine ⟨12260762462153468979787207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16347683282871291973049609 12260762462153468979787207)
  ·
    refine ⟨18391143693230203469680811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12260762462153468979787207 18391143693230203469680811)
    ·
      refine ⟨27586715539845305204521217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18391143693230203469680811 27586715539845305204521217)
      ·
        refine ⟨20690036654883978903390913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27586715539845305204521217 20690036654883978903390913)
        ·
          refine ⟨15517527491162984177543185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20690036654883978903390913 15517527491162984177543185)
          ·
            refine ⟨11638145618372238133157389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15517527491162984177543185 11638145618372238133157389)
            ·
              refine ⟨4364304606889589299934021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11638145618372238133157389 4364304606889589299934021)
              ·
                refine ⟨818307113791797993737629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4364304606889589299934021 818307113791797993737629)
                ·
                  refine ⟨306865167671924247651611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 818307113791797993737629 306865167671924247651611)
                  ·
                    rfl

theorem cell20_672320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 3, 4, 3].length) (baseStart_672320 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_672320 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_672320 prefixEnd_672320 := by exact prefixLift 672320
  have htrace : WordTrace (prefixWord ++ tailWord_672320) baseStart_672320 baseEnd_672320 := by
    simpa [prefixWord, tailWord_672320, baseEnd_672320] using wordTrace_append hprefix tailTrace_672320
  have hstable : (prefixWord ++ tailWord_672320).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_672320).length < 2 ^ (prefixWord ++ tailWord_672320).sum := by decide
  have hdescent : baseEnd_672320 < baseStart_672320 := by decide
  rcases family_descends (prefixWord ++ tailWord_672320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_672416 : List Nat := [2, 1, 1, 4, 4, 2, 1, 3, 2]
def baseStart_672416 : Nat := 118140960795 + 672416 * 2 ^ 59
def prefixEnd_672416 : Nat := 4983230072969 + 3 ^ 40 * 672416 * 2
def baseEnd_672416 : Nat := 306908984687774580451219

theorem tailTrace_672416 : CollatzResearch.WordTrace tailWord_672416 prefixEnd_672416 306908984687774580451219 := by
  unfold tailWord_672416
  simp only [CollatzResearch.WordTrace]
  refine ⟨12262513165979573177534551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16350017554639430903379401 12262513165979573177534551)
  ·
    refine ⟨18393769748969359766301827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12262513165979573177534551 18393769748969359766301827)
    ·
      refine ⟨27590654623454039649452741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18393769748969359766301827 27590654623454039649452741)
      ·
        refine ⟨5173247741897632434272389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 27590654623454039649452741 5173247741897632434272389)
        ·
          refine ⟨969983951605806081426073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5173247741897632434272389 969983951605806081426073)
          ·
            refine ⟨727487963704354561069555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 969983951605806081426073 727487963704354561069555)
            ·
              refine ⟨1091231945556531841604333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 727487963704354561069555 1091231945556531841604333)
              ·
                refine ⟨409211979583699440601625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1091231945556531841604333 409211979583699440601625)
                ·
                  refine ⟨306908984687774580451219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 409211979583699440601625 306908984687774580451219)
                  ·
                    rfl

theorem cell20_672416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 2, 1, 3, 2].length) (baseStart_672416 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_672416 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_672416 prefixEnd_672416 := by exact prefixLift 672416
  have htrace : WordTrace (prefixWord ++ tailWord_672416) baseStart_672416 baseEnd_672416 := by
    simpa [prefixWord, tailWord_672416, baseEnd_672416] using wordTrace_append hprefix tailTrace_672416
  have hstable : (prefixWord ++ tailWord_672416).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_672416).length < 2 ^ (prefixWord ++ tailWord_672416).sum := by decide
  have hdescent : baseEnd_672416 < baseStart_672416 := by decide
  rcases family_descends (prefixWord ++ tailWord_672416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_672423 : List Nat := [1, 1, 6, 3, 2, 1, 6]
def baseStart_672423 : Nat := 118140960795 + 672423 * 2 ^ 59
def prefixEnd_672423 : Nat := 4983230072969 + 3 ^ 40 * 672423 * 2
def baseEnd_672423 : Nat := 34101353297612629690873

theorem tailTrace_672423 : CollatzResearch.WordTrace tailWord_672423 prefixEnd_672423 34101353297612629690873 := by
  unfold tailWord_672423
  simp only [CollatzResearch.WordTrace]
  refine ⟨24525281642933786550573923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16350187761955857700382615 24525281642933786550573923)
  ·
    refine ⟨36787922464400679825860885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24525281642933786550573923 36787922464400679825860885)
    ·
      refine ⟨1724433865518781866837229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 36787922464400679825860885 1724433865518781866837229)
      ·
        refine ⟨646662699569543200063961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1724433865518781866837229 646662699569543200063961)
        ·
          refine ⟨484997024677157400047971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 646662699569543200063961 484997024677157400047971)
          ·
            refine ⟨727495537015736100071957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 484997024677157400047971 727495537015736100071957)
            ·
              refine ⟨34101353297612629690873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 727495537015736100071957 34101353297612629690873)
              ·
                rfl

theorem cell20_672423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 2, 1, 6].length) (baseStart_672423 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_672423 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_672423 prefixEnd_672423 := by exact prefixLift 672423
  have htrace : WordTrace (prefixWord ++ tailWord_672423) baseStart_672423 baseEnd_672423 := by
    simpa [prefixWord, tailWord_672423, baseEnd_672423] using wordTrace_append hprefix tailTrace_672423
  have hstable : (prefixWord ++ tailWord_672423).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_672423).length < 2 ^ (prefixWord ++ tailWord_672423).sum := by decide
  have hdescent : baseEnd_672423 < baseStart_672423 := by decide
  rcases family_descends (prefixWord ++ tailWord_672423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_672433 : List Nat := [1, 2, 2, 6, 1, 1, 3, 2, 2]
def baseStart_672433 : Nat := 118140960795 + 672433 * 2 ^ 59
def prefixEnd_672433 : Nat := 4983230072969 + 3 ^ 40 * 672433 * 2
def baseEnd_672433 : Nat := 306916743950998076884483

theorem tailTrace_672433 : CollatzResearch.WordTrace tailWord_672433 prefixEnd_672433 306916743950998076884483 := by
  unfold tailWord_672433
  simp only [CollatzResearch.WordTrace]
  refine ⟨24525646372897558258437953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16350430915265038838958635 24525646372897558258437953)
  ·
    refine ⟨18394234779673168693828465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24525646372897558258437953 18394234779673168693828465)
    ·
      refine ⟨13795676084754876520371349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18394234779673168693828465 13795676084754876520371349)
      ·
        refine ⟨646672316472884836892407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 13795676084754876520371349 646672316472884836892407)
        ·
          refine ⟨970008474709327255338611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 646672316472884836892407 970008474709327255338611)
          ·
            refine ⟨1455012712063990883007917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 970008474709327255338611 1455012712063990883007917)
            ·
              refine ⟨545629767023996581127969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1455012712063990883007917 545629767023996581127969)
              ·
                refine ⟨409222325267997435845977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 545629767023996581127969 409222325267997435845977)
                ·
                  refine ⟨306916743950998076884483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 409222325267997435845977 306916743950998076884483)
                  ·
                    rfl

theorem cell20_672433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 1, 3, 2, 2].length) (baseStart_672433 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_672433 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_672433 prefixEnd_672433 := by exact prefixLift 672433
  have htrace : WordTrace (prefixWord ++ tailWord_672433) baseStart_672433 baseEnd_672433 := by
    simpa [prefixWord, tailWord_672433, baseEnd_672433] using wordTrace_append hprefix tailTrace_672433
  have hstable : (prefixWord ++ tailWord_672433).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_672433).length < 2 ^ (prefixWord ++ tailWord_672433).sum := by decide
  have hdescent : baseEnd_672433 < baseStart_672433 := by decide
  rcases family_descends (prefixWord ++ tailWord_672433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_672434 : List Nat := [3, 2, 1, 1, 1, 2, 1, 6, 3]
def baseStart_672434 : Nat := 118140960795 + 672434 * 2 ^ 59
def prefixEnd_672434 : Nat := 4983230072969 + 3 ^ 40 * 672434 * 2
def baseEnd_672434 : Nat := 306917200378246517851145

theorem tailTrace_672434 : CollatzResearch.WordTrace tailWord_672434 prefixEnd_672434 306917200378246517851145 := by
  unfold tailWord_672434
  simp only [CollatzResearch.WordTrace]
  refine ⟨6131420711473483857306089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16350455230595956952816237 6131420711473483857306089)
  ·
    refine ⟨4598565533605112892979567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6131420711473483857306089 4598565533605112892979567)
    ·
      refine ⟨6897848300407669339469351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4598565533605112892979567 6897848300407669339469351)
      ·
        refine ⟨10346772450611504009204027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6897848300407669339469351 10346772450611504009204027)
        ·
          refine ⟨15520158675917256013806041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10346772450611504009204027 15520158675917256013806041)
          ·
            refine ⟨11640119006937942010354531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15520158675917256013806041 11640119006937942010354531)
            ·
              refine ⟨17460178510406913015531797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11640119006937942010354531 17460178510406913015531797)
              ·
                refine ⟨818445867675324047603053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 17460178510406913015531797 818445867675324047603053)
                ·
                  refine ⟨306917200378246517851145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 818445867675324047603053 306917200378246517851145)
                  ·
                    rfl

theorem cell20_672434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 6, 3].length) (baseStart_672434 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_672434 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_672434 prefixEnd_672434 := by exact prefixLift 672434
  have htrace : WordTrace (prefixWord ++ tailWord_672434) baseStart_672434 baseEnd_672434 := by
    simpa [prefixWord, tailWord_672434, baseEnd_672434] using wordTrace_append hprefix tailTrace_672434
  have hstable : (prefixWord ++ tailWord_672434).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_672434).length < 2 ^ (prefixWord ++ tailWord_672434).sum := by decide
  have hdescent : baseEnd_672434 < baseStart_672434 := by decide
  rcases family_descends (prefixWord ++ tailWord_672434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_672437 : List Nat := [1, 3, 3, 3, 1, 3, 1, 1, 4]
def baseStart_672437 : Nat := 118140960795 + 672437 * 2 ^ 59
def prefixEnd_672437 : Nat := 4983230072969 + 3 ^ 40 * 672437 * 2
def baseEnd_672437 : Nat := 306918569659991840751133

theorem tailTrace_672437 : CollatzResearch.WordTrace tailWord_672437 prefixEnd_672437 306918569659991840751133 := by
  unfold tailWord_672437
  simp only [CollatzResearch.WordTrace]
  refine ⟨24525792264883066941583565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16350528176588711294389043 24525792264883066941583565)
  ·
    refine ⟨9197172099331150103093837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24525792264883066941583565 9197172099331150103093837)
    ·
      refine ⟨3448939537249181288660189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9197172099331150103093837 3448939537249181288660189)
      ·
        refine ⟨1293352326468442983247571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3448939537249181288660189 1293352326468442983247571)
        ·
          refine ⟨1940028489702664474871357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1293352326468442983247571 1940028489702664474871357)
          ·
            refine ⟨727510683638499178076759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1940028489702664474871357 727510683638499178076759)
            ·
              refine ⟨1091266025457748767115139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 727510683638499178076759 1091266025457748767115139)
              ·
                refine ⟨1636899038186623150672709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1091266025457748767115139 1636899038186623150672709)
                ·
                  refine ⟨306918569659991840751133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1636899038186623150672709 306918569659991840751133)
                  ·
                    rfl

theorem cell20_672437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 3, 1, 1, 4].length) (baseStart_672437 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_672437 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_672437 prefixEnd_672437 := by exact prefixLift 672437
  have htrace : WordTrace (prefixWord ++ tailWord_672437) baseStart_672437 baseEnd_672437 := by
    simpa [prefixWord, tailWord_672437, baseEnd_672437] using wordTrace_append hprefix tailTrace_672437
  have hstable : (prefixWord ++ tailWord_672437).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_672437).length < 2 ^ (prefixWord ++ tailWord_672437).sum := by decide
  have hdescent : baseEnd_672437 < baseStart_672437 := by decide
  rcases family_descends (prefixWord ++ tailWord_672437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_672448 : List Nat := [2, 1, 1, 2, 4, 2, 1, 7]
def baseStart_672448 : Nat := 118140960795 + 672448 * 2 ^ 59
def prefixEnd_672448 : Nat := 4983230072969 + 3 ^ 40 * 672448 * 2
def baseEnd_672448 : Nat := 102307863453241563794807

theorem tailTrace_672448 : CollatzResearch.WordTrace tailWord_672448 prefixEnd_672448 102307863453241563794807 := by
  unfold tailWord_672448
  simp only [CollatzResearch.WordTrace]
  refine ⟨12263096733921607910116999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16350795645228810546822665 12263096733921607910116999)
  ·
    refine ⟨18394645100882411865175499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12263096733921607910116999 18394645100882411865175499)
    ·
      refine ⟨27591967651323617797763249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18394645100882411865175499 27591967651323617797763249)
      ·
        refine ⟨20693975738492713348322437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27591967651323617797763249 20693975738492713348322437)
        ·
          refine ⟨3880120450967383752810457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20693975738492713348322437 3880120450967383752810457)
          ·
            refine ⟨2910090338225537814607843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3880120450967383752810457 2910090338225537814607843)
            ·
              refine ⟨4365135507338306721911765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2910090338225537814607843 4365135507338306721911765)
              ·
                refine ⟨102307863453241563794807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4365135507338306721911765 102307863453241563794807)
                ·
                  rfl

theorem cell20_672448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 1, 7].length) (baseStart_672448 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_672448 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_672448 prefixEnd_672448 := by exact prefixLift 672448
  have htrace : WordTrace (prefixWord ++ tailWord_672448) baseStart_672448 baseEnd_672448 := by
    simpa [prefixWord, tailWord_672448, baseEnd_672448] using wordTrace_append hprefix tailTrace_672448
  have hstable : (prefixWord ++ tailWord_672448).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_672448).length < 2 ^ (prefixWord ++ tailWord_672448).sum := by decide
  have hdescent : baseEnd_672448 < baseStart_672448 := by decide
  rcases family_descends (prefixWord ++ tailWord_672448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_672455 : List Nat := [1, 1, 4, 1, 1, 1, 2, 2, 7]
def baseStart_672455 : Nat := 118140960795 + 672455 * 2 ^ 59
def prefixEnd_672455 : Nat := 4983230072969 + 3 ^ 40 * 672455 * 2
def baseEnd_672455 : Nat := 306926785350463778151059

theorem tailTrace_672455 : CollatzResearch.WordTrace tailWord_672455 prefixEnd_672455 306926785350463778151059 := by
  unfold tailWord_672455
  simp only [CollatzResearch.WordTrace]
  refine ⟨24526448778817856015738819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16350965852545237343825879 24526448778817856015738819)
  ·
    refine ⟨36789673168226784023608229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24526448778817856015738819 36789673168226784023608229)
    ·
      refine ⟨6898063719042522004426543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 36789673168226784023608229 6898063719042522004426543)
      ·
        refine ⟨10347095578563783006639815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6898063719042522004426543 10347095578563783006639815)
        ·
          refine ⟨15520643367845674509959723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10347095578563783006639815 15520643367845674509959723)
          ·
            refine ⟨23280965051768511764939585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15520643367845674509959723 23280965051768511764939585)
            ·
              refine ⟨17460723788826383823704689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23280965051768511764939585 17460723788826383823704689)
              ·
                refine ⟨13095542841619787867778517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17460723788826383823704689 13095542841619787867778517)
                ·
                  refine ⟨306926785350463778151059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13095542841619787867778517 306926785350463778151059)
                  ·
                    rfl

theorem cell20_672455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 2, 7].length) (baseStart_672455 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_672455 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_672455 prefixEnd_672455 := by exact prefixLift 672455
  have htrace : WordTrace (prefixWord ++ tailWord_672455) baseStart_672455 baseEnd_672455 := by
    simpa [prefixWord, tailWord_672455, baseEnd_672455] using wordTrace_append hprefix tailTrace_672455
  have hstable : (prefixWord ++ tailWord_672455).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_672455).length < 2 ^ (prefixWord ++ tailWord_672455).sum := by decide
  have hdescent : baseEnd_672455 < baseStart_672455 := by decide
  rcases family_descends (prefixWord ++ tailWord_672455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_672496 : List Nat := [2, 1, 1, 1, 3, 1, 5, 4, 2]
def baseStart_672496 : Nat := 118140960795 + 672496 * 2 ^ 59
def prefixEnd_672496 : Nat := 4983230072969 + 3 ^ 40 * 672496 * 2
def baseEnd_672496 : Nat := 306945498867649857784225

theorem tailTrace_672496 : CollatzResearch.WordTrace tailWord_672496 prefixEnd_672496 306945498867649857784225 := by
  unfold tailWord_672496
  simp only [CollatzResearch.WordTrace]
  refine ⟨12263972085834660008990671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16351962781112880011987561 12263972085834660008990671)
  ·
    refine ⟨18395958128751990013486007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12263972085834660008990671 18395958128751990013486007)
    ·
      refine ⟨27593937193127985020229011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18395958128751990013486007 27593937193127985020229011)
      ·
        refine ⟨41390905789691977530343517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27593937193127985020229011 41390905789691977530343517)
        ·
          refine ⟨15521589671134491573878819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41390905789691977530343517 15521589671134491573878819)
          ·
            refine ⟨23282384506701737360818229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15521589671134491573878819 23282384506701737360818229)
            ·
              refine ⟨2182723547503287877576709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 23282384506701737360818229 2182723547503287877576709)
              ·
                refine ⟨409260665156866477045633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2182723547503287877576709 409260665156866477045633)
                ·
                  refine ⟨306945498867649857784225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 409260665156866477045633 306945498867649857784225)
                  ·
                    rfl

theorem cell20_672496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 5, 4, 2].length) (baseStart_672496 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_672496 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_672496 prefixEnd_672496 := by exact prefixLift 672496
  have htrace : WordTrace (prefixWord ++ tailWord_672496) baseStart_672496 baseEnd_672496 := by
    simpa [prefixWord, tailWord_672496, baseEnd_672496] using wordTrace_append hprefix tailTrace_672496
  have hstable : (prefixWord ++ tailWord_672496).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_672496).length < 2 ^ (prefixWord ++ tailWord_672496).sum := by decide
  have hdescent : baseEnd_672496 < baseStart_672496 := by decide
  rcases family_descends (prefixWord ++ tailWord_672496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_672531 : List Nat := [1, 1, 1, 2, 1, 3, 4, 2, 5]
def baseStart_672531 : Nat := 118140960795 + 672531 * 2 ^ 59
def prefixEnd_672531 : Nat := 4983230072969 + 3 ^ 40 * 672531 * 2
def baseEnd_672531 : Nat := 306961473821345291617415

theorem tailTrace_672531 : CollatzResearch.WordTrace tailWord_672531 prefixEnd_672531 306961473821345291617415 := by
  unfold tailWord_672531
  simp only [CollatzResearch.WordTrace]
  refine ⟨24529220726542520995505447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16352813817695013997003631 24529220726542520995505447)
  ·
    refine ⟨36793831089813781493258171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24529220726542520995505447 36793831089813781493258171)
    ·
      refine ⟨55190746634720672239887257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36793831089813781493258171 55190746634720672239887257)
      ·
        refine ⟨41393059976040504179915443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55190746634720672239887257 41393059976040504179915443)
        ·
          refine ⟨62089589964060756269873165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41393059976040504179915443 62089589964060756269873165)
          ·
            refine ⟨23283596236522783601202437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 62089589964060756269873165 23283596236522783601202437)
            ·
              refine ⟨4365674294348021925225457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23283596236522783601202437 4365674294348021925225457)
              ·
                refine ⟨3274255720761016443919093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4365674294348021925225457 3274255720761016443919093)
                ·
                  refine ⟨306961473821345291617415, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3274255720761016443919093 306961473821345291617415)
                  ·
                    rfl

theorem cell20_672531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 4, 2, 5].length) (baseStart_672531 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_672531 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_672531 prefixEnd_672531 := by exact prefixLift 672531
  have htrace : WordTrace (prefixWord ++ tailWord_672531) baseStart_672531 baseEnd_672531 := by
    simpa [prefixWord, tailWord_672531, baseEnd_672531] using wordTrace_append hprefix tailTrace_672531
  have hstable : (prefixWord ++ tailWord_672531).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_672531).length < 2 ^ (prefixWord ++ tailWord_672531).sum := by decide
  have hdescent : baseEnd_672531 < baseStart_672531 := by decide
  rcases family_descends (prefixWord ++ tailWord_672531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_672562 : List Nat := [3, 2, 1, 1, 3, 1, 2, 7]
def baseStart_672562 : Nat := 118140960795 + 672562 * 2 ^ 59
def prefixEnd_672562 : Nat := 4983230072969 + 3 ^ 40 * 672562 * 2
def baseEnd_672562 : Nat := 102325207688682320527985

theorem tailTrace_672562 : CollatzResearch.WordTrace tailWord_672562 prefixEnd_672562 102325207688682320527985 := by
  unfold tailWord_672562
  simp only [CollatzResearch.WordTrace]
  refine ⟨6132587847357553322470985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16353567592953475526589293 6132587847357553322470985)
  ·
    refine ⟨4599440885518164991853239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6132587847357553322470985 4599440885518164991853239)
    ·
      refine ⟨6899161328277247487779859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4599440885518164991853239 6899161328277247487779859)
      ·
        refine ⟨10348741992415871231669789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6899161328277247487779859 10348741992415871231669789)
        ·
          refine ⟨3880778247155951711876171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10348741992415871231669789 3880778247155951711876171)
          ·
            refine ⟨5821167370733927567814257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3880778247155951711876171 5821167370733927567814257)
            ·
              refine ⟨4365875528050445675860693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5821167370733927567814257 4365875528050445675860693)
              ·
                refine ⟨102325207688682320527985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4365875528050445675860693 102325207688682320527985)
                ·
                  rfl

theorem cell20_672562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 2, 7].length) (baseStart_672562 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_672562 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_672562 prefixEnd_672562 := by exact prefixLift 672562
  have htrace : WordTrace (prefixWord ++ tailWord_672562) baseStart_672562 baseEnd_672562 := by
    simpa [prefixWord, tailWord_672562, baseEnd_672562] using wordTrace_append hprefix tailTrace_672562
  have hstable : (prefixWord ++ tailWord_672562).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_672562).length < 2 ^ (prefixWord ++ tailWord_672562).sum := by decide
  have hdescent : baseEnd_672562 < baseStart_672562 := by decide
  rcases family_descends (prefixWord ++ tailWord_672562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_672596 : List Nat := [2, 4, 1, 1, 5, 1, 6]
def baseStart_672596 : Nat := 118140960795 + 672596 * 2 ^ 59
def prefixEnd_672596 : Nat := 4983230072969 + 3 ^ 40 * 672596 * 2
def baseEnd_672596 : Nat := 34110126843610439383387

theorem tailTrace_672596 : CollatzResearch.WordTrace tailWord_672596 prefixEnd_672596 34110126843610439383387 := by
  unfold tailWord_672596
  simp only [CollatzResearch.WordTrace]
  refine ⟨12265795735653518548310821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16354394314204691397747761 12265795735653518548310821)
  ·
    refine ⟨2299836700435034727808279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12265795735653518548310821 2299836700435034727808279)
    ·
      refine ⟨3449755050652552091712419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2299836700435034727808279 3449755050652552091712419)
      ·
        refine ⟨5174632575978828137568629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3449755050652552091712419 5174632575978828137568629)
        ·
          refine ⟨485121803998015137897059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 5174632575978828137568629 485121803998015137897059)
          ·
            refine ⟨727682705997022706845589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 485121803998015137897059 727682705997022706845589)
            ·
              refine ⟨34110126843610439383387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 727682705997022706845589 34110126843610439383387)
              ·
                rfl

theorem cell20_672596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 5, 1, 6].length) (baseStart_672596 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_672596 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_672596 prefixEnd_672596 := by exact prefixLift 672596
  have htrace : WordTrace (prefixWord ++ tailWord_672596) baseStart_672596 baseEnd_672596 := by
    simpa [prefixWord, tailWord_672596, baseEnd_672596] using wordTrace_append hprefix tailTrace_672596
  have hstable : (prefixWord ++ tailWord_672596).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_672596).length < 2 ^ (prefixWord ++ tailWord_672596).sum := by decide
  have hdescent : baseEnd_672596 < baseStart_672596 := by decide
  rcases family_descends (prefixWord ++ tailWord_672596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_672607 : List Nat := [1, 1, 2, 3, 1, 3, 1, 3, 5]
def baseStart_672607 : Nat := 118140960795 + 672607 * 2 ^ 59
def prefixEnd_672607 : Nat := 4983230072969 + 3 ^ 40 * 672607 * 2
def baseEnd_672607 : Nat := 306996162292226805083771

theorem tailTrace_672607 : CollatzResearch.WordTrace tailWord_672607 prefixEnd_672607 306996162292226805083771 := by
  unfold tailWord_672607
  simp only [CollatzResearch.WordTrace]
  refine ⟨24531992674267185975272075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16354661782844790650181383 24531992674267185975272075)
  ·
    refine ⟨36797989011400778962908113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24531992674267185975272075 36797989011400778962908113)
    ·
      refine ⟨27598491758550584222181085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36797989011400778962908113 27598491758550584222181085)
      ·
        refine ⟨10349434409456469083317907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27598491758550584222181085 10349434409456469083317907)
        ·
          refine ⟨15524151614184703624976861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10349434409456469083317907 15524151614184703624976861)
          ·
            refine ⟨5821556855319263859366323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15524151614184703624976861 5821556855319263859366323)
            ·
              refine ⟨8732335282978895789049485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5821556855319263859366323 8732335282978895789049485)
              ·
                refine ⟨3274625731117085920893557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8732335282978895789049485 3274625731117085920893557)
                ·
                  refine ⟨306996162292226805083771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3274625731117085920893557 306996162292226805083771)
                  ·
                    rfl

theorem cell20_672607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 1, 3, 5].length) (baseStart_672607 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_672607 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_672607 prefixEnd_672607 := by exact prefixLift 672607
  have htrace : WordTrace (prefixWord ++ tailWord_672607) baseStart_672607 baseEnd_672607 := by
    simpa [prefixWord, tailWord_672607, baseEnd_672607] using wordTrace_append hprefix tailTrace_672607
  have hstable : (prefixWord ++ tailWord_672607).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_672607).length < 2 ^ (prefixWord ++ tailWord_672607).sum := by decide
  have hdescent : baseEnd_672607 < baseStart_672607 := by decide
  rcases family_descends (prefixWord ++ tailWord_672607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_672658 : List Nat := [3, 2, 3, 2, 2, 1, 2, 2, 3]
def baseStart_672658 : Nat := 118140960795 + 672658 * 2 ^ 59
def prefixEnd_672658 : Nat := 4983230072969 + 3 ^ 40 * 672658 * 2
def baseEnd_672658 : Nat := 307019440081897294383563

theorem tailTrace_672658 : CollatzResearch.WordTrace tailWord_672658 prefixEnd_672658 307019440081897294383563 := by
  unfold tailWord_672658
  simp only [CollatzResearch.WordTrace]
  refine ⟨6133463199270605421344657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16355901864721614456919085 6133463199270605421344657)
  ·
    refine ⟨4600097399452954066008493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6133463199270605421344657 4600097399452954066008493)
    ·
      refine ⟨1725036524794857774753185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4600097399452954066008493 1725036524794857774753185)
      ·
        refine ⟨1293777393596143331064889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1725036524794857774753185 1293777393596143331064889)
        ·
          refine ⟨970333045197107498298667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1293777393596143331064889 970333045197107498298667)
          ·
            refine ⟨1455499567795661247448001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 970333045197107498298667 1455499567795661247448001)
            ·
              refine ⟨1091624675846745935586001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1455499567795661247448001 1091624675846745935586001)
              ·
                refine ⟨818718506885059451689501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1091624675846745935586001 818718506885059451689501)
                ·
                  refine ⟨307019440081897294383563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 818718506885059451689501 307019440081897294383563)
                  ·
                    rfl

theorem cell20_672658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 1, 2, 2, 3].length) (baseStart_672658 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_672658 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_672658 prefixEnd_672658 := by exact prefixLift 672658
  have htrace : WordTrace (prefixWord ++ tailWord_672658) baseStart_672658 baseEnd_672658 := by
    simpa [prefixWord, tailWord_672658, baseEnd_672658] using wordTrace_append hprefix tailTrace_672658
  have hstable : (prefixWord ++ tailWord_672658).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_672658).length < 2 ^ (prefixWord ++ tailWord_672658).sum := by decide
  have hdescent : baseEnd_672658 < baseStart_672658 := by decide
  rcases family_descends (prefixWord ++ tailWord_672658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_672669 : List Nat := [1, 4, 2, 1, 2, 1, 2, 3, 4]
def baseStart_672669 : Nat := 118140960795 + 672669 * 2 ^ 59
def prefixEnd_672669 : Nat := 4983230072969 + 3 ^ 40 * 672669 * 2
def baseEnd_672669 : Nat := 307024460781630145016851

theorem tailTrace_672669 : CollatzResearch.WordTrace tailWord_672669 prefixEnd_672669 307024460781630145016851 := by
  unfold tailWord_672669
  simp only [CollatzResearch.WordTrace]
  refine ⟨24534254000042570564029061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16356169333361713709352707 24534254000042570564029061)
  ·
    refine ⟨4600172625007981980755449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24534254000042570564029061 4600172625007981980755449)
    ·
      refine ⟨3450129468755986485566587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4600172625007981980755449 3450129468755986485566587)
      ·
        refine ⟨5175194203133979728349881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3450129468755986485566587 5175194203133979728349881)
        ·
          refine ⟨3881395652350484796262411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5175194203133979728349881 3881395652350484796262411)
          ·
            refine ⟨5822093478525727194393617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3881395652350484796262411 5822093478525727194393617)
            ·
              refine ⟨4366570108894295395795213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5822093478525727194393617 4366570108894295395795213)
              ·
                refine ⟨1637463790835360773423205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4366570108894295395795213 1637463790835360773423205)
                ·
                  refine ⟨307024460781630145016851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1637463790835360773423205 307024460781630145016851)
                  ·
                    rfl

theorem cell20_672669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 2, 3, 4].length) (baseStart_672669 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_672669 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_672669 prefixEnd_672669 := by exact prefixLift 672669
  have htrace : WordTrace (prefixWord ++ tailWord_672669) baseStart_672669 baseEnd_672669 := by
    simpa [prefixWord, tailWord_672669, baseEnd_672669] using wordTrace_append hprefix tailTrace_672669
  have hstable : (prefixWord ++ tailWord_672669).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_672669).length < 2 ^ (prefixWord ++ tailWord_672669).sum := by decide
  have hdescent : baseEnd_672669 < baseStart_672669 := by decide
  rcases family_descends (prefixWord ++ tailWord_672669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_672693 : List Nat := [1, 3, 3, 2, 1, 1, 5, 4]
def baseStart_672693 : Nat := 118140960795 + 672693 * 2 ^ 59
def prefixEnd_672693 : Nat := 4983230072969 + 3 ^ 40 * 672693 * 2
def baseEnd_672693 : Nat := 102345138345197576072251

theorem tailTrace_672693 : CollatzResearch.WordTrace tailWord_672693 prefixEnd_672693 102345138345197576072251 := by
  unfold tailWord_672693
  simp only [CollatzResearch.WordTrace]
  refine ⟨24535129351955622662902733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16356752901303748441935155 24535129351955622662902733)
  ·
    refine ⟨9200673506983358498588525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24535129351955622662902733 9200673506983358498588525)
    ·
      refine ⟨3450252565118759436970697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9200673506983358498588525 3450252565118759436970697)
      ·
        refine ⟨2587689423839069577728023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3450252565118759436970697 2587689423839069577728023)
        ·
          refine ⟨3881534135758604366592035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2587689423839069577728023 3881534135758604366592035)
          ·
            refine ⟨5822301203637906549888053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3881534135758604366592035 5822301203637906549888053)
            ·
              refine ⟨545840737841053739052005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5822301203637906549888053 545840737841053739052005)
              ·
                refine ⟨102345138345197576072251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 545840737841053739052005 102345138345197576072251)
                ·
                  rfl

theorem cell20_672693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 5, 4].length) (baseStart_672693 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_672693 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_672693 prefixEnd_672693 := by exact prefixLift 672693
  have htrace : WordTrace (prefixWord ++ tailWord_672693) baseStart_672693 baseEnd_672693 := by
    simpa [prefixWord, tailWord_672693, baseEnd_672693] using wordTrace_append hprefix tailTrace_672693
  have hstable : (prefixWord ++ tailWord_672693).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_672693).length < 2 ^ (prefixWord ++ tailWord_672693).sum := by decide
  have hdescent : baseEnd_672693 < baseStart_672693 := by decide
  rcases family_descends (prefixWord ++ tailWord_672693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_672721 : List Nat := [1, 2, 2, 1, 2, 1, 5, 1, 5]
def baseStart_672721 : Nat := 118140960795 + 672721 * 2 ^ 59
def prefixEnd_672721 : Nat := 4983230072969 + 3 ^ 40 * 672721 * 2
def baseEnd_672721 : Nat := 307048194998549075283305

theorem tailTrace_672721 : CollatzResearch.WordTrace tailWord_672721 prefixEnd_672721 307048194998549075283305 := by
  unfold tailWord_672721
  simp only [CollatzResearch.WordTrace]
  refine ⟨24536150595854183444922017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16357433730569455629948011 24536150595854183444922017)
  ·
    refine ⟨18402112946890637583691513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24536150595854183444922017 18402112946890637583691513)
    ·
      refine ⟨13801584710167978187768635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18402112946890637583691513 13801584710167978187768635)
      ·
        refine ⟨20702377065251967281652953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13801584710167978187768635 20702377065251967281652953)
        ·
          refine ⟨15526782798938975461239715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20702377065251967281652953 15526782798938975461239715)
          ·
            refine ⟨23290174198408463191859573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15526782798938975461239715 23290174198408463191859573)
            ·
              refine ⟨2183453831100793424236835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 23290174198408463191859573 2183453831100793424236835)
              ·
                refine ⟨3275180746651190136355253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2183453831100793424236835 3275180746651190136355253)
                ·
                  refine ⟨307048194998549075283305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3275180746651190136355253 307048194998549075283305)
                  ·
                    rfl

theorem cell20_672721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 5, 1, 5].length) (baseStart_672721 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_672721 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_672721 prefixEnd_672721 := by exact prefixLift 672721
  have htrace : WordTrace (prefixWord ++ tailWord_672721) baseStart_672721 baseEnd_672721 := by
    simpa [prefixWord, tailWord_672721, baseEnd_672721] using wordTrace_append hprefix tailTrace_672721
  have hstable : (prefixWord ++ tailWord_672721).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_672721).length < 2 ^ (prefixWord ++ tailWord_672721).sum := by decide
  have hdescent : baseEnd_672721 < baseStart_672721 := by decide
  rcases family_descends (prefixWord ++ tailWord_672721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_672724 : List Nat := [2, 4, 1, 2, 1, 3, 2, 1, 4]
def baseStart_672724 : Nat := 118140960795 + 672724 * 2 ^ 59
def prefixEnd_672724 : Nat := 4983230072969 + 3 ^ 40 * 672724 * 2
def baseEnd_672724 : Nat := 307049564280294398183293

theorem tailTrace_672724 : CollatzResearch.WordTrace tailWord_672724 prefixEnd_672724 307049564280294398183293 := by
  unfold tailWord_672724
  simp only [CollatzResearch.WordTrace]
  refine ⟨12268130007421657478640613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16357506676562209971520817 12268130007421657478640613)
  ·
    refine ⟨2300274376391560777245115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12268130007421657478640613 2300274376391560777245115)
    ·
      refine ⟨3450411564587341165867673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2300274376391560777245115 3450411564587341165867673)
      ·
        refine ⟨2587808673440505874400755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3450411564587341165867673 2587808673440505874400755)
        ·
          refine ⟨3881713010160758811601133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2587808673440505874400755 3881713010160758811601133)
          ·
            refine ⟨1455642378810284554350425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3881713010160758811601133 1455642378810284554350425)
            ·
              refine ⟨1091731784107713415762819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1455642378810284554350425 1091731784107713415762819)
              ·
                refine ⟨1637597676161570123644229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1091731784107713415762819 1637597676161570123644229)
                ·
                  refine ⟨307049564280294398183293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1637597676161570123644229 307049564280294398183293)
                  ·
                    rfl

theorem cell20_672724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 3, 2, 1, 4].length) (baseStart_672724 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_672724 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_672724 prefixEnd_672724 := by exact prefixLift 672724
  have htrace : WordTrace (prefixWord ++ tailWord_672724) baseStart_672724 baseEnd_672724 := by
    simpa [prefixWord, tailWord_672724, baseEnd_672724] using wordTrace_append hprefix tailTrace_672724
  have hstable : (prefixWord ++ tailWord_672724).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_672724).length < 2 ^ (prefixWord ++ tailWord_672724).sum := by decide
  have hdescent : baseEnd_672724 < baseStart_672724 := by decide
  rcases family_descends (prefixWord ++ tailWord_672724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_672758 : List Nat := [5, 1, 1, 1, 3, 3, 1, 3, 2]
def baseStart_672758 : Nat := 118140960795 + 672758 * 2 ^ 59
def prefixEnd_672758 : Nat := 4983230072969 + 3 ^ 40 * 672758 * 2
def baseEnd_672758 : Nat := 307065082806741391049821

theorem tailTrace_672758 : CollatzResearch.WordTrace tailWord_672758 prefixEnd_672758 307065082806741391049821 := by
  unfold tailWord_672758
  simp only [CollatzResearch.WordTrace]
  refine ⟨1533593756045008672751183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 16358333397813425842679285 1533593756045008672751183)
  ·
    refine ⟨2300390634067513009126775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1533593756045008672751183 2300390634067513009126775)
    ·
      refine ⟨3450585951101269513690163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2300390634067513009126775 3450585951101269513690163)
      ·
        refine ⟨5175878926651904270535245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3450585951101269513690163 5175878926651904270535245)
        ·
          refine ⟨1940954597494464101450717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5175878926651904270535245 1940954597494464101450717)
          ·
            refine ⟨727857974060424038044019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1940954597494464101450717 727857974060424038044019)
            ·
              refine ⟨1091786961090636057066029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 727857974060424038044019 1091786961090636057066029)
              ·
                refine ⟨409420110408988521399761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1091786961090636057066029 409420110408988521399761)
                ·
                  refine ⟨307065082806741391049821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 409420110408988521399761 307065082806741391049821)
                  ·
                    rfl

theorem cell20_672758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 3, 1, 3, 2].length) (baseStart_672758 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_672758 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_672758 prefixEnd_672758 := by exact prefixLift 672758
  have htrace : WordTrace (prefixWord ++ tailWord_672758) baseStart_672758 baseEnd_672758 := by
    simpa [prefixWord, tailWord_672758, baseEnd_672758] using wordTrace_append hprefix tailTrace_672758
  have hstable : (prefixWord ++ tailWord_672758).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_672758).length < 2 ^ (prefixWord ++ tailWord_672758).sum := by decide
  have hdescent : baseEnd_672758 < baseStart_672758 := by decide
  rcases family_descends (prefixWord ++ tailWord_672758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_672779 : List Nat := [1, 1, 1, 1, 6, 3, 3, 2, 2]
def baseStart_672779 : Nat := 118140960795 + 672779 * 2 ^ 59
def prefixEnd_672779 : Nat := 4983230072969 + 3 ^ 40 * 672779 * 2
def baseEnd_672779 : Nat := 307074667778958651349735

theorem tailTrace_672779 : CollatzResearch.WordTrace tailWord_672779 prefixEnd_672779 307074667778958651349735 := by
  unfold tailWord_672779
  simp only [CollatzResearch.WordTrace]
  refine ⟨24538266029644059350533391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16358844019762706233688927 24538266029644059350533391)
  ·
    refine ⟨36807399044466089025800087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24538266029644059350533391 36807399044466089025800087)
    ·
      refine ⟨55211098566699133538700131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36807399044466089025800087 55211098566699133538700131)
      ·
        refine ⟨82816647850048700308050197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55211098566699133538700131 82816647850048700308050197)
        ·
          refine ⟨3882030367971032826939853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 82816647850048700308050197 3882030367971032826939853)
          ·
            refine ⟨1455761387989137310102445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3882030367971032826939853 1455761387989137310102445)
            ·
              refine ⟨545910520495926491288417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1455761387989137310102445 545910520495926491288417)
              ·
                refine ⟨409432890371944868466313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 545910520495926491288417 409432890371944868466313)
                ·
                  refine ⟨307074667778958651349735, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 409432890371944868466313 307074667778958651349735)
                  ·
                    rfl

theorem cell20_672779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 3, 3, 2, 2].length) (baseStart_672779 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_672779 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_672779 prefixEnd_672779 := by exact prefixLift 672779
  have htrace : WordTrace (prefixWord ++ tailWord_672779) baseStart_672779 baseEnd_672779 := by
    simpa [prefixWord, tailWord_672779, baseEnd_672779] using wordTrace_append hprefix tailTrace_672779
  have hstable : (prefixWord ++ tailWord_672779).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_672779).length < 2 ^ (prefixWord ++ tailWord_672779).sum := by decide
  have hdescent : baseEnd_672779 < baseStart_672779 := by decide
  rcases family_descends (prefixWord ++ tailWord_672779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_672807 : List Nat := [1, 1, 7, 1, 1, 1, 2, 6]
def baseStart_672807 : Nat := 118140960795 + 672807 * 2 ^ 59
def prefixEnd_672807 : Nat := 4983230072969 + 3 ^ 40 * 672807 * 2
def baseEnd_672807 : Nat := 102362482580638332805429

theorem tailTrace_672807 : CollatzResearch.WordTrace tailWord_672807 prefixEnd_672807 102362482580638332805429 := by
  unfold tailWord_672807
  simp only [CollatzResearch.WordTrace]
  refine ⟨24539287273542620132552675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16359524849028413421701783 24539287273542620132552675)
  ·
    refine ⟨36808930910313930198829013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24539287273542620132552675 36808930910313930198829013)
    ·
      refine ⟨862709318210482739035055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 36808930910313930198829013 862709318210482739035055)
      ·
        refine ⟨1294063977315724108552583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 862709318210482739035055 1294063977315724108552583)
        ·
          refine ⟨1941095965973586162828875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1294063977315724108552583 1941095965973586162828875)
          ·
            refine ⟨2911643948960379244243313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1941095965973586162828875 2911643948960379244243313)
            ·
              refine ⟨2183732961720284433182485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2911643948960379244243313 2183732961720284433182485)
              ·
                refine ⟨102362482580638332805429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2183732961720284433182485 102362482580638332805429)
                ·
                  rfl

theorem cell20_672807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 2, 6].length) (baseStart_672807 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_672807 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_672807 prefixEnd_672807 := by exact prefixLift 672807
  have htrace : WordTrace (prefixWord ++ tailWord_672807) baseStart_672807 baseEnd_672807 := by
    simpa [prefixWord, tailWord_672807, baseEnd_672807] using wordTrace_append hprefix tailTrace_672807
  have hstable : (prefixWord ++ tailWord_672807).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_672807).length < 2 ^ (prefixWord ++ tailWord_672807).sum := by decide
  have hdescent : baseEnd_672807 < baseStart_672807 := by decide
  rcases family_descends (prefixWord ++ tailWord_672807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_672811 : List Nat := [1, 1, 1, 1, 2, 1, 5, 8]
def baseStart_672811 : Nat := 118140960795 + 672811 * 2 ^ 59
def prefixEnd_672811 : Nat := 4983230072969 + 3 ^ 40 * 672811 * 2
def baseEnd_672811 : Nat := 102363091150302920760979

theorem tailTrace_672811 : CollatzResearch.WordTrace tailWord_672811 prefixEnd_672811 102363091150302920760979 := by
  unfold tailWord_672811
  simp only [CollatzResearch.WordTrace]
  refine ⟨24539433165528128815698287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16359622110352085877132191 24539433165528128815698287)
  ·
    refine ⟨36809149748292193223547431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24539433165528128815698287 36809149748292193223547431)
    ·
      refine ⟨55213724622438289835321147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36809149748292193223547431 55213724622438289835321147)
      ·
        refine ⟨82820586933657434752981721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55213724622438289835321147 82820586933657434752981721)
        ·
          refine ⟨62115440200243076064736291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 82820586933657434752981721 62115440200243076064736291)
          ·
            refine ⟨93173160300364614097104437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62115440200243076064736291 93173160300364614097104437)
            ·
              refine ⟨8734983778159182571603541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 93173160300364614097104437 8734983778159182571603541)
              ·
                refine ⟨102363091150302920760979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8734983778159182571603541 102363091150302920760979)
                ·
                  rfl

theorem cell20_672811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 5, 8].length) (baseStart_672811 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_672811 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_672811 prefixEnd_672811 := by exact prefixLift 672811
  have htrace : WordTrace (prefixWord ++ tailWord_672811) baseStart_672811 baseEnd_672811 := by
    simpa [prefixWord, tailWord_672811, baseEnd_672811] using wordTrace_append hprefix tailTrace_672811
  have hstable : (prefixWord ++ tailWord_672811).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_672811).length < 2 ^ (prefixWord ++ tailWord_672811).sum := by decide
  have hdescent : baseEnd_672811 < baseStart_672811 := by decide
  rcases family_descends (prefixWord ++ tailWord_672811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_672845 : List Nat := [1, 6, 1, 1, 1, 2, 3, 5]
def baseStart_672845 : Nat := 118140960795 + 672845 * 2 ^ 59
def prefixEnd_672845 : Nat := 4983230072969 + 3 ^ 40 * 672845 * 2
def baseEnd_672845 : Nat := 102368263992451918383155

theorem tailTrace_672845 : CollatzResearch.WordTrace tailWord_672845 prefixEnd_672845 102368263992451918383155 := by
  unfold tailWord_672845
  simp only [CollatzResearch.WordTrace]
  refine ⟨24540673247404952622435989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16360448831603301748290659 24540673247404952622435989)
  ·
    refine ⟨1150344058472107154176687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 24540673247404952622435989 1150344058472107154176687)
    ·
      refine ⟨1725516087708160731265031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1150344058472107154176687 1725516087708160731265031)
      ·
        refine ⟨2588274131562241096897547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1725516087708160731265031 2588274131562241096897547)
        ·
          refine ⟨3882411197343361645346321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2588274131562241096897547 3882411197343361645346321)
          ·
            refine ⟨2911808398007521234009741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3882411197343361645346321 2911808398007521234009741)
            ·
              refine ⟨1091928149252820462753653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2911808398007521234009741 1091928149252820462753653)
              ·
                refine ⟨102368263992451918383155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1091928149252820462753653 102368263992451918383155)
                ·
                  rfl

theorem cell20_672845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 3, 5].length) (baseStart_672845 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_672845 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_672845 prefixEnd_672845 := by exact prefixLift 672845
  have htrace : WordTrace (prefixWord ++ tailWord_672845) baseStart_672845 baseEnd_672845 := by
    simpa [prefixWord, tailWord_672845, baseEnd_672845] using wordTrace_append hprefix tailTrace_672845
  have hstable : (prefixWord ++ tailWord_672845).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_672845).length < 2 ^ (prefixWord ++ tailWord_672845).sum := by decide
  have hdescent : baseEnd_672845 < baseStart_672845 := by decide
  rcases family_descends (prefixWord ++ tailWord_672845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_672852 : List Nat := [2, 4, 1, 1, 1, 1, 4, 3, 3]
def baseStart_672852 : Nat := 118140960795 + 672852 * 2 ^ 59
def prefixEnd_672852 : Nat := 4983230072969 + 3 ^ 40 * 672852 * 2
def baseEnd_672852 : Nat := 307107986968094841916103

theorem tailTrace_672852 : CollatzResearch.WordTrace tailWord_672852 prefixEnd_672852 307107986968094841916103 := by
  unfold tailWord_672852
  simp only [CollatzResearch.WordTrace]
  refine ⟨12270464279189796408970405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16360619038919728545293873 12270464279189796408970405)
  ·
    refine ⟨2300712052348086826681951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12270464279189796408970405 2300712052348086826681951)
    ·
      refine ⟨3451068078522130240022927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2300712052348086826681951 3451068078522130240022927)
      ·
        refine ⟨5176602117783195360034391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3451068078522130240022927 5176602117783195360034391)
        ·
          refine ⟨7764903176674793040051587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5176602117783195360034391 7764903176674793040051587)
          ·
            refine ⟨11647354765012189560077381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7764903176674793040051587 11647354765012189560077381)
            ·
              refine ⟨2183879018439785542514509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11647354765012189560077381 2183879018439785542514509)
              ·
                refine ⟨818954631914919578442941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2183879018439785542514509 818954631914919578442941)
                ·
                  refine ⟨307107986968094841916103, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 818954631914919578442941 307107986968094841916103)
                  ·
                    rfl

theorem cell20_672852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 4, 3, 3].length) (baseStart_672852 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_672852 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_672852 prefixEnd_672852 := by exact prefixLift 672852
  have htrace : WordTrace (prefixWord ++ tailWord_672852) baseStart_672852 baseEnd_672852 := by
    simpa [prefixWord, tailWord_672852, baseEnd_672852] using wordTrace_append hprefix tailTrace_672852
  have hstable : (prefixWord ++ tailWord_672852).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_672852).length < 2 ^ (prefixWord ++ tailWord_672852).sum := by decide
  have hdescent : baseEnd_672852 < baseStart_672852 := by decide
  rcases family_descends (prefixWord ++ tailWord_672852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_672872 : List Nat := [2, 1, 4, 4, 1, 1, 2, 3, 2]
def baseStart_672872 : Nat := 118140960795 + 672872 * 2 ^ 59
def prefixEnd_672872 : Nat := 4983230072969 + 3 ^ 40 * 672872 * 2
def baseEnd_672872 : Nat := 307117115513063661249355

theorem tailTrace_672872 : CollatzResearch.WordTrace tailWord_672872 prefixEnd_672872 307117115513063661249355 := by
  unfold tailWord_672872
  simp only [CollatzResearch.WordTrace]
  refine ⟨12270829009153568116834435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16361105345538090822445913 12270829009153568116834435)
  ·
    refine ⟨18406243513730352175251653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12270829009153568116834435 18406243513730352175251653)
    ·
      refine ⟨3451170658824441032859685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18406243513730352175251653 3451170658824441032859685)
      ·
        refine ⟨647094498529582693661191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3451170658824441032859685 647094498529582693661191)
        ·
          refine ⟨970641747794374040491787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 647094498529582693661191 970641747794374040491787)
          ·
            refine ⟨1455962621691561060737681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 970641747794374040491787 1455962621691561060737681)
            ·
              refine ⟨1091971966268670795553261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1455962621691561060737681 1091971966268670795553261)
              ·
                refine ⟨409489487350751548332473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1091971966268670795553261 409489487350751548332473)
                ·
                  refine ⟨307117115513063661249355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 409489487350751548332473 307117115513063661249355)
                  ·
                    rfl

theorem cell20_672872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 1, 2, 3, 2].length) (baseStart_672872 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_672872 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_672872 prefixEnd_672872 := by exact prefixLift 672872
  have htrace : WordTrace (prefixWord ++ tailWord_672872) baseStart_672872 baseEnd_672872 := by
    simpa [prefixWord, tailWord_672872, baseEnd_672872] using wordTrace_append hprefix tailTrace_672872
  have hstable : (prefixWord ++ tailWord_672872).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_672872).length < 2 ^ (prefixWord ++ tailWord_672872).sum := by decide
  have hdescent : baseEnd_672872 < baseStart_672872 := by decide
  rcases family_descends (prefixWord ++ tailWord_672872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_672876 : List Nat := [2, 2, 1, 1, 3, 2, 4, 3, 2]
def baseStart_672876 : Nat := 118140960795 + 672876 * 2 ^ 59
def prefixEnd_672876 : Nat := 4983230072969 + 3 ^ 40 * 672876 * 2
def baseEnd_672876 : Nat := 307118941222057425116005

theorem tailTrace_672876 : CollatzResearch.WordTrace tailWord_672876 prefixEnd_672876 307118941222057425116005 := by
  unfold tailWord_672876
  simp only [CollatzResearch.WordTrace]
  refine ⟨12270901955146322458407241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16361202606861763277876321 12270901955146322458407241)
  ·
    refine ⟨9203176466359741843805431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12270901955146322458407241 9203176466359741843805431)
    ·
      refine ⟨13804764699539612765708147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9203176466359741843805431 13804764699539612765708147)
      ·
        refine ⟨20707147049309419148562221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13804764699539612765708147 20707147049309419148562221)
        ·
          refine ⟨7765180143491032180710833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20707147049309419148562221 7765180143491032180710833)
          ·
            refine ⟨5823885107618274135533125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7765180143491032180710833 5823885107618274135533125)
            ·
              refine ⟨1091978457678426400412461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5823885107618274135533125 1091978457678426400412461)
              ·
                refine ⟨409491921629409900154673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1091978457678426400412461 409491921629409900154673)
                ·
                  refine ⟨307118941222057425116005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 409491921629409900154673 307118941222057425116005)
                  ·
                    rfl

theorem cell20_672876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 4, 3, 2].length) (baseStart_672876 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_672876 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_672876 prefixEnd_672876 := by exact prefixLift 672876
  have htrace : WordTrace (prefixWord ++ tailWord_672876) baseStart_672876 baseEnd_672876 := by
    simpa [prefixWord, tailWord_672876, baseEnd_672876] using wordTrace_append hprefix tailTrace_672876
  have hstable : (prefixWord ++ tailWord_672876).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_672876).length < 2 ^ (prefixWord ++ tailWord_672876).sum := by decide
  have hdescent : baseEnd_672876 < baseStart_672876 := by decide
  rcases family_descends (prefixWord ++ tailWord_672876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_672880 : List Nat := [2, 1, 1, 1, 5, 1, 1, 2, 6]
def baseStart_672880 : Nat := 118140960795 + 672880 * 2 ^ 59
def prefixEnd_672880 : Nat := 4983230072969 + 3 ^ 40 * 672880 * 2
def baseEnd_672880 : Nat := 307120766931051188982655

theorem tailTrace_672880 : CollatzResearch.WordTrace tailWord_672880 prefixEnd_672880 307120766931051188982655 := by
  unfold tailWord_672880
  simp only [CollatzResearch.WordTrace]
  refine ⟨12270974901139076799980047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16361299868185435733306729 12270974901139076799980047)
  ·
    refine ⟨18406462351708615199970071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12270974901139076799980047 18406462351708615199970071)
    ·
      refine ⟨27609693527562922799955107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18406462351708615199970071 27609693527562922799955107)
      ·
        refine ⟨41414540291344384199932661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27609693527562922799955107 41414540291344384199932661)
        ·
          refine ⟨3882613152313536018743687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 41414540291344384199932661 3882613152313536018743687)
          ·
            refine ⟨5823919728470304028115531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3882613152313536018743687 5823919728470304028115531)
            ·
              refine ⟨8735879592705456042173297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5823919728470304028115531 8735879592705456042173297)
              ·
                refine ⟨6551909694529092031629973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8735879592705456042173297 6551909694529092031629973)
                ·
                  refine ⟨307120766931051188982655, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6551909694529092031629973 307120766931051188982655)
                  ·
                    rfl

theorem cell20_672880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 1, 2, 6].length) (baseStart_672880 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_672880 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_672880 prefixEnd_672880 := by exact prefixLift 672880
  have htrace : WordTrace (prefixWord ++ tailWord_672880) baseStart_672880 baseEnd_672880 := by
    simpa [prefixWord, tailWord_672880, baseEnd_672880] using wordTrace_append hprefix tailTrace_672880
  have hstable : (prefixWord ++ tailWord_672880).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_672880).length < 2 ^ (prefixWord ++ tailWord_672880).sum := by decide
  have hdescent : baseEnd_672880 < baseStart_672880 := by decide
  rcases family_descends (prefixWord ++ tailWord_672880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_672887 : List Nat := [1, 1, 3, 1, 1, 4, 9]
def baseStart_672887 : Nat := 118140960795 + 672887 * 2 ^ 59
def prefixEnd_672887 : Nat := 4983230072969 + 3 ^ 40 * 672887 * 2
def baseEnd_672887 : Nat := 34124884657976697305477

theorem tailTrace_672887 : CollatzResearch.WordTrace tailWord_672887 prefixEnd_672887 34124884657976697305477 := by
  unfold tailWord_672887
  simp only [CollatzResearch.WordTrace]
  refine ⟨24542205113252793795464915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16361470075501862530309943 24542205113252793795464915)
  ·
    refine ⟨36813307669879190693197373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24542205113252793795464915 36813307669879190693197373)
    ·
      refine ⟨13804990376204696509949015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36813307669879190693197373 13804990376204696509949015)
      ·
        refine ⟨20707485564307044764923523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13804990376204696509949015 20707485564307044764923523)
        ·
          refine ⟨31061228346460567147385285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20707485564307044764923523 31061228346460567147385285)
          ·
            refine ⟨5823980314961356340134741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 31061228346460567147385285 5823980314961356340134741)
            ·
              refine ⟨34124884657976697305477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 5823980314961356340134741 34124884657976697305477)
              ·
                rfl

theorem cell20_672887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 9].length) (baseStart_672887 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_672887 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_672887 prefixEnd_672887 := by exact prefixLift 672887
  have htrace : WordTrace (prefixWord ++ tailWord_672887) baseStart_672887 baseEnd_672887 := by
    simpa [prefixWord, tailWord_672887, baseEnd_672887] using wordTrace_append hprefix tailTrace_672887
  have hstable : (prefixWord ++ tailWord_672887).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_672887).length < 2 ^ (prefixWord ++ tailWord_672887).sum := by decide
  have hdescent : baseEnd_672887 < baseStart_672887 := by decide
  rcases family_descends (prefixWord ++ tailWord_672887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_672897 : List Nat := [1, 2, 4, 2, 2, 1, 1, 3, 4]
def baseStart_672897 : Nat := 118140960795 + 672897 * 2 ^ 59
def prefixEnd_672897 : Nat := 4983230072969 + 3 ^ 40 * 672897 * 2
def baseEnd_672897 : Nat := 307128526194274685415919

theorem tailTrace_672897 : CollatzResearch.WordTrace tailWord_672897 prefixEnd_672897 307128526194274685415919 := by
  unfold tailWord_672897
  simp only [CollatzResearch.WordTrace]
  refine ⟨24542569843216565503328945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16361713228811043668885963 24542569843216565503328945)
  ·
    refine ⟨18406927382412424127496709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24542569843216565503328945 18406927382412424127496709)
    ·
      refine ⟨3451298884202329523905633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18406927382412424127496709 3451298884202329523905633)
      ·
        refine ⟨2588474163151747142929225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3451298884202329523905633 2588474163151747142929225)
        ·
          refine ⟨1941355622363810357196919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2588474163151747142929225 1941355622363810357196919)
          ·
            refine ⟨2912033433545715535795379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1941355622363810357196919 2912033433545715535795379)
            ·
              refine ⟨4368050150318573303693069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2912033433545715535795379 4368050150318573303693069)
              ·
                refine ⟨1638018806369464988884901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4368050150318573303693069 1638018806369464988884901)
                ·
                  refine ⟨307128526194274685415919, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1638018806369464988884901 307128526194274685415919)
                  ·
                    rfl

theorem cell20_672897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 1, 3, 4].length) (baseStart_672897 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_672897 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_672897 prefixEnd_672897 := by exact prefixLift 672897
  have htrace : WordTrace (prefixWord ++ tailWord_672897) baseStart_672897 baseEnd_672897 := by
    simpa [prefixWord, tailWord_672897, baseEnd_672897] using wordTrace_append hprefix tailTrace_672897
  have hstable : (prefixWord ++ tailWord_672897).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_672897).length < 2 ^ (prefixWord ++ tailWord_672897).sum := by decide
  have hdescent : baseEnd_672897 < baseStart_672897 := by decide
  rcases family_descends (prefixWord ++ tailWord_672897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_673004 : List Nat := [2, 2, 1, 1, 2, 5, 2, 2, 3]
def baseStart_673004 : Nat := 118140960795 + 673004 * 2 ^ 59
def prefixEnd_673004 : Nat := 4983230072969 + 3 ^ 40 * 673004 * 2
def baseEnd_673004 : Nat := 307177363909857868848815

theorem tailTrace_673004 : CollatzResearch.WordTrace tailWord_673004 prefixEnd_673004 307177363909857868848815 := by
  unfold tailWord_673004
  simp only [CollatzResearch.WordTrace]
  refine ⟨12273236226914461388737033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16364314969219281851649377 12273236226914461388737033)
  ·
    refine ⟨9204927170185846041552775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12273236226914461388737033 9204927170185846041552775)
    ·
      refine ⟨13807390755278769062329163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9204927170185846041552775 13807390755278769062329163)
      ·
        refine ⟨20711086132918153593493745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13807390755278769062329163 20711086132918153593493745)
        ·
          refine ⟨15533314599688615195120309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20711086132918153593493745 15533314599688615195120309)
          ·
            refine ⟨1456248243720807674542529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 15533314599688615195120309 1456248243720807674542529)
            ·
              refine ⟨1092186182790605755906897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1456248243720807674542529 1092186182790605755906897)
              ·
                refine ⟨819139637092954316930173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1092186182790605755906897 819139637092954316930173)
                ·
                  refine ⟨307177363909857868848815, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 819139637092954316930173 307177363909857868848815)
                  ·
                    rfl

theorem cell20_673004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 3].length) (baseStart_673004 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_673004 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_673004 prefixEnd_673004 := by exact prefixLift 673004
  have htrace : WordTrace (prefixWord ++ tailWord_673004) baseStart_673004 baseEnd_673004 := by
    simpa [prefixWord, tailWord_673004, baseEnd_673004] using wordTrace_append hprefix tailTrace_673004
  have hstable : (prefixWord ++ tailWord_673004).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_673004).length < 2 ^ (prefixWord ++ tailWord_673004).sum := by decide
  have hdescent : baseEnd_673004 < baseStart_673004 := by decide
  rcases family_descends (prefixWord ++ tailWord_673004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_673056 : List Nat := [2, 1, 1, 5, 3, 1, 7]
def baseStart_673056 : Nat := 118140960795 + 673056 * 2 ^ 59
def prefixEnd_673056 : Nat := 4983230072969 + 3 ^ 40 * 673056 * 2
def baseEnd_673056 : Nat := 34133455347419644346141

theorem tailTrace_673056 : CollatzResearch.WordTrace tailWord_673056 prefixEnd_673056 34133455347419644346141 := by
  unfold tailWord_673056
  simp only [CollatzResearch.WordTrace]
  refine ⟨12274184524820267829183511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16365579366427023772244681 12274184524820267829183511)
  ·
    refine ⟨18411276787230401743775267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12274184524820267829183511 18411276787230401743775267)
    ·
      refine ⟨27616915180845602615662901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18411276787230401743775267 27616915180845602615662901)
      ·
        refine ⟨2589085798204275245218397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 27616915180845602615662901 2589085798204275245218397)
        ·
          refine ⟨970907174326603216956899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2589085798204275245218397 970907174326603216956899)
          ·
            refine ⟨1456360761489904825435349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 970907174326603216956899 1456360761489904825435349)
            ·
              refine ⟨34133455347419644346141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1456360761489904825435349 34133455347419644346141)
              ·
                rfl

theorem cell20_673056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 1, 7].length) (baseStart_673056 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_673056 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_673056 prefixEnd_673056 := by exact prefixLift 673056
  have htrace : WordTrace (prefixWord ++ tailWord_673056) baseStart_673056 baseEnd_673056 := by
    simpa [prefixWord, tailWord_673056, baseEnd_673056] using wordTrace_append hprefix tailTrace_673056
  have hstable : (prefixWord ++ tailWord_673056).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_673056).length < 2 ^ (prefixWord ++ tailWord_673056).sum := by decide
  have hdescent : baseEnd_673056 < baseStart_673056 := by decide
  rcases family_descends (prefixWord ++ tailWord_673056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_673066 : List Nat := [3, 1, 4, 2, 1, 2, 2, 1, 4]
def baseStart_673066 : Nat := 118140960795 + 673066 * 2 ^ 59
def prefixEnd_673066 : Nat := 4983230072969 + 3 ^ 40 * 673066 * 2
def baseEnd_673066 : Nat := 307205662399261208781895

theorem tailTrace_673066 : CollatzResearch.WordTrace tailWord_673066 prefixEnd_673066 307205662399261208781895 := by
  unfold tailWord_673066
  simp only [CollatzResearch.WordTrace]
  refine ⟨6137183444901076841557763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16365822519736204910820701 6137183444901076841557763)
  ·
    refine ⟨9205775167351615262336645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6137183444901076841557763 9205775167351615262336645)
    ·
      refine ⟨1726082843878427861688121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9205775167351615262336645 1726082843878427861688121)
      ·
        refine ⟨1294562132908820896266091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1726082843878427861688121 1294562132908820896266091)
        ·
          refine ⟨1941843199363231344399137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1294562132908820896266091 1941843199363231344399137)
          ·
            refine ⟨1456382399522423508299353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1941843199363231344399137 1456382399522423508299353)
            ·
              refine ⟨1092286799641817631224515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1456382399522423508299353 1092286799641817631224515)
              ·
                refine ⟨1638430199462726446836773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1092286799641817631224515 1638430199462726446836773)
                ·
                  refine ⟨307205662399261208781895, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1638430199462726446836773 307205662399261208781895)
                  ·
                    rfl

theorem cell20_673066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 2, 2, 1, 4].length) (baseStart_673066 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_673066 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_673066 prefixEnd_673066 := by exact prefixLift 673066
  have htrace : WordTrace (prefixWord ++ tailWord_673066) baseStart_673066 baseEnd_673066 := by
    simpa [prefixWord, tailWord_673066, baseEnd_673066] using wordTrace_append hprefix tailTrace_673066
  have hstable : (prefixWord ++ tailWord_673066).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_673066).length < 2 ^ (prefixWord ++ tailWord_673066).sum := by decide
  have hdescent : baseEnd_673066 < baseStart_673066 := by decide
  rcases family_descends (prefixWord ++ tailWord_673066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_673117 : List Nat := [1, 4, 5, 1, 2, 1, 1, 1, 4]
def baseStart_673117 : Nat := 118140960795 + 673117 * 2 ^ 59
def prefixEnd_673117 : Nat := 4983230072969 + 3 ^ 40 * 673117 * 2
def baseEnd_673117 : Nat := 307228940188931698081687

theorem tailTrace_673117 : CollatzResearch.WordTrace tailWord_673117 prefixEnd_673117 307228940188931698081687 := by
  unfold tailWord_673117
  simp only [CollatzResearch.WordTrace]
  refine ⟨24550593902419543076337605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16367062601613028717558403 24550593902419543076337605)
  ·
    refine ⟨4603236356703664326813301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24550593902419543076337605 4603236356703664326813301)
    ·
      refine ⟨431553408440968530638747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 4603236356703664326813301 431553408440968530638747)
      ·
        refine ⟨647330112661452795958121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 431553408440968530638747 647330112661452795958121)
        ·
          refine ⟨485497584496089596968591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 647330112661452795958121 485497584496089596968591)
          ·
            refine ⟨728246376744134395452887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 485497584496089596968591 728246376744134395452887)
            ·
              refine ⟨1092369565116201593179331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 728246376744134395452887 1092369565116201593179331)
              ·
                refine ⟨1638554347674302389768997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1092369565116201593179331 1638554347674302389768997)
                ·
                  refine ⟨307228940188931698081687, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1638554347674302389768997 307228940188931698081687)
                  ·
                    rfl

theorem cell20_673117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 2, 1, 1, 1, 4].length) (baseStart_673117 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_673117 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_673117 prefixEnd_673117 := by exact prefixLift 673117
  have htrace : WordTrace (prefixWord ++ tailWord_673117) baseStart_673117 baseEnd_673117 := by
    simpa [prefixWord, tailWord_673117, baseEnd_673117] using wordTrace_append hprefix tailTrace_673117
  have hstable : (prefixWord ++ tailWord_673117).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_673117).length < 2 ^ (prefixWord ++ tailWord_673117).sum := by decide
  have hdescent : baseEnd_673117 < baseStart_673117 := by decide
  rcases family_descends (prefixWord ++ tailWord_673117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_673132 : List Nat := [2, 2, 1, 1, 5, 2, 2, 5]
def baseStart_673132 : Nat := 118140960795 + 673132 * 2 ^ 59
def prefixEnd_673132 : Nat := 4983230072969 + 3 ^ 40 * 673132 * 2
def baseEnd_673132 : Nat := 102411928865886104193875

theorem tailTrace_673132 : CollatzResearch.WordTrace tailWord_673132 prefixEnd_673132 102411928865886104193875 := by
  unfold tailWord_673132
  simp only [CollatzResearch.WordTrace]
  refine ⟨12275570498682600319066825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16367427331576800425422433 12275570498682600319066825)
  ·
    refine ⟨9206677874011950239300119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12275570498682600319066825 9206677874011950239300119)
    ·
      refine ⟨13810016811017925358950179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9206677874011950239300119 13810016811017925358950179)
      ·
        refine ⟨20715025216526888038425269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13810016811017925358950179 20715025216526888038425269)
        ·
          refine ⟨1942033614049395753602369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 20715025216526888038425269 1942033614049395753602369)
          ·
            refine ⟨1456525210537046815201777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1942033614049395753602369 1456525210537046815201777)
            ·
              refine ⟨1092393907902785111401333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1456525210537046815201777 1092393907902785111401333)
              ·
                refine ⟨102411928865886104193875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1092393907902785111401333 102411928865886104193875)
                ·
                  rfl

theorem cell20_673132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 2, 2, 5].length) (baseStart_673132 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_673132 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_673132 prefixEnd_673132 := by exact prefixLift 673132
  have htrace : WordTrace (prefixWord ++ tailWord_673132) baseStart_673132 baseEnd_673132 := by
    simpa [prefixWord, tailWord_673132, baseEnd_673132] using wordTrace_append hprefix tailTrace_673132
  have hstable : (prefixWord ++ tailWord_673132).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_673132).length < 2 ^ (prefixWord ++ tailWord_673132).sum := by decide
  have hdescent : baseEnd_673132 < baseStart_673132 := by decide
  rcases family_descends (prefixWord ++ tailWord_673132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_673163 : List Nat := [1, 1, 1, 1, 4, 3, 2, 5, 2]
def baseStart_673163 : Nat := 118140960795 + 673163 * 2 ^ 59
def prefixEnd_673163 : Nat := 4983230072969 + 3 ^ 40 * 673163 * 2
def baseEnd_673163 : Nat := 307249935842359982548165

theorem tailTrace_673163 : CollatzResearch.WordTrace tailWord_673163 prefixEnd_673163 307249935842359982548165 := by
  unfold tailWord_673163
  simp only [CollatzResearch.WordTrace]
  refine ⟨24552271660252892932512143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16368181106835261955008095 24552271660252892932512143)
  ·
    refine ⟨36828407490379339398768215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24552271660252892932512143 36828407490379339398768215)
    ·
      refine ⟨55242611235569009098152323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36828407490379339398768215 55242611235569009098152323)
      ·
        refine ⟨82863916853353513647228485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55242611235569009098152323 82863916853353513647228485)
        ·
          refine ⟨15536984410003783808855341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 82863916853353513647228485 15536984410003783808855341)
          ·
            refine ⟨5826369153751418928320753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15536984410003783808855341 5826369153751418928320753)
            ·
              refine ⟨4369776865313564196240565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5826369153751418928320753 4369776865313564196240565)
              ·
                refine ⟨409666581123146643397553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4369776865313564196240565 409666581123146643397553)
                ·
                  refine ⟨307249935842359982548165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 409666581123146643397553 307249935842359982548165)
                  ·
                    rfl

theorem cell20_673163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 2, 5, 2].length) (baseStart_673163 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_673163 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_673163 prefixEnd_673163 := by exact prefixLift 673163
  have htrace : WordTrace (prefixWord ++ tailWord_673163) baseStart_673163 baseEnd_673163 := by
    simpa [prefixWord, tailWord_673163, baseEnd_673163] using wordTrace_append hprefix tailTrace_673163
  have hstable : (prefixWord ++ tailWord_673163).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_673163).length < 2 ^ (prefixWord ++ tailWord_673163).sum := by decide
  have hdescent : baseEnd_673163 < baseStart_673163 := by decide
  rcases family_descends (prefixWord ++ tailWord_673163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_673170 : List Nat := [3, 2, 3, 3, 9]
def baseStart_673170 : Nat := 118140960795 + 673170 * 2 ^ 59
def prefixEnd_673170 : Nat := 4983230072969 + 3 ^ 40 * 673170 * 2
def baseEnd_673170 : Nat := 3793248528803692213763

theorem tailTrace_673170 : CollatzResearch.WordTrace tailWord_673170 prefixEnd_673170 3793248528803692213763 := by
  unfold tailWord_673170
  simp only [CollatzResearch.WordTrace]
  refine ⟨6138131742806883282004241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16368351314151688752011309 6138131742806883282004241)
  ·
    refine ⟨4603598807105162461503181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6138131742806883282004241 4603598807105162461503181)
    ·
      refine ⟨1726349552664435923063693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4603598807105162461503181 1726349552664435923063693)
      ·
        refine ⟨647381082249163471148885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1726349552664435923063693 647381082249163471148885)
        ·
          refine ⟨3793248528803692213763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 9 647381082249163471148885 3793248528803692213763)
          ·
            rfl

theorem cell20_673170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 9].length) (baseStart_673170 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_673170 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_673170 prefixEnd_673170 := by exact prefixLift 673170
  have htrace : WordTrace (prefixWord ++ tailWord_673170) baseStart_673170 baseEnd_673170 := by
    simpa [prefixWord, tailWord_673170, baseEnd_673170] using wordTrace_append hprefix tailTrace_673170
  have hstable : (prefixWord ++ tailWord_673170).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_673170).length < 2 ^ (prefixWord ++ tailWord_673170).sum := by decide
  have hdescent : baseEnd_673170 < baseStart_673170 := by decide
  rcases family_descends (prefixWord ++ tailWord_673170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_673176 : List Nat := [2, 1, 2, 5, 2, 2, 2, 2, 2]
def baseStart_673176 : Nat := 118140960795 + 673176 * 2 ^ 59
def prefixEnd_673176 : Nat := 4983230072969 + 3 ^ 40 * 673176 * 2
def baseEnd_673176 : Nat := 307255869396589715114779

theorem tailTrace_673176 : CollatzResearch.WordTrace tailWord_673176 prefixEnd_673176 307255869396589715114779 := by
  unfold tailWord_673176
  simp only [CollatzResearch.WordTrace]
  refine ⟨12276372904602898076367691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16368497206137197435156921 12276372904602898076367691)
  ·
    refine ⟨18414559356904347114551537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12276372904602898076367691 18414559356904347114551537)
    ·
      refine ⟨13810919517678260335913653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18414559356904347114551537 13810919517678260335913653)
      ·
        refine ⟨1294773704782336906491905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 13810919517678260335913653 1294773704782336906491905)
        ·
          refine ⟨971080278586752679868929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1294773704782336906491905 971080278586752679868929)
          ·
            refine ⟨728310208940064509901697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 971080278586752679868929 728310208940064509901697)
            ·
              refine ⟨546232656705048382426273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 728310208940064509901697 546232656705048382426273)
              ·
                refine ⟨409674492528786286819705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 546232656705048382426273 409674492528786286819705)
                ·
                  refine ⟨307255869396589715114779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 409674492528786286819705 307255869396589715114779)
                  ·
                    rfl

theorem cell20_673176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 2, 2, 2, 2].length) (baseStart_673176 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_673176 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_673176 prefixEnd_673176 := by exact prefixLift 673176
  have htrace : WordTrace (prefixWord ++ tailWord_673176) baseStart_673176 baseEnd_673176 := by
    simpa [prefixWord, tailWord_673176, baseEnd_673176] using wordTrace_append hprefix tailTrace_673176
  have hstable : (prefixWord ++ tailWord_673176).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_673176).length < 2 ^ (prefixWord ++ tailWord_673176).sum := by decide
  have hdescent : baseEnd_673176 < baseStart_673176 := by decide
  rcases family_descends (prefixWord ++ tailWord_673176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_673177 : List Nat := [1, 2, 1, 2, 1, 5, 1, 4, 3]
def baseStart_673177 : Nat := 118140960795 + 673177 * 2 ^ 59
def prefixEnd_673177 : Nat := 4983230072969 + 3 ^ 40 * 673177 * 2
def baseEnd_673177 : Nat := 307256325823838156081441

theorem tailTrace_673177 : CollatzResearch.WordTrace tailWord_673177 prefixEnd_673177 307256325823838156081441 := by
  unfold tailWord_673177
  simp only [CollatzResearch.WordTrace]
  refine ⟨24552782282202173323521785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16368521521468115549014523 24552782282202173323521785)
  ·
    refine ⟨18414586711651629992641339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24552782282202173323521785 18414586711651629992641339)
    ·
      refine ⟨27621880067477444988962009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18414586711651629992641339 27621880067477444988962009)
      ·
        refine ⟨20716410050608083741721507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27621880067477444988962009 20716410050608083741721507)
        ·
          refine ⟨31074615075912125612582261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20716410050608083741721507 31074615075912125612582261)
          ·
            refine ⟨2913245163366761776179587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 31074615075912125612582261 2913245163366761776179587)
            ·
              refine ⟨4369867745050142664269381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2913245163366761776179587 4369867745050142664269381)
              ·
                refine ⟨819350202196901749550509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4369867745050142664269381 819350202196901749550509)
                ·
                  refine ⟨307256325823838156081441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 819350202196901749550509 307256325823838156081441)
                  ·
                    rfl

theorem cell20_673177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 1, 4, 3].length) (baseStart_673177 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_673177 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_673177 prefixEnd_673177 := by exact prefixLift 673177
  have htrace : WordTrace (prefixWord ++ tailWord_673177) baseStart_673177 baseEnd_673177 := by
    simpa [prefixWord, tailWord_673177, baseEnd_673177] using wordTrace_append hprefix tailTrace_673177
  have hstable : (prefixWord ++ tailWord_673177).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_673177).length < 2 ^ (prefixWord ++ tailWord_673177).sum := by decide
  have hdescent : baseEnd_673177 < baseStart_673177 := by decide
  rcases family_descends (prefixWord ++ tailWord_673177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_673184 : List Nat := [2, 1, 1, 4, 1, 2, 2, 3, 4]
def baseStart_673184 : Nat := 118140960795 + 673184 * 2 ^ 59
def prefixEnd_673184 : Nat := 4983230072969 + 3 ^ 40 * 673184 * 2
def baseEnd_673184 : Nat := 307259520814577242848079

theorem tailTrace_673184 : CollatzResearch.WordTrace tailWord_673184 prefixEnd_673184 307259520814577242848079 := by
  unfold tailWord_673184
  simp only [CollatzResearch.WordTrace]
  refine ⟨12276518796588406759513303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16368691728784542346017737 12276518796588406759513303)
  ·
    refine ⟨18414778194882610139269955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12276518796588406759513303 18414778194882610139269955)
    ·
      refine ⟨27622167292323915208904933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18414778194882610139269955 27622167292323915208904933)
      ·
        refine ⟨5179156367310734101669675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 27622167292323915208904933 5179156367310734101669675)
        ·
          refine ⟨7768734550966101152504513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5179156367310734101669675 7768734550966101152504513)
          ·
            refine ⟨5826550913224575864378385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7768734550966101152504513 5826550913224575864378385)
            ·
              refine ⟨4369913184918431898283789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5826550913224575864378385 4369913184918431898283789)
              ·
                refine ⟨1638717444344411961856421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4369913184918431898283789 1638717444344411961856421)
                ·
                  refine ⟨307259520814577242848079, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1638717444344411961856421 307259520814577242848079)
                  ·
                    rfl

theorem cell20_673184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 2, 3, 4].length) (baseStart_673184 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_673184 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_673184 prefixEnd_673184 := by exact prefixLift 673184
  have htrace : WordTrace (prefixWord ++ tailWord_673184) baseStart_673184 baseEnd_673184 := by
    simpa [prefixWord, tailWord_673184, baseEnd_673184] using wordTrace_append hprefix tailTrace_673184
  have hstable : (prefixWord ++ tailWord_673184).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_673184).length < 2 ^ (prefixWord ++ tailWord_673184).sum := by decide
  have hdescent : baseEnd_673184 < baseStart_673184 := by decide
  rcases family_descends (prefixWord ++ tailWord_673184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_673274 : List Nat := [3, 1, 1, 1, 1, 2, 3, 1, 7]
def baseStart_673274 : Nat := 118140960795 + 673274 * 2 ^ 59
def prefixEnd_673274 : Nat := 4983230072969 + 3 ^ 40 * 673274 * 2
def baseEnd_673274 : Nat := 307300599266936929847711

theorem tailTrace_673274 : CollatzResearch.WordTrace tailWord_673274 prefixEnd_673274 307300599266936929847711 := by
  unfold tailWord_673274
  simp only [CollatzResearch.WordTrace]
  refine ⟨6139080040712689722450719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16370880108567172593201917 6139080040712689722450719)
  ·
    refine ⟨9208620061069034583676079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6139080040712689722450719 9208620061069034583676079)
    ·
      refine ⟨13812930091603551875514119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9208620061069034583676079 13812930091603551875514119)
      ·
        refine ⟨20719395137405327813271179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13812930091603551875514119 20719395137405327813271179)
        ·
          refine ⟨31079092706107991719906769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20719395137405327813271179 31079092706107991719906769)
          ·
            refine ⟨23309319529580993789930077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31079092706107991719906769 23309319529580993789930077)
            ·
              refine ⟨8740994823592872671223779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23309319529580993789930077 8740994823592872671223779)
              ·
                refine ⟨13111492235389309006835669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8740994823592872671223779 13111492235389309006835669)
                ·
                  refine ⟨307300599266936929847711, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13111492235389309006835669 307300599266936929847711)
                  ·
                    rfl

theorem cell20_673274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 3, 1, 7].length) (baseStart_673274 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_673274 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_673274 prefixEnd_673274 := by exact prefixLift 673274
  have htrace : WordTrace (prefixWord ++ tailWord_673274) baseStart_673274 baseEnd_673274 := by
    simpa [prefixWord, tailWord_673274, baseEnd_673274] using wordTrace_append hprefix tailTrace_673274
  have hstable : (prefixWord ++ tailWord_673274).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_673274).length < 2 ^ (prefixWord ++ tailWord_673274).sum := by decide
  have hdescent : baseEnd_673274 < baseStart_673274 := by decide
  rcases family_descends (prefixWord ++ tailWord_673274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_673286 : List Nat := [6, 2, 1, 1, 2, 1, 3, 2, 2]
def baseStart_673286 : Nat := 118140960795 + 673286 * 2 ^ 59
def prefixEnd_673286 : Nat := 4983230072969 + 3 ^ 40 * 673286 * 2
def baseEnd_673286 : Nat := 307306076393918221447663

theorem tailTrace_673286 : CollatzResearch.WordTrace tailWord_673286 prefixEnd_673286 307306076393918221447663 := by
  unfold tailWord_673286
  simp only [CollatzResearch.WordTrace]
  refine ⟨767398682462727654351241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 16371171892538189959493141 767398682462727654351241)
  ·
    refine ⟨575549011847045740763431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 767398682462727654351241 575549011847045740763431)
    ·
      refine ⟨863323517770568611145147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 575549011847045740763431 863323517770568611145147)
      ·
        refine ⟨1294985276655852916717721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 863323517770568611145147 1294985276655852916717721)
        ·
          refine ⟨971238957491889687538291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1294985276655852916717721 971238957491889687538291)
          ·
            refine ⟨1456858436237834531307437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 971238957491889687538291 1456858436237834531307437)
            ·
              refine ⟨546321913589187949240289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1456858436237834531307437 546321913589187949240289)
              ·
                refine ⟨409741435191890961930217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 546321913589187949240289 409741435191890961930217)
                ·
                  refine ⟨307306076393918221447663, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 409741435191890961930217 307306076393918221447663)
                  ·
                    rfl

theorem cell20_673286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 1, 3, 2, 2].length) (baseStart_673286 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_673286 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_673286 prefixEnd_673286 := by exact prefixLift 673286
  have htrace : WordTrace (prefixWord ++ tailWord_673286) baseStart_673286 baseEnd_673286 := by
    simpa [prefixWord, tailWord_673286, baseEnd_673286] using wordTrace_append hprefix tailTrace_673286
  have hstable : (prefixWord ++ tailWord_673286).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_673286).length < 2 ^ (prefixWord ++ tailWord_673286).sum := by decide
  have hdescent : baseEnd_673286 < baseStart_673286 := by decide
  rcases family_descends (prefixWord ++ tailWord_673286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_673294 : List Nat := [4, 1, 1, 2, 4, 2, 1, 1, 4]
def baseStart_673294 : Nat := 118140960795 + 673294 * 2 ^ 59
def prefixEnd_673294 : Nat := 4983230072969 + 3 ^ 40 * 673294 * 2
def baseEnd_673294 : Nat := 307309727811905749180963

theorem tailTrace_673294 : CollatzResearch.WordTrace tailWord_673294 prefixEnd_673294 307309727811905749180963 := by
  unfold tailWord_673294
  simp only [CollatzResearch.WordTrace]
  refine ⟨3069631202847287788191367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16371366415185534870353957 3069631202847287788191367)
  ·
    refine ⟨4604446804270931682287051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3069631202847287788191367 4604446804270931682287051)
    ·
      refine ⟨6906670206406397523430577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4604446804270931682287051 6906670206406397523430577)
      ·
        refine ⟨5180002654804798142572933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6906670206406397523430577 5180002654804798142572933)
        ·
          refine ⟨971250497775899651732425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5180002654804798142572933 971250497775899651732425)
          ·
            refine ⟨728437873331924738799319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 971250497775899651732425 728437873331924738799319)
            ·
              refine ⟨1092656809997887108198979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 728437873331924738799319 1092656809997887108198979)
              ·
                refine ⟨1638985214996830662298469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1092656809997887108198979 1638985214996830662298469)
                ·
                  refine ⟨307309727811905749180963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1638985214996830662298469 307309727811905749180963)
                  ·
                    rfl

theorem cell20_673294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 2, 1, 1, 4].length) (baseStart_673294 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_673294 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_673294 prefixEnd_673294 := by exact prefixLift 673294
  have htrace : WordTrace (prefixWord ++ tailWord_673294) baseStart_673294 baseEnd_673294 := by
    simpa [prefixWord, tailWord_673294, baseEnd_673294] using wordTrace_append hprefix tailTrace_673294
  have hstable : (prefixWord ++ tailWord_673294).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_673294).length < 2 ^ (prefixWord ++ tailWord_673294).sum := by decide
  have hdescent : baseEnd_673294 < baseStart_673294 := by decide
  rcases family_descends (prefixWord ++ tailWord_673294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_673304 : List Nat := [2, 1, 2, 3, 5, 1, 2, 1, 3]
def baseStart_673304 : Nat := 118140960795 + 673304 * 2 ^ 59
def prefixEnd_673304 : Nat := 4983230072969 + 3 ^ 40 * 673304 * 2
def baseEnd_673304 : Nat := 307314292084390158847589

theorem tailTrace_673304 : CollatzResearch.WordTrace tailWord_673304 prefixEnd_673304 307314292084390158847589 := by
  unfold tailWord_673304
  simp only [CollatzResearch.WordTrace]
  refine ⟨12278707176371037006697483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16371609568494716008929977 12278707176371037006697483)
  ·
    refine ⟨18418060764556555510046225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12278707176371037006697483 18418060764556555510046225)
    ·
      refine ⟨13813545573417416632534669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18418060764556555510046225 13813545573417416632534669)
      ·
        refine ⟨5180079590031531237200501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13813545573417416632534669 5180079590031531237200501)
        ·
          refine ⟨485632461565456053487547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 5180079590031531237200501 485632461565456053487547)
          ·
            refine ⟨728448692348184080231321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 485632461565456053487547 728448692348184080231321)
            ·
              refine ⟨546336519261138060173491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 728448692348184080231321 546336519261138060173491)
              ·
                refine ⟨819504778891707090260237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 546336519261138060173491 819504778891707090260237)
                ·
                  refine ⟨307314292084390158847589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 819504778891707090260237 307314292084390158847589)
                  ·
                    rfl

theorem cell20_673304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 5, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 5, 1, 2, 1, 3].length) (baseStart_673304 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_673304 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_673304 prefixEnd_673304 := by exact prefixLift 673304
  have htrace : WordTrace (prefixWord ++ tailWord_673304) baseStart_673304 baseEnd_673304 := by
    simpa [prefixWord, tailWord_673304, baseEnd_673304] using wordTrace_append hprefix tailTrace_673304
  have hstable : (prefixWord ++ tailWord_673304).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_673304).length < 2 ^ (prefixWord ++ tailWord_673304).sum := by decide
  have hdescent : baseEnd_673304 < baseStart_673304 := by decide
  rcases family_descends (prefixWord ++ tailWord_673304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_673367 : List Nat := [1, 1, 3, 2, 2, 3, 2, 3, 3]
def baseStart_673367 : Nat := 118140960795 + 673367 * 2 ^ 59
def prefixEnd_673367 : Nat := 4983230072969 + 3 ^ 40 * 673367 * 2
def baseEnd_673367 : Nat := 307343047001041939747331

theorem tailTrace_673367 : CollatzResearch.WordTrace tailWord_673367 prefixEnd_673367 307343047001041939747331 := by
  unfold tailWord_673367
  simp only [CollatzResearch.WordTrace]
  refine ⟨24559712151513835772938355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16373141434342557181958903 24559712151513835772938355)
  ·
    refine ⟨36839568227270753659407533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24559712151513835772938355 36839568227270753659407533)
    ·
      refine ⟨13814838085226532622277825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36839568227270753659407533 13814838085226532622277825)
      ·
        refine ⟨10361128563919899466708369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13814838085226532622277825 10361128563919899466708369)
        ·
          refine ⟨7770846422939924600031277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10361128563919899466708369 7770846422939924600031277)
          ·
            refine ⟨2914067408602471725011729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7770846422939924600031277 2914067408602471725011729)
            ·
              refine ⟨2185550556451853793758797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2914067408602471725011729 2185550556451853793758797)
              ·
                refine ⟨819581458669445172659549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2185550556451853793758797 819581458669445172659549)
                ·
                  refine ⟨307343047001041939747331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 819581458669445172659549 307343047001041939747331)
                  ·
                    rfl

theorem cell20_673367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 2, 3, 3].length) (baseStart_673367 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_673367 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_673367 prefixEnd_673367 := by exact prefixLift 673367
  have htrace : WordTrace (prefixWord ++ tailWord_673367) baseStart_673367 baseEnd_673367 := by
    simpa [prefixWord, tailWord_673367, baseEnd_673367] using wordTrace_append hprefix tailTrace_673367
  have hstable : (prefixWord ++ tailWord_673367).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_673367).length < 2 ^ (prefixWord ++ tailWord_673367).sum := by decide
  have hdescent : baseEnd_673367 < baseStart_673367 := by decide
  rcases family_descends (prefixWord ++ tailWord_673367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_673388 : List Nat := [2, 2, 1, 1, 3, 1, 1, 4, 5]
def baseStart_673388 : Nat := 118140960795 + 673388 * 2 ^ 59
def prefixEnd_673388 : Nat := 4983230072969 + 3 ^ 40 * 673388 * 2
def baseEnd_673388 : Nat := 307352631973259200047245

theorem tailTrace_673388 : CollatzResearch.WordTrace tailWord_673388 prefixEnd_673388 307352631973259200047245 := by
  unfold tailWord_673388
  simp only [CollatzResearch.WordTrace]
  refine ⟨12280239042218878179726409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16373652056291837572968545 12280239042218878179726409)
  ·
    refine ⟨9210179281664158634794807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12280239042218878179726409 9210179281664158634794807)
    ·
      refine ⟨13815268922496237952192211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9210179281664158634794807 13815268922496237952192211)
      ·
        refine ⟨20722903383744356928288317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13815268922496237952192211 20722903383744356928288317)
        ·
          refine ⟨7771088768904133848108119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20722903383744356928288317 7771088768904133848108119)
          ·
            refine ⟨11656633153356200772162179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7771088768904133848108119 11656633153356200772162179)
            ·
              refine ⟨17484949730034301158243269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11656633153356200772162179 17484949730034301158243269)
              ·
                refine ⟨3278428074381431467170613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17484949730034301158243269 3278428074381431467170613)
                ·
                  refine ⟨307352631973259200047245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3278428074381431467170613 307352631973259200047245)
                  ·
                    rfl

theorem cell20_673388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 5].length) (baseStart_673388 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_673388 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_673388 prefixEnd_673388 := by exact prefixLift 673388
  have htrace : WordTrace (prefixWord ++ tailWord_673388) baseStart_673388 baseEnd_673388 := by
    simpa [prefixWord, tailWord_673388, baseEnd_673388] using wordTrace_append hprefix tailTrace_673388
  have hstable : (prefixWord ++ tailWord_673388).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_673388).length < 2 ^ (prefixWord ++ tailWord_673388).sum := by decide
  have hdescent : baseEnd_673388 < baseStart_673388 := by decide
  rcases family_descends (prefixWord ++ tailWord_673388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_673398 : List Nat := [5, 1, 1, 2, 2, 2, 7]
def baseStart_673398 : Nat := 118140960795 + 673398 * 2 ^ 59
def prefixEnd_673398 : Nat := 4983230072969 + 3 ^ 40 * 673398 * 2
def baseEnd_673398 : Nat := 34150799582860401079319

theorem tailTrace_673398 : CollatzResearch.WordTrace tailWord_673398 prefixEnd_673398 34150799582860401079319 := by
  unfold tailWord_673398
  simp only [CollatzResearch.WordTrace]
  refine ⟨1535052675900095504207303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 16373895209601018711544565 1535052675900095504207303)
  ·
    refine ⟨2302579013850143256310955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1535052675900095504207303 2302579013850143256310955)
    ·
      refine ⟨3453868520775214884466433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2302579013850143256310955 3453868520775214884466433)
      ·
        refine ⟨2590401390581411163349825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3453868520775214884466433 2590401390581411163349825)
        ·
          refine ⟨1942801042936058372512369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2590401390581411163349825 1942801042936058372512369)
          ·
            refine ⟨1457100782202043779384277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1942801042936058372512369 1457100782202043779384277)
            ·
              refine ⟨34150799582860401079319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1457100782202043779384277 34150799582860401079319)
              ·
                rfl

theorem cell20_673398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 2, 7].length) (baseStart_673398 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_673398 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_673398 prefixEnd_673398 := by exact prefixLift 673398
  have htrace : WordTrace (prefixWord ++ tailWord_673398) baseStart_673398 baseEnd_673398 := by
    simpa [prefixWord, tailWord_673398, baseEnd_673398] using wordTrace_append hprefix tailTrace_673398
  have hstable : (prefixWord ++ tailWord_673398).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_673398).length < 2 ^ (prefixWord ++ tailWord_673398).sum := by decide
  have hdescent : baseEnd_673398 < baseStart_673398 := by decide
  rcases family_descends (prefixWord ++ tailWord_673398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_673405 : List Nat := [1, 4, 1, 1, 4, 2, 1, 1, 5]
def baseStart_673405 : Nat := 118140960795 + 673405 * 2 ^ 59
def prefixEnd_673405 : Nat := 4983230072969 + 3 ^ 40 * 673405 * 2
def baseEnd_673405 : Nat := 307360391236482696480509

theorem tailTrace_673405 : CollatzResearch.WordTrace tailWord_673405 prefixEnd_673405 307360391236482696480509 := by
  unfold tailWord_673405
  simp only [CollatzResearch.WordTrace]
  refine ⟨24561098125376168262821669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16374065416917445508547779 24561098125376168262821669)
  ·
    refine ⟨4605205898508031549279063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24561098125376168262821669 4605205898508031549279063)
    ·
      refine ⟨6907808847762047323918595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4605205898508031549279063 6907808847762047323918595)
      ·
        refine ⟨10361713271643070985877893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6907808847762047323918595 10361713271643070985877893)
        ·
          refine ⟨1942821238433075809852105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10361713271643070985877893 1942821238433075809852105)
          ·
            refine ⟨1457115928824806857389079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1942821238433075809852105 1457115928824806857389079)
            ·
              refine ⟨2185673893237210286083619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1457115928824806857389079 2185673893237210286083619)
              ·
                refine ⟨3278510839855815429125429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2185673893237210286083619 3278510839855815429125429)
                ·
                  refine ⟨307360391236482696480509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3278510839855815429125429 307360391236482696480509)
                  ·
                    rfl

theorem cell20_673405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 2, 1, 1, 5].length) (baseStart_673405 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_673405 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_673405 prefixEnd_673405 := by exact prefixLift 673405
  have htrace : WordTrace (prefixWord ++ tailWord_673405) baseStart_673405 baseEnd_673405 := by
    simpa [prefixWord, tailWord_673405, baseEnd_673405] using wordTrace_append hprefix tailTrace_673405
  have hstable : (prefixWord ++ tailWord_673405).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_673405).length < 2 ^ (prefixWord ++ tailWord_673405).sum := by decide
  have hdescent : baseEnd_673405 < baseStart_673405 := by decide
  rcases family_descends (prefixWord ++ tailWord_673405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_673433 : List Nat := [1, 2, 1, 2, 1, 2, 2, 3, 6]
def baseStart_673433 : Nat := 118140960795 + 673433 * 2 ^ 59
def prefixEnd_673433 : Nat := 4983230072969 + 3 ^ 40 * 673433 * 2
def baseEnd_673433 : Nat := 307373171199439043547061

theorem tailTrace_673433 : CollatzResearch.WordTrace tailWord_673433 prefixEnd_673433 307373171199439043547061 := by
  unfold tailWord_673433
  simp only [CollatzResearch.WordTrace]
  refine ⟨24562119369274729044840953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16374746246183152696560635 24562119369274729044840953)
  ·
    refine ⟨18421589526956046783630715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24562119369274729044840953 18421589526956046783630715)
    ·
      refine ⟨27632384290434070175446073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18421589526956046783630715 27632384290434070175446073)
      ·
        refine ⟨20724288217825552631584555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27632384290434070175446073 20724288217825552631584555)
        ·
          refine ⟨31086432326738328947376833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20724288217825552631584555 31086432326738328947376833)
          ·
            refine ⟨23314824245053746710532625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31086432326738328947376833 23314824245053746710532625)
            ·
              refine ⟨17486118183790310032899469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23314824245053746710532625 17486118183790310032899469)
              ·
                refine ⟨6557294318921366262337301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17486118183790310032899469 6557294318921366262337301)
                ·
                  refine ⟨307373171199439043547061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6557294318921366262337301 307373171199439043547061)
                  ·
                    rfl

theorem cell20_673433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 3, 6].length) (baseStart_673433 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_673433 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_673433 prefixEnd_673433 := by exact prefixLift 673433
  have htrace : WordTrace (prefixWord ++ tailWord_673433) baseStart_673433 baseEnd_673433 := by
    simpa [prefixWord, tailWord_673433, baseEnd_673433] using wordTrace_append hprefix tailTrace_673433
  have hstable : (prefixWord ++ tailWord_673433).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_673433).length < 2 ^ (prefixWord ++ tailWord_673433).sum := by decide
  have hdescent : baseEnd_673433 < baseStart_673433 := by decide
  rcases family_descends (prefixWord ++ tailWord_673433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_673436 : List Nat := [2, 2, 3, 2, 3, 1, 1, 6]
def baseStart_673436 : Nat := 118140960795 + 673436 * 2 ^ 59
def prefixEnd_673436 : Nat := 4983230072969 + 3 ^ 40 * 673436 * 2
def baseEnd_673436 : Nat := 102458180160394788815683

theorem tailTrace_673436 : CollatzResearch.WordTrace tailWord_673436 prefixEnd_673436 102458180160394788815683 := by
  unfold tailWord_673436
  simp only [CollatzResearch.WordTrace]
  refine ⟨12281114394131930278600081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16374819192175907038133441 12281114394131930278600081)
  ·
    refine ⟨9210835795598947708950061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12281114394131930278600081 9210835795598947708950061)
    ·
      refine ⟨3454063423349605390856273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9210835795598947708950061 3454063423349605390856273)
      ·
        refine ⟨2590547567512204043142205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3454063423349605390856273 2590547567512204043142205)
        ·
          refine ⟨971455337817076516178327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2590547567512204043142205 971455337817076516178327)
          ·
            refine ⟨1457183006725614774267491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 971455337817076516178327 1457183006725614774267491)
            ·
              refine ⟨2185774510088422161401237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1457183006725614774267491 2185774510088422161401237)
              ·
                refine ⟨102458180160394788815683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2185774510088422161401237 102458180160394788815683)
                ·
                  rfl

theorem cell20_673436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 1, 1, 6].length) (baseStart_673436 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_673436 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_673436 prefixEnd_673436 := by exact prefixLift 673436
  have htrace : WordTrace (prefixWord ++ tailWord_673436) baseStart_673436 baseEnd_673436 := by
    simpa [prefixWord, tailWord_673436, baseEnd_673436] using wordTrace_append hprefix tailTrace_673436
  have hstable : (prefixWord ++ tailWord_673436).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_673436).length < 2 ^ (prefixWord ++ tailWord_673436).sum := by decide
  have hdescent : baseEnd_673436 < baseStart_673436 := by decide
  rcases family_descends (prefixWord ++ tailWord_673436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_673442 : List Nat := [3, 3, 1, 4, 1, 2, 1, 3, 2]
def baseStart_673442 : Nat := 118140960795 + 673442 * 2 ^ 59
def prefixEnd_673442 : Nat := 4983230072969 + 3 ^ 40 * 673442 * 2
def baseEnd_673442 : Nat := 307377279044675012247025

theorem tailTrace_673442 : CollatzResearch.WordTrace tailWord_673442 prefixEnd_673442 307377279044675012247025 := by
  unfold tailWord_673442
  simp only [CollatzResearch.WordTrace]
  refine ⟨6140611906560530895479645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16374965084161415721279053 6140611906560530895479645)
  ·
    refine ⟨2302729464960199085804867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6140611906560530895479645 2302729464960199085804867)
    ·
      refine ⟨3454094197440298628707301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2302729464960199085804867 3454094197440298628707301)
      ·
        refine ⟨647642662020055992882619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3454094197440298628707301 647642662020055992882619)
        ·
          refine ⟨971463993030083989323929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 647642662020055992882619 971463993030083989323929)
          ·
            refine ⟨728597994772562991992947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 971463993030083989323929 728597994772562991992947)
            ·
              refine ⟨1092896992158844487989421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 728597994772562991992947 1092896992158844487989421)
              ·
                refine ⟨409836372059566682996033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1092896992158844487989421 409836372059566682996033)
                ·
                  refine ⟨307377279044675012247025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 409836372059566682996033 307377279044675012247025)
                  ·
                    rfl

theorem cell20_673442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 2, 1, 3, 2].length) (baseStart_673442 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_673442 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_673442 prefixEnd_673442 := by exact prefixLift 673442
  have htrace : WordTrace (prefixWord ++ tailWord_673442) baseStart_673442 baseEnd_673442 := by
    simpa [prefixWord, tailWord_673442, baseEnd_673442] using wordTrace_append hprefix tailTrace_673442
  have hstable : (prefixWord ++ tailWord_673442).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_673442).length < 2 ^ (prefixWord ++ tailWord_673442).sum := by decide
  have hdescent : baseEnd_673442 < baseStart_673442 := by decide
  rcases family_descends (prefixWord ++ tailWord_673442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_673519 : List Nat := [1, 1, 2, 1, 5, 1, 4, 2, 3]
def baseStart_673519 : Nat := 118140960795 + 673519 * 2 ^ 59
def prefixEnd_673519 : Nat := 4983230072969 + 3 ^ 40 * 673519 * 2
def baseEnd_673519 : Nat := 307412423942804966680043

theorem tailTrace_673519 : CollatzResearch.WordTrace tailWord_673519 prefixEnd_673519 307412423942804966680043 := by
  unfold tailWord_673519
  simp only [CollatzResearch.WordTrace]
  refine ⟨24565256046963165732471611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16376837364642110488314407 24565256046963165732471611)
  ·
    refine ⟨36847884070444748598707417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24565256046963165732471611 36847884070444748598707417)
    ·
      refine ⟨27635913052833561449030563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36847884070444748598707417 27635913052833561449030563)
      ·
        refine ⟨41453869579250342173545845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27635913052833561449030563 41453869579250342173545845)
        ·
          refine ⟨3886300273054719578769923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 41453869579250342173545845 3886300273054719578769923)
          ·
            refine ⟨5829450409582079368154885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3886300273054719578769923 5829450409582079368154885)
            ·
              refine ⟨1093021951796639881529041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5829450409582079368154885 1093021951796639881529041)
              ·
                refine ⟨819766463847479911146781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1093021951796639881529041 819766463847479911146781)
                ·
                  refine ⟨307412423942804966680043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 819766463847479911146781 307412423942804966680043)
                  ·
                    rfl

theorem cell20_673519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 4, 2, 3].length) (baseStart_673519 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_673519 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_673519 prefixEnd_673519 := by exact prefixLift 673519
  have htrace : WordTrace (prefixWord ++ tailWord_673519) baseStart_673519 baseEnd_673519 := by
    simpa [prefixWord, tailWord_673519, baseEnd_673519] using wordTrace_append hprefix tailTrace_673519
  have hstable : (prefixWord ++ tailWord_673519).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_673519).length < 2 ^ (prefixWord ++ tailWord_673519).sum := by decide
  have hdescent : baseEnd_673519 < baseStart_673519 := by decide
  rcases family_descends (prefixWord ++ tailWord_673519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_673543 : List Nat := [1, 1, 4, 4, 2, 1, 1, 2, 4]
def baseStart_673543 : Nat := 118140960795 + 673543 * 2 ^ 59
def prefixEnd_673543 : Nat := 4983230072969 + 3 ^ 40 * 673543 * 2
def baseEnd_673543 : Nat := 307423378196767549879945

theorem tailTrace_673543 : CollatzResearch.WordTrace tailWord_673543 prefixEnd_673543 307423378196767549879945 := by
  unfold tailWord_673543
  simp only [CollatzResearch.WordTrace]
  refine ⟨24566131398876217831345283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16377420932584145220896855 24566131398876217831345283)
  ·
    refine ⟨36849197098314326747017925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24566131398876217831345283 36849197098314326747017925)
    ·
      refine ⟨6909224455933936265065861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 36849197098314326747017925 6909224455933936265065861)
      ·
        refine ⟨1295479585487613049699849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6909224455933936265065861 1295479585487613049699849)
        ·
          refine ⟨971609689115709787274887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1295479585487613049699849 971609689115709787274887)
          ·
            refine ⟨1457414533673564680912331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 971609689115709787274887 1457414533673564680912331)
            ·
              refine ⟨2186121800510347021368497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1457414533673564680912331 2186121800510347021368497)
              ·
                refine ⟨1639591350382760266026373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2186121800510347021368497 1639591350382760266026373)
                ·
                  refine ⟨307423378196767549879945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1639591350382760266026373 307423378196767549879945)
                  ·
                    rfl

theorem cell20_673543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 1, 1, 2, 4].length) (baseStart_673543 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_673543 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_673543 prefixEnd_673543 := by exact prefixLift 673543
  have htrace : WordTrace (prefixWord ++ tailWord_673543) baseStart_673543 baseEnd_673543 := by
    simpa [prefixWord, tailWord_673543, baseEnd_673543] using wordTrace_append hprefix tailTrace_673543
  have hstable : (prefixWord ++ tailWord_673543).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_673543).length < 2 ^ (prefixWord ++ tailWord_673543).sum := by decide
  have hdescent : baseEnd_673543 < baseStart_673543 := by decide
  rcases family_descends (prefixWord ++ tailWord_673543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_673547 : List Nat := [1, 1, 1, 1, 5, 1, 3, 1, 6]
def baseStart_673547 : Nat := 118140960795 + 673547 * 2 ^ 59
def prefixEnd_673547 : Nat := 4983230072969 + 3 ^ 40 * 673547 * 2
def baseEnd_673547 : Nat := 307425203905761313746595

theorem tailTrace_673547 : CollatzResearch.WordTrace tailWord_673547 prefixEnd_673547 307425203905761313746595 := by
  unfold tailWord_673547
  simp only [CollatzResearch.WordTrace]
  refine ⟨24566277290861726514490895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16377518193907817676327263 24566277290861726514490895)
  ·
    refine ⟨36849415936292589771736343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24566277290861726514490895 36849415936292589771736343)
    ·
      refine ⟨55274123904438884657604515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36849415936292589771736343 55274123904438884657604515)
      ·
        refine ⟨82911185856658326986406773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55274123904438884657604515 82911185856658326986406773)
        ·
          refine ⟨7772923674061718154975635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 82911185856658326986406773 7772923674061718154975635)
          ·
            refine ⟨11659385511092577232463453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7772923674061718154975635 11659385511092577232463453)
            ·
              refine ⟨4372269566659716462173795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11659385511092577232463453 4372269566659716462173795)
              ·
                refine ⟨6558404349989574693260693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4372269566659716462173795 6558404349989574693260693)
                ·
                  refine ⟨307425203905761313746595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6558404349989574693260693 307425203905761313746595)
                  ·
                    rfl

theorem cell20_673547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 3, 1, 6].length) (baseStart_673547 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_673547 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_673547 prefixEnd_673547 := by exact prefixLift 673547
  have htrace : WordTrace (prefixWord ++ tailWord_673547) baseStart_673547 baseEnd_673547 := by
    simpa [prefixWord, tailWord_673547, baseEnd_673547] using wordTrace_append hprefix tailTrace_673547
  have hstable : (prefixWord ++ tailWord_673547).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_673547).length < 2 ^ (prefixWord ++ tailWord_673547).sum := by decide
  have hdescent : baseEnd_673547 < baseStart_673547 := by decide
  rcases family_descends (prefixWord ++ tailWord_673547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_673636 : List Nat := [2, 3, 1, 1, 6, 1, 1, 1, 4]
def baseStart_673636 : Nat := 118140960795 + 673636 * 2 ^ 59
def prefixEnd_673636 : Nat := 4983230072969 + 3 ^ 40 * 673636 * 2
def baseEnd_673636 : Nat := 307465825930872559779565

theorem tailTrace_673636 : CollatzResearch.WordTrace tailWord_673636 prefixEnd_673636 307465825930872559779565 := by
  unfold tailWord_673636
  simp only [CollatzResearch.WordTrace]
  refine ⟨12284761693769647357240381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16379682258359529809653841 12284761693769647357240381)
  ·
    refine ⟨4606785635163617758965143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12284761693769647357240381 4606785635163617758965143)
    ·
      refine ⟨6910178452745426638447715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4606785635163617758965143 6910178452745426638447715)
      ·
        refine ⟨10365267679118139957671573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6910178452745426638447715 10365267679118139957671573)
        ·
          refine ⟨485871922458662810515855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 10365267679118139957671573 485871922458662810515855)
          ·
            refine ⟨728807883687994215773783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 485871922458662810515855 728807883687994215773783)
            ·
              refine ⟨1093211825531991323660675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 728807883687994215773783 1093211825531991323660675)
              ·
                refine ⟨1639817738297986985491013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1093211825531991323660675 1639817738297986985491013)
                ·
                  refine ⟨307465825930872559779565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1639817738297986985491013 307465825930872559779565)
                  ·
                    rfl

theorem cell20_673636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 6, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 6, 1, 1, 1, 4].length) (baseStart_673636 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_673636 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_673636 prefixEnd_673636 := by exact prefixLift 673636
  have htrace : WordTrace (prefixWord ++ tailWord_673636) baseStart_673636 baseEnd_673636 := by
    simpa [prefixWord, tailWord_673636, baseEnd_673636] using wordTrace_append hprefix tailTrace_673636
  have hstable : (prefixWord ++ tailWord_673636).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_673636).length < 2 ^ (prefixWord ++ tailWord_673636).sum := by decide
  have hdescent : baseEnd_673636 < baseStart_673636 := by decide
  rcases family_descends (prefixWord ++ tailWord_673636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_673661 : List Nat := [1, 4, 1, 1, 2, 1, 1, 3, 6]
def baseStart_673661 : Nat := 118140960795 + 673661 * 2 ^ 59
def prefixEnd_673661 : Nat := 4983230072969 + 3 ^ 40 * 673661 * 2
def baseEnd_673661 : Nat := 307477236612083583946129

theorem tailTrace_673661 : CollatzResearch.WordTrace tailWord_673661 prefixEnd_673661 307477236612083583946129 := by
  unfold tailWord_673661
  simp only [CollatzResearch.WordTrace]
  refine ⟨24570435212448723984140837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16380290141632482656093891 24570435212448723984140837)
  ·
    refine ⟨4606956602334135747026407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24570435212448723984140837 4606956602334135747026407)
    ·
      refine ⟨6910434903501203620539611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4606956602334135747026407 6910434903501203620539611)
      ·
        refine ⟨10365652355251805430809417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6910434903501203620539611 10365652355251805430809417)
        ·
          refine ⟨7774239266438854073107063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10365652355251805430809417 7774239266438854073107063)
          ·
            refine ⟨11661358899658281109660595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7774239266438854073107063 11661358899658281109660595)
            ·
              refine ⟨17492038349487421664490893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11661358899658281109660595 17492038349487421664490893)
              ·
                refine ⟨6559514381057783124184085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17492038349487421664490893 6559514381057783124184085)
                ·
                  refine ⟨307477236612083583946129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6559514381057783124184085 307477236612083583946129)
                  ·
                    rfl

theorem cell20_673661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 3, 6].length) (baseStart_673661 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_673661 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_673661 prefixEnd_673661 := by exact prefixLift 673661
  have htrace : WordTrace (prefixWord ++ tailWord_673661) baseStart_673661 baseEnd_673661 := by
    simpa [prefixWord, tailWord_673661, baseEnd_673661] using wordTrace_append hprefix tailTrace_673661
  have hstable : (prefixWord ++ tailWord_673661).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_673661).length < 2 ^ (prefixWord ++ tailWord_673661).sum := by decide
  have hdescent : baseEnd_673661 < baseStart_673661 := by decide
  rcases family_descends (prefixWord ++ tailWord_673661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_673699 : List Nat := [1, 1, 1, 4, 1, 2, 1, 5, 4]
def baseStart_673699 : Nat := 118140960795 + 673699 * 2 ^ 59
def prefixEnd_673699 : Nat := 4983230072969 + 3 ^ 40 * 673699 * 2
def baseEnd_673699 : Nat := 307494580847524340679307

theorem tailTrace_673699 : CollatzResearch.WordTrace tailWord_673699 prefixEnd_673699 307494580847524340679307 := by
  unfold tailWord_673699
  simp only [CollatzResearch.WordTrace]
  refine ⟨24571821186311056474024151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16381214124207370982682767 24571821186311056474024151)
  ·
    refine ⟨36857731779466584711036227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24571821186311056474024151 36857731779466584711036227)
    ·
      refine ⟨55286597669199877066554341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36857731779466584711036227 55286597669199877066554341)
      ·
        refine ⟨10366237062974976949978939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 55286597669199877066554341 10366237062974976949978939)
        ·
          refine ⟨15549355594462465424968409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10366237062974976949978939 15549355594462465424968409)
          ·
            refine ⟨11662016695846849068726307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15549355594462465424968409 11662016695846849068726307)
            ·
              refine ⟨17493025043770273603089461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11662016695846849068726307 17493025043770273603089461)
              ·
                refine ⟨1639971097853463150289637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 17493025043770273603089461 1639971097853463150289637)
                ·
                  refine ⟨307494580847524340679307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1639971097853463150289637 307494580847524340679307)
                  ·
                    rfl

theorem cell20_673699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 5, 4].length) (baseStart_673699 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_673699 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_673699 prefixEnd_673699 := by exact prefixLift 673699
  have htrace : WordTrace (prefixWord ++ tailWord_673699) baseStart_673699 baseEnd_673699 := by
    simpa [prefixWord, tailWord_673699, baseEnd_673699] using wordTrace_append hprefix tailTrace_673699
  have hstable : (prefixWord ++ tailWord_673699).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_673699).length < 2 ^ (prefixWord ++ tailWord_673699).sum := by decide
  have hdescent : baseEnd_673699 < baseStart_673699 := by decide
  rcases family_descends (prefixWord ++ tailWord_673699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_673750 : List Nat := [5, 2, 1, 1, 3, 1, 2, 1, 4]
def baseStart_673750 : Nat := 118140960795 + 673750 * 2 ^ 59
def prefixEnd_673750 : Nat := 4983230072969 + 3 ^ 40 * 673750 * 2
def baseEnd_673750 : Nat := 307517858637194829979099

theorem tailTrace_673750 : CollatzResearch.WordTrace tailWord_673750 prefixEnd_673750 307517858637194829979099 := by
  unfold tailWord_673750
  simp only [CollatzResearch.WordTrace]
  refine ⟨1535855081820393261508169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 16382454206084194789420469 1535855081820393261508169)
  ·
    refine ⟨1151891311365294946131127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1535855081820393261508169 1151891311365294946131127)
    ·
      refine ⟨1727836967047942419196691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1151891311365294946131127 1727836967047942419196691)
      ·
        refine ⟨2591755450571913628795037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1727836967047942419196691 2591755450571913628795037)
        ·
          refine ⟨971908293964467610798139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2591755450571913628795037 971908293964467610798139)
          ·
            refine ⟨1457862440946701416197209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 971908293964467610798139 1457862440946701416197209)
            ·
              refine ⟨1093396830710026062147907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1457862440946701416197209 1093396830710026062147907)
              ·
                refine ⟨1640095246065039093221861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1093396830710026062147907 1640095246065039093221861)
                ·
                  refine ⟨307517858637194829979099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1640095246065039093221861 307517858637194829979099)
                  ·
                    rfl

theorem cell20_673750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 1, 2, 1, 4].length) (baseStart_673750 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_673750 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_673750 prefixEnd_673750 := by exact prefixLift 673750
  have htrace : WordTrace (prefixWord ++ tailWord_673750) baseStart_673750 baseEnd_673750 := by
    simpa [prefixWord, tailWord_673750, baseEnd_673750] using wordTrace_append hprefix tailTrace_673750
  have hstable : (prefixWord ++ tailWord_673750).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_673750).length < 2 ^ (prefixWord ++ tailWord_673750).sum := by decide
  have hdescent : baseEnd_673750 < baseStart_673750 := by decide
  rcases family_descends (prefixWord ++ tailWord_673750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_673775 : List Nat := [1, 1, 2, 1, 4, 2, 1, 4, 4]
def baseStart_673775 : Nat := 118140960795 + 673775 * 2 ^ 59
def prefixEnd_673775 : Nat := 4983230072969 + 3 ^ 40 * 673775 * 2
def baseEnd_673775 : Nat := 307529269318405854145663

theorem tailTrace_673775 : CollatzResearch.WordTrace tailWord_673775 prefixEnd_673775 307529269318405854145663 := by
  unfold tailWord_673775
  simp only [CollatzResearch.WordTrace]
  refine ⟨24574593134035721453790779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16383062089357147635860519 24574593134035721453790779)
  ·
    refine ⟨36861889701053582180686169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24574593134035721453790779 36861889701053582180686169)
    ·
      refine ⟨27646417275790186635514627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36861889701053582180686169 27646417275790186635514627)
      ·
        refine ⟨41469625913685279953271941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27646417275790186635514627 41469625913685279953271941)
        ·
          refine ⟨7775554858815989991238489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 41469625913685279953271941 7775554858815989991238489)
          ·
            refine ⟨5831666144111992493428867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7775554858815989991238489 5831666144111992493428867)
            ·
              refine ⟨8747499216167988740143301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5831666144111992493428867 8747499216167988740143301)
              ·
                refine ⟨1640156103031497888776869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8747499216167988740143301 1640156103031497888776869)
                ·
                  refine ⟨307529269318405854145663, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1640156103031497888776869 307529269318405854145663)
                  ·
                    rfl

theorem cell20_673775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 1, 4, 4].length) (baseStart_673775 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_673775 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_673775 prefixEnd_673775 := by exact prefixLift 673775
  have htrace : WordTrace (prefixWord ++ tailWord_673775) baseStart_673775 baseEnd_673775 := by
    simpa [prefixWord, tailWord_673775, baseEnd_673775] using wordTrace_append hprefix tailTrace_673775
  have hstable : (prefixWord ++ tailWord_673775).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_673775).length < 2 ^ (prefixWord ++ tailWord_673775).sum := by decide
  have hdescent : baseEnd_673775 < baseStart_673775 := by decide
  rcases family_descends (prefixWord ++ tailWord_673775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_673792 : List Nat := [2, 1, 1, 2, 1, 1, 1, 9, 2]
def baseStart_673792 : Nat := 118140960795 + 673792 * 2 ^ 59
def prefixEnd_673792 : Nat := 4983230072969 + 3 ^ 40 * 673792 * 2
def baseEnd_673792 : Nat := 307537028581629350578927

theorem tailTrace_673792 : CollatzResearch.WordTrace tailWord_673792 prefixEnd_673792 307537028581629350578927 := by
  unfold tailWord_673792
  simp only [CollatzResearch.WordTrace]
  refine ⟨12287606587487066678579815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16383475449982755571439753 12287606587487066678579815)
  ·
    refine ⟨18431409881230600017869723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12287606587487066678579815 18431409881230600017869723)
    ·
      refine ⟨27647114821845900026804585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18431409881230600017869723 27647114821845900026804585)
      ·
        refine ⟨20735336116384425020103439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27647114821845900026804585 20735336116384425020103439)
        ·
          refine ⟨31103004174576637530155159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20735336116384425020103439 31103004174576637530155159)
          ·
            refine ⟨46654506261864956295232739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31103004174576637530155159 46654506261864956295232739)
            ·
              refine ⟨69981759392797434442849109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46654506261864956295232739 69981759392797434442849109)
              ·
                refine ⟨410049371442172467438569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 69981759392797434442849109 410049371442172467438569)
                ·
                  refine ⟨307537028581629350578927, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 410049371442172467438569 307537028581629350578927)
                  ·
                    rfl

theorem cell20_673792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 9, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 9, 2].length) (baseStart_673792 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_673792 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_673792 prefixEnd_673792 := by exact prefixLift 673792
  have htrace : WordTrace (prefixWord ++ tailWord_673792) baseStart_673792 baseEnd_673792 := by
    simpa [prefixWord, tailWord_673792, baseEnd_673792] using wordTrace_append hprefix tailTrace_673792
  have hstable : (prefixWord ++ tailWord_673792).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_673792).length < 2 ^ (prefixWord ++ tailWord_673792).sum := by decide
  have hdescent : baseEnd_673792 < baseStart_673792 := by decide
  rcases family_descends (prefixWord ++ tailWord_673792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_673799 : List Nat := [1, 1, 4, 3, 1, 4, 6]
def baseStart_673799 : Nat := 118140960795 + 673799 * 2 ^ 59
def prefixEnd_673799 : Nat := 4983230072969 + 3 ^ 40 * 673799 * 2
def baseEnd_673799 : Nat := 34171135952485381927285

theorem tailTrace_673799 : CollatzResearch.WordTrace tailWord_673799 prefixEnd_673799 34171135952485381927285 := by
  unfold tailWord_673799
  simp only [CollatzResearch.WordTrace]
  refine ⟨24575468485948773552664451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16383645657299182368442967 24575468485948773552664451)
  ·
    refine ⟨36863202728923160328996677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24575468485948773552664451 36863202728923160328996677)
    ·
      refine ⟨6911850511673092561686877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 36863202728923160328996677 6911850511673092561686877)
      ·
        refine ⟨2591943941877409710632579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6911850511673092561686877 2591943941877409710632579)
        ·
          refine ⟨3887915912816114565948869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2591943941877409710632579 3887915912816114565948869)
          ·
            refine ⟨728984233653021481115413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3887915912816114565948869 728984233653021481115413)
            ·
              refine ⟨34171135952485381927285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 728984233653021481115413 34171135952485381927285)
              ·
                rfl

theorem cell20_673799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 4, 6].length) (baseStart_673799 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_673799 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_673799 prefixEnd_673799 := by exact prefixLift 673799
  have htrace : WordTrace (prefixWord ++ tailWord_673799) baseStart_673799 baseEnd_673799 := by
    simpa [prefixWord, tailWord_673799, baseEnd_673799] using wordTrace_append hprefix tailTrace_673799
  have hstable : (prefixWord ++ tailWord_673799).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_673799).length < 2 ^ (prefixWord ++ tailWord_673799).sum := by decide
  have hdescent : baseEnd_673799 < baseStart_673799 := by decide
  rcases family_descends (prefixWord ++ tailWord_673799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_673806 : List Nat := [4, 1, 1, 2, 2, 1, 1, 3, 5]
def baseStart_673806 : Nat := 118140960795 + 673806 * 2 ^ 59
def prefixEnd_673806 : Nat := 4983230072969 + 3 ^ 40 * 673806 * 2
def baseEnd_673806 : Nat := 307543418563107524112203

theorem tailTrace_673806 : CollatzResearch.WordTrace tailWord_673806 prefixEnd_673806 307543418563107524112203 := by
  unfold tailWord_673806
  simp only [CollatzResearch.WordTrace]
  refine ⟨3071965474615426718521159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16383815864615609165446181 3071965474615426718521159)
  ·
    refine ⟨4607948211923140077781739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3071965474615426718521159 4607948211923140077781739)
    ·
      refine ⟨6911922317884710116672609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4607948211923140077781739 6911922317884710116672609)
      ·
        refine ⟨5183941738413532587504457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6911922317884710116672609 5183941738413532587504457)
        ·
          refine ⟨3887956303810149440628343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5183941738413532587504457 3887956303810149440628343)
          ·
            refine ⟨5831934455715224160942515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3887956303810149440628343 5831934455715224160942515)
            ·
              refine ⟨8747901683572836241413773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5831934455715224160942515 8747901683572836241413773)
              ·
                refine ⟨3280463131339813590530165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8747901683572836241413773 3280463131339813590530165)
                ·
                  refine ⟨307543418563107524112203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3280463131339813590530165 307543418563107524112203)
                  ·
                    rfl

theorem cell20_673806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 1, 3, 5].length) (baseStart_673806 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_673806 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_673806 prefixEnd_673806 := by exact prefixLift 673806
  have htrace : WordTrace (prefixWord ++ tailWord_673806) baseStart_673806 baseEnd_673806 := by
    simpa [prefixWord, tailWord_673806, baseEnd_673806] using wordTrace_append hprefix tailTrace_673806
  have hstable : (prefixWord ++ tailWord_673806).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_673806).length < 2 ^ (prefixWord ++ tailWord_673806).sum := by decide
  have hdescent : baseEnd_673806 < baseStart_673806 := by decide
  rcases family_descends (prefixWord ++ tailWord_673806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_673854 : List Nat := [4, 2, 1, 3, 3, 7]
def baseStart_673854 : Nat := 118140960795 + 673854 * 2 ^ 59
def prefixEnd_673854 : Nat := 4983230072969 + 3 ^ 40 * 673854 * 2
def baseEnd_673854 : Nat := 11391308410038247796741

theorem tailTrace_673854 : CollatzResearch.WordTrace tailWord_673854 prefixEnd_673854 11391308410038247796741 := by
  unfold tailWord_673854
  simp only [CollatzResearch.WordTrace]
  refine ⟨3072184312593689743239577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16384983000499678630611077 3072184312593689743239577)
  ·
    refine ⟨2304138234445267307429683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3072184312593689743239577 2304138234445267307429683)
    ·
      refine ⟨3456207351667900961144525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2304138234445267307429683 3456207351667900961144525)
      ·
        refine ⟨1296077756875462860429197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3456207351667900961144525 1296077756875462860429197)
        ·
          refine ⟨486029158828298572660949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1296077756875462860429197 486029158828298572660949)
          ·
            refine ⟨11391308410038247796741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 486029158828298572660949 11391308410038247796741)
            ·
              rfl

theorem cell20_673854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 3, 7].length) (baseStart_673854 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_673854 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_673854 prefixEnd_673854 := by exact prefixLift 673854
  have htrace : WordTrace (prefixWord ++ tailWord_673854) baseStart_673854 baseEnd_673854 := by
    simpa [prefixWord, tailWord_673854, baseEnd_673854] using wordTrace_append hprefix tailTrace_673854
  have hstable : (prefixWord ++ tailWord_673854).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_673854).length < 2 ^ (prefixWord ++ tailWord_673854).sum := by decide
  have hdescent : baseEnd_673854 < baseStart_673854 := by decide
  rcases family_descends (prefixWord ++ tailWord_673854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_673882 : List Nat := [3, 1, 1, 2, 1, 1, 3, 5, 3]
def baseStart_673882 : Nat := 118140960795 + 673882 * 2 ^ 59
def prefixEnd_673882 : Nat := 4983230072969 + 3 ^ 40 * 673882 * 2
def baseEnd_673882 : Nat := 307578107033989037578559

theorem tailTrace_673882 : CollatzResearch.WordTrace tailWord_673882 prefixEnd_673882 307578107033989037578559 := by
  unfold tailWord_673882
  simp only [CollatzResearch.WordTrace]
  refine ⟨6144623936162019681983975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16385663829765385818623933 6144623936162019681983975)
  ·
    refine ⟨9216935904243029522975963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6144623936162019681983975 9216935904243029522975963)
    ·
      refine ⟨13825403856364544284463945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9216935904243029522975963 13825403856364544284463945)
      ·
        refine ⟨10369052892273408213347959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13825403856364544284463945 10369052892273408213347959)
        ·
          refine ⟨15553579338410112320021939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10369052892273408213347959 15553579338410112320021939)
          ·
            refine ⟨23330369007615168480032909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15553579338410112320021939 23330369007615168480032909)
            ·
              refine ⟨8748888377855688180012341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23330369007615168480032909 8748888377855688180012341)
              ·
                refine ⟨820208285423970766876157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8748888377855688180012341 820208285423970766876157)
                ·
                  refine ⟨307578107033989037578559, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 820208285423970766876157 307578107033989037578559)
                  ·
                    rfl

theorem cell20_673882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 3, 5, 3].length) (baseStart_673882 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_673882 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_673882 prefixEnd_673882 := by exact prefixLift 673882
  have htrace : WordTrace (prefixWord ++ tailWord_673882) baseStart_673882 baseEnd_673882 := by
    simpa [prefixWord, tailWord_673882, baseEnd_673882] using wordTrace_append hprefix tailTrace_673882
  have hstable : (prefixWord ++ tailWord_673882).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_673882).length < 2 ^ (prefixWord ++ tailWord_673882).sum := by decide
  have hdescent : baseEnd_673882 < baseStart_673882 := by decide
  rcases family_descends (prefixWord ++ tailWord_673882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_673885 : List Nat := [1, 4, 4, 1, 1, 2, 1, 2, 4]
def baseStart_673885 : Nat := 118140960795 + 673885 * 2 ^ 59
def prefixEnd_673885 : Nat := 4983230072969 + 3 ^ 40 * 673885 * 2
def baseEnd_673885 : Nat := 307579476315734360478547

theorem tailTrace_673885 : CollatzResearch.WordTrace tailWord_673885 prefixEnd_673885 307579476315734360478547 := by
  unfold tailWord_673885
  simp only [CollatzResearch.WordTrace]
  refine ⟨24578605163637210240295109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16385736775758140160196739 24578605163637210240295109)
  ·
    refine ⟨4608488468181976920055333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24578605163637210240295109 4608488468181976920055333)
    ·
      refine ⟨864091587784120672510375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4608488468181976920055333 864091587784120672510375)
      ·
        refine ⟨1296137381676181008765563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 864091587784120672510375 1296137381676181008765563)
        ·
          refine ⟨1944206072514271513148345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1296137381676181008765563 1944206072514271513148345)
          ·
            refine ⟨1458154554385703634861259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1944206072514271513148345 1458154554385703634861259)
            ·
              refine ⟨2187231831578555452291889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1458154554385703634861259 2187231831578555452291889)
              ·
                refine ⟨1640423873683916589218917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2187231831578555452291889 1640423873683916589218917)
                ·
                  refine ⟨307579476315734360478547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1640423873683916589218917 307579476315734360478547)
                  ·
                    rfl

theorem cell20_673885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 2, 1, 2, 4].length) (baseStart_673885 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_673885 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_673885 prefixEnd_673885 := by exact prefixLift 673885
  have htrace : WordTrace (prefixWord ++ tailWord_673885) baseStart_673885 baseEnd_673885 := by
    simpa [prefixWord, tailWord_673885, baseEnd_673885] using wordTrace_append hprefix tailTrace_673885
  have hstable : (prefixWord ++ tailWord_673885).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_673885).length < 2 ^ (prefixWord ++ tailWord_673885).sum := by decide
  have hdescent : baseEnd_673885 < baseStart_673885 := by decide
  rcases family_descends (prefixWord ++ tailWord_673885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_673927 : List Nat := [1, 1, 4, 2, 1, 1, 3, 3, 4]
def baseStart_673927 : Nat := 118140960795 + 673927 * 2 ^ 59
def prefixEnd_673927 : Nat := 4983230072969 + 3 ^ 40 * 673927 * 2
def baseEnd_673927 : Nat := 307598646260168881078375

theorem tailTrace_673927 : CollatzResearch.WordTrace tailWord_673927 prefixEnd_673927 307598646260168881078375 := by
  unfold tailWord_673927
  simp only [CollatzResearch.WordTrace]
  refine ⟨24580137029485051413324035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16386758019656700942216023 24580137029485051413324035)
  ·
    refine ⟨36870205544227577119986053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24580137029485051413324035 36870205544227577119986053)
    ·
      refine ⟨6913163539542670709997385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 36870205544227577119986053 6913163539542670709997385)
      ·
        refine ⟨5184872654657003032498039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6913163539542670709997385 5184872654657003032498039)
        ·
          refine ⟨7777308981985504548747059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5184872654657003032498039 7777308981985504548747059)
          ·
            refine ⟨11665963472978256823120589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7777308981985504548747059 11665963472978256823120589)
            ·
              refine ⟨4374736302366846308670221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11665963472978256823120589 4374736302366846308670221)
              ·
                refine ⟨1640526113387567365751333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4374736302366846308670221 1640526113387567365751333)
                ·
                  refine ⟨307598646260168881078375, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1640526113387567365751333 307598646260168881078375)
                  ·
                    rfl

theorem cell20_673927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 3, 3, 4].length) (baseStart_673927 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_673927 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_673927 prefixEnd_673927 := by exact prefixLift 673927
  have htrace : WordTrace (prefixWord ++ tailWord_673927) baseStart_673927 baseEnd_673927 := by
    simpa [prefixWord, tailWord_673927, baseEnd_673927] using wordTrace_append hprefix tailTrace_673927
  have hstable : (prefixWord ++ tailWord_673927).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_673927).length < 2 ^ (prefixWord ++ tailWord_673927).sum := by decide
  have hdescent : baseEnd_673927 < baseStart_673927 := by decide
  rcases family_descends (prefixWord ++ tailWord_673927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_673951 : List Nat := [1, 1, 2, 6, 1, 2, 1, 6]
def baseStart_673951 : Nat := 118140960795 + 673951 * 2 ^ 59
def prefixEnd_673951 : Nat := 4983230072969 + 3 ^ 40 * 673951 * 2
def baseEnd_673951 : Nat := 102536533504710488092759

theorem tailTrace_673951 : CollatzResearch.WordTrace tailWord_673951 prefixEnd_673951 102536533504710488092759 := by
  unfold tailWord_673951
  simp only [CollatzResearch.WordTrace]
  refine ⟨24581012381398103512197707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16387341587598735674798471 24581012381398103512197707)
  ·
    refine ⟨36871518572097155268296561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24581012381398103512197707 36871518572097155268296561)
    ·
      refine ⟨27653638929072866451222421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36871518572097155268296561 27653638929072866451222421)
      ·
        refine ⟨1296264324800290614901051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 27653638929072866451222421 1296264324800290614901051)
        ·
          refine ⟨1944396487200435922351577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1296264324800290614901051 1944396487200435922351577)
          ·
            refine ⟨1458297365400326941763683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1944396487200435922351577 1458297365400326941763683)
            ·
              refine ⟨2187446048100490412645525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1458297365400326941763683 2187446048100490412645525)
              ·
                refine ⟨102536533504710488092759, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2187446048100490412645525 102536533504710488092759)
                ·
                  rfl

theorem cell20_673951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 2, 1, 6].length) (baseStart_673951 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_673951 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_673951 prefixEnd_673951 := by exact prefixLift 673951
  have htrace : WordTrace (prefixWord ++ tailWord_673951) baseStart_673951 baseEnd_673951 := by
    simpa [prefixWord, tailWord_673951, baseEnd_673951] using wordTrace_append hprefix tailTrace_673951
  have hstable : (prefixWord ++ tailWord_673951).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_673951).length < 2 ^ (prefixWord ++ tailWord_673951).sum := by decide
  have hdescent : baseEnd_673951 < baseStart_673951 := by decide
  rcases family_descends (prefixWord ++ tailWord_673951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_673979 : List Nat := [1, 1, 1, 1, 1, 2, 5, 3, 5]
def baseStart_673979 : Nat := 118140960795 + 673979 * 2 ^ 59
def prefixEnd_673979 : Nat := 4983230072969 + 3 ^ 40 * 673979 * 2
def baseEnd_673979 : Nat := 307622380477087811344829

theorem tailTrace_673979 : CollatzResearch.WordTrace tailWord_673979 prefixEnd_673979 307622380477087811344829 := by
  unfold tailWord_673979
  simp only [CollatzResearch.WordTrace]
  refine ⟨24582033625296664294216991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16388022416864442862811327 24582033625296664294216991)
  ·
    refine ⟨36873050437944996441325487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24582033625296664294216991 36873050437944996441325487)
    ·
      refine ⟨55309575656917494661988231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36873050437944996441325487 55309575656917494661988231)
      ·
        refine ⟨82964363485376241992982347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55309575656917494661988231 82964363485376241992982347)
        ·
          refine ⟨124446545228064362989473521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82964363485376241992982347 124446545228064362989473521)
          ·
            refine ⟨93334908921048272242105141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 124446545228064362989473521 93334908921048272242105141)
            ·
              refine ⟨8750147711348275522697357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 93334908921048272242105141 8750147711348275522697357)
              ·
                refine ⟨3281305391755603321011509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8750147711348275522697357 3281305391755603321011509)
                ·
                  refine ⟨307622380477087811344829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3281305391755603321011509 307622380477087811344829)
                  ·
                    rfl

theorem cell20_673979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 5, 3, 5].length) (baseStart_673979 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_673979 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_673979 prefixEnd_673979 := by exact prefixLift 673979
  have htrace : WordTrace (prefixWord ++ tailWord_673979) baseStart_673979 baseEnd_673979 := by
    simpa [prefixWord, tailWord_673979, baseEnd_673979] using wordTrace_append hprefix tailTrace_673979
  have hstable : (prefixWord ++ tailWord_673979).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_673979).length < 2 ^ (prefixWord ++ tailWord_673979).sum := by decide
  have hdescent : baseEnd_673979 < baseStart_673979 := by decide
  rcases family_descends (prefixWord ++ tailWord_673979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_674006 : List Nat := [5, 2, 1, 2, 1, 1, 2, 6]
def baseStart_674006 : Nat := 118140960795 + 674006 * 2 ^ 59
def prefixEnd_674006 : Nat := 4983230072969 + 3 ^ 40 * 674006 * 2
def baseEnd_674006 : Nat := 102544901337598572481573

theorem tailTrace_674006 : CollatzResearch.WordTrace tailWord_674006 prefixEnd_674006 102544901337598572481573 := by
  unfold tailWord_674006
  simp only [CollatzResearch.WordTrace]
  refine ⟨1536438649762427994090617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 16388678930799231936966581 1536438649762427994090617)
  ·
    refine ⟨1152328987321820995567963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1536438649762427994090617 1152328987321820995567963)
    ·
      refine ⟨1728493480982731493351945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1152328987321820995567963 1728493480982731493351945)
      ·
        refine ⟨1296370110737048620013959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1728493480982731493351945 1296370110737048620013959)
        ·
          refine ⟨1944555166105572930020939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1296370110737048620013959 1944555166105572930020939)
          ·
            refine ⟨2916832749158359395031409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1944555166105572930020939 2916832749158359395031409)
            ·
              refine ⟨2187624561868769546273557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2916832749158359395031409 2187624561868769546273557)
              ·
                refine ⟨102544901337598572481573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2187624561868769546273557 102544901337598572481573)
                ·
                  rfl

theorem cell20_674006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 2, 6].length) (baseStart_674006 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_674006 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_674006 prefixEnd_674006 := by exact prefixLift 674006
  have htrace : WordTrace (prefixWord ++ tailWord_674006) baseStart_674006 baseEnd_674006 := by
    simpa [prefixWord, tailWord_674006, baseEnd_674006] using wordTrace_append hprefix tailTrace_674006
  have hstable : (prefixWord ++ tailWord_674006).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_674006).length < 2 ^ (prefixWord ++ tailWord_674006).sum := by decide
  have hdescent : baseEnd_674006 < baseStart_674006 := by decide
  rcases family_descends (prefixWord ++ tailWord_674006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_674010 : List Nat := [3, 1, 1, 2, 2, 1, 4, 6]
def baseStart_674010 : Nat := 118140960795 + 674010 * 2 ^ 59
def prefixEnd_674010 : Nat := 4983230072969 + 3 ^ 40 * 674010 * 2
def baseEnd_674010 : Nat := 102545509907263160437123

theorem tailTrace_674010 : CollatzResearch.WordTrace tailWord_674010 prefixEnd_674010 102545509907263160437123 := by
  unfold tailWord_674010
  simp only [CollatzResearch.WordTrace]
  refine ⟨6145791072046089147148871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16388776192122904392396989 6145791072046089147148871)
  ·
    refine ⟨9218686608069133720723307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6145791072046089147148871 9218686608069133720723307)
    ·
      refine ⟨13828029912103700581084961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9218686608069133720723307 13828029912103700581084961)
      ·
        refine ⟨10371022434077775435813721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13828029912103700581084961 10371022434077775435813721)
        ·
          refine ⟨7778266825558331576860291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10371022434077775435813721 7778266825558331576860291)
          ·
            refine ⟨11667400238337497365290437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7778266825558331576860291 11667400238337497365290437)
            ·
              refine ⟨2187637544688280755991957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11667400238337497365290437 2187637544688280755991957)
              ·
                refine ⟨102545509907263160437123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2187637544688280755991957 102545509907263160437123)
                ·
                  rfl

theorem cell20_674010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 4, 6].length) (baseStart_674010 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_674010 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_674010 prefixEnd_674010 := by exact prefixLift 674010
  have htrace : WordTrace (prefixWord ++ tailWord_674010) baseStart_674010 baseEnd_674010 := by
    simpa [prefixWord, tailWord_674010, baseEnd_674010] using wordTrace_append hprefix tailTrace_674010
  have hstable : (prefixWord ++ tailWord_674010).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_674010).length < 2 ^ (prefixWord ++ tailWord_674010).sum := by decide
  have hdescent : baseEnd_674010 < baseStart_674010 := by decide
  rcases family_descends (prefixWord ++ tailWord_674010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_674020 : List Nat := [2, 3, 1, 1, 1, 2, 1, 7, 2]
def baseStart_674020 : Nat := 118140960795 + 674020 * 2 ^ 59
def prefixEnd_674020 : Nat := 4983230072969 + 3 ^ 40 * 674020 * 2
def baseEnd_674020 : Nat := 307641093994273890977995

theorem tailTrace_674020 : CollatzResearch.WordTrace tailWord_674020 prefixEnd_674020 307641093994273890977995 := by
  unfold tailWord_674020
  simp only [CollatzResearch.WordTrace]
  refine ⟨12291764509074064148229757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16389019345432085530973009 12291764509074064148229757)
  ·
    refine ⟨4609411690902774055586159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12291764509074064148229757 4609411690902774055586159)
    ·
      refine ⟨6914117536354161083379239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4609411690902774055586159 6914117536354161083379239)
      ·
        refine ⟨10371176304531241625068859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6914117536354161083379239 10371176304531241625068859)
        ·
          refine ⟨15556764456796862437603289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10371176304531241625068859 15556764456796862437603289)
          ·
            refine ⟨11667573342597646828202467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15556764456796862437603289 11667573342597646828202467)
            ·
              refine ⟨17501360013896470242303701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11667573342597646828202467 17501360013896470242303701)
              ·
                refine ⟨410188125325698521303993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 17501360013896470242303701 410188125325698521303993)
                ·
                  refine ⟨307641093994273890977995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 410188125325698521303993 307641093994273890977995)
                  ·
                    rfl

theorem cell20_674020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 7, 2].length) (baseStart_674020 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_674020 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_674020 prefixEnd_674020 := by exact prefixLift 674020
  have htrace : WordTrace (prefixWord ++ tailWord_674020) baseStart_674020 baseEnd_674020 := by
    simpa [prefixWord, tailWord_674020, baseEnd_674020] using wordTrace_append hprefix tailTrace_674020
  have hstable : (prefixWord ++ tailWord_674020).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_674020).length < 2 ^ (prefixWord ++ tailWord_674020).sum := by decide
  have hdescent : baseEnd_674020 < baseStart_674020 := by decide
  rcases family_descends (prefixWord ++ tailWord_674020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_674048 : List Nat := [2, 1, 1, 2, 1, 1, 7, 5]
def baseStart_674048 : Nat := 118140960795 + 674048 * 2 ^ 59
def prefixEnd_674048 : Nat := 4983230072969 + 3 ^ 40 * 674048 * 2
def baseEnd_674048 : Nat := 102551291319076746014849

theorem tailTrace_674048 : CollatzResearch.WordTrace tailWord_674048 prefixEnd_674048 102551291319076746014849 := by
  unfold tailWord_674048
  simp only [CollatzResearch.WordTrace]
  refine ⟨12292275131023344539239399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16389700174697792718985865 12292275131023344539239399)
  ·
    refine ⟨18438412696535016808859099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12292275131023344539239399 18438412696535016808859099)
    ·
      refine ⟨27657619044802525213288649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18438412696535016808859099 27657619044802525213288649)
      ·
        refine ⟨20743214283601893909966487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27657619044802525213288649 20743214283601893909966487)
        ·
          refine ⟨31114821425402840864949731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20743214283601893909966487 31114821425402840864949731)
          ·
            refine ⟨46672232138104261297424597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31114821425402840864949731 46672232138104261297424597)
            ·
              refine ⟨1093880440736818624158389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 46672232138104261297424597 1093880440736818624158389)
              ·
                refine ⟨102551291319076746014849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1093880440736818624158389 102551291319076746014849)
                ·
                  rfl

theorem cell20_674048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 7, 5].length) (baseStart_674048 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_674048 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_674048 prefixEnd_674048 := by exact prefixLift 674048
  have htrace : WordTrace (prefixWord ++ tailWord_674048) baseStart_674048 baseEnd_674048 := by
    simpa [prefixWord, tailWord_674048, baseEnd_674048] using wordTrace_append hprefix tailTrace_674048
  have hstable : (prefixWord ++ tailWord_674048).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_674048).length < 2 ^ (prefixWord ++ tailWord_674048).sum := by decide
  have hdescent : baseEnd_674048 < baseStart_674048 := by decide
  rcases family_descends (prefixWord ++ tailWord_674048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_674065 : List Nat := [1, 2, 2, 1, 1, 6, 3, 4]
def baseStart_674065 : Nat := 118140960795 + 674065 * 2 ^ 59
def prefixEnd_674065 : Nat := 4983230072969 + 3 ^ 40 * 674065 * 2
def baseEnd_674065 : Nat := 102553877740151244825937

theorem tailTrace_674065 : CollatzResearch.WordTrace tailWord_674065 prefixEnd_674065 102553877740151244825937 := by
  unfold tailWord_674065
  simp only [CollatzResearch.WordTrace]
  refine ⟨24585170302985100981847649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16390113535323400654565099 24585170302985100981847649)
  ·
    refine ⟨18438877727238825736385737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24585170302985100981847649 18438877727238825736385737)
    ·
      refine ⟨13829158295429119302289303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18438877727238825736385737 13829158295429119302289303)
      ·
        refine ⟨20743737443143678953433955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13829158295429119302289303 20743737443143678953433955)
        ·
          refine ⟨31115606164715518430150933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20743737443143678953433955 31115606164715518430150933)
          ·
            refine ⟨1458544038971039926413325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 31115606164715518430150933 1458544038971039926413325)
            ·
              refine ⟨546954014614139972404997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1458544038971039926413325 546954014614139972404997)
              ·
                refine ⟨102553877740151244825937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 546954014614139972404997 102553877740151244825937)
                ·
                  rfl

theorem cell20_674065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 6, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 6, 3, 4].length) (baseStart_674065 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_674065 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_674065 prefixEnd_674065 := by exact prefixLift 674065
  have htrace : WordTrace (prefixWord ++ tailWord_674065) baseStart_674065 baseEnd_674065 := by
    simpa [prefixWord, tailWord_674065, baseEnd_674065] using wordTrace_append hprefix tailTrace_674065
  have hstable : (prefixWord ++ tailWord_674065).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_674065).length < 2 ^ (prefixWord ++ tailWord_674065).sum := by decide
  have hdescent : baseEnd_674065 < baseStart_674065 := by decide
  rcases family_descends (prefixWord ++ tailWord_674065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_674116 : List Nat := [2, 3, 4, 1, 3, 1, 2, 4]
def baseStart_674116 : Nat := 118140960795 + 674116 * 2 ^ 59
def prefixEnd_674116 : Nat := 4983230072969 + 3 ^ 40 * 674116 * 2
def baseEnd_674116 : Nat := 102561637003374741259201

theorem tailTrace_674116 : CollatzResearch.WordTrace tailWord_674116 prefixEnd_674116 102561637003374741259201 := by
  unfold tailWord_674116
  simp only [CollatzResearch.WordTrace]
  refine ⟨12293515212900168345977101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16391353617200224461302801 12293515212900168345977101)
  ·
    refine ⟨4610068204837563129741413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12293515212900168345977101 4610068204837563129741413)
    ·
      refine ⟨864387788407043086826515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4610068204837563129741413 864387788407043086826515)
      ·
        refine ⟨1296581682610564630239773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 864387788407043086826515 1296581682610564630239773)
        ·
          refine ⟨486218130978961736339915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1296581682610564630239773 486218130978961736339915)
          ·
            refine ⟨729327196468442604509873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 486218130978961736339915 729327196468442604509873)
            ·
              refine ⟨546995397351331953382405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 729327196468442604509873 546995397351331953382405)
              ·
                refine ⟨102561637003374741259201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 546995397351331953382405 102561637003374741259201)
                ·
                  rfl

theorem cell20_674116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 3, 1, 2, 4].length) (baseStart_674116 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_674116 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_674116 prefixEnd_674116 := by exact prefixLift 674116
  have htrace : WordTrace (prefixWord ++ tailWord_674116) baseStart_674116 baseEnd_674116 := by
    simpa [prefixWord, tailWord_674116, baseEnd_674116] using wordTrace_append hprefix tailTrace_674116
  have hstable : (prefixWord ++ tailWord_674116).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_674116).length < 2 ^ (prefixWord ++ tailWord_674116).sum := by decide
  have hdescent : baseEnd_674116 < baseStart_674116 := by decide
  rcases family_descends (prefixWord ++ tailWord_674116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_674124 : List Nat := [2, 2, 1, 3, 2, 1, 3, 6]
def baseStart_674124 : Nat := 118140960795 + 674124 * 2 ^ 59
def prefixEnd_674124 : Nat := 4983230072969 + 3 ^ 40 * 674124 * 2
def baseEnd_674124 : Nat := 102562854142703917170301

theorem tailTrace_674124 : CollatzResearch.WordTrace tailWord_674124 prefixEnd_674124 102562854142703917170301 := by
  unfold tailWord_674124
  simp only [CollatzResearch.WordTrace]
  refine ⟨12293661104885677029122713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16391548139847569372163617 12293661104885677029122713)
  ·
    refine ⟨9220245828664257771842035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12293661104885677029122713 9220245828664257771842035)
    ·
      refine ⟨13830368742996386657763053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9220245828664257771842035 13830368742996386657763053)
      ·
        refine ⟨5186388278623644996661145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13830368742996386657763053 5186388278623644996661145)
        ·
          refine ⟨3889791208967733747495859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5186388278623644996661145 3889791208967733747495859)
          ·
            refine ⟨5834686813451600621243789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3889791208967733747495859 5834686813451600621243789)
            ·
              refine ⟨2188007555044350232966421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5834686813451600621243789 2188007555044350232966421)
              ·
                refine ⟨102562854142703917170301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2188007555044350232966421 102562854142703917170301)
                ·
                  rfl

theorem cell20_674124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 3, 6].length) (baseStart_674124 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_674124 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_674124 prefixEnd_674124 := by exact prefixLift 674124
  have htrace : WordTrace (prefixWord ++ tailWord_674124) baseStart_674124 baseEnd_674124 := by
    simpa [prefixWord, tailWord_674124, baseEnd_674124] using wordTrace_append hprefix tailTrace_674124
  have hstable : (prefixWord ++ tailWord_674124).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_674124).length < 2 ^ (prefixWord ++ tailWord_674124).sum := by decide
  have hdescent : baseEnd_674124 < baseStart_674124 := by decide
  rcases family_descends (prefixWord ++ tailWord_674124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan20Incremental
