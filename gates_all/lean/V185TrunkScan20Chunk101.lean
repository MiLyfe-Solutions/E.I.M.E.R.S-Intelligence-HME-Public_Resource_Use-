import V185TrunkScan20Chunk100

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental

namespace V185TrunkScan20Incremental

def tailWord_614384 : List Nat := [2, 1, 1, 1, 3, 2, 5, 5]
def baseStart_614384 : Nat := 118140960795 + 614384 * 2 ^ 59
def prefixEnd_614384 : Nat := 4983230072969 + 3 ^ 40 * 614384 * 2
def baseEnd_614384 : Nat := 93473866202082801029483

theorem tailTrace_614384 : CollatzResearch.WordTrace tailWord_614384 prefixEnd_614384 93473866202082801029483 := by
  unfold tailWord_614384
  simp only [CollatzResearch.WordTrace]
  refine ⟨11204212703099585639265103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14938950270799447519020137 11204212703099585639265103)
  ·
    refine ⟨16806319054649378458897655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11204212703099585639265103 16806319054649378458897655)
    ·
      refine ⟨25209478581974067688346483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16806319054649378458897655 25209478581974067688346483)
      ·
        refine ⟨37814217872961101532519725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25209478581974067688346483 37814217872961101532519725)
        ·
          refine ⟨14180331702360413074694897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37814217872961101532519725 14180331702360413074694897)
          ·
            refine ⟨10635248776770309806021173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14180331702360413074694897 10635248776770309806021173)
            ·
              refine ⟨997054572822216544314485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 10635248776770309806021173 997054572822216544314485)
              ·
                refine ⟨93473866202082801029483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 997054572822216544314485 93473866202082801029483)
                ·
                  rfl

theorem cell20_614384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 5, 5].length) (baseStart_614384 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_614384 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_614384 prefixEnd_614384 := by exact prefixLift 614384
  have htrace : WordTrace (prefixWord ++ tailWord_614384) baseStart_614384 baseEnd_614384 := by
    simpa [prefixWord, tailWord_614384, baseEnd_614384] using wordTrace_append hprefix tailTrace_614384
  have hstable : (prefixWord ++ tailWord_614384).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_614384).length < 2 ^ (prefixWord ++ tailWord_614384).sum := by decide
  have hdescent : baseEnd_614384 < baseStart_614384 := by decide
  rcases family_descends (prefixWord ++ tailWord_614384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_614401 : List Nat := [1, 2, 4, 1, 2, 1, 5, 4]
def baseStart_614401 : Nat := 118140960795 + 614401 * 2 ^ 59
def prefixEnd_614401 : Nat := 4983230072969 + 3 ^ 40 * 614401 * 2
def baseEnd_614401 : Nat := 93476452623157299840571

theorem tailTrace_614401 : CollatzResearch.WordTrace tailWord_614401 prefixEnd_614401 93476452623157299840571 := by
  unfold tailWord_614401
  simp only [CollatzResearch.WordTrace]
  refine ⟨22409045447137583181899057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14939363631425055454599371 22409045447137583181899057)
  ·
    refine ⟨16806784085353187386424293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22409045447137583181899057 16806784085353187386424293)
    ·
      refine ⟨3151272016003722634954555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16806784085353187386424293 3151272016003722634954555)
      ·
        refine ⟨4726908024005583952431833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3151272016003722634954555 4726908024005583952431833)
        ·
          refine ⟨3545181018004187964323875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4726908024005583952431833 3545181018004187964323875)
          ·
            refine ⟨5317771527006281946485813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3545181018004187964323875 5317771527006281946485813)
            ·
              refine ⟨498541080656838932483045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5317771527006281946485813 498541080656838932483045)
              ·
                refine ⟨93476452623157299840571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 498541080656838932483045 93476452623157299840571)
                ·
                  rfl

theorem cell20_614401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 5, 4].length) (baseStart_614401 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_614401 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_614401 prefixEnd_614401 := by exact prefixLift 614401
  have htrace : WordTrace (prefixWord ++ tailWord_614401) baseStart_614401 baseEnd_614401 := by
    simpa [prefixWord, tailWord_614401, baseEnd_614401] using wordTrace_append hprefix tailTrace_614401
  have hstable : (prefixWord ++ tailWord_614401).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_614401).length < 2 ^ (prefixWord ++ tailWord_614401).sum := by decide
  have hdescent : baseEnd_614401 < baseStart_614401 := by decide
  rcases family_descends (prefixWord ++ tailWord_614401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_614442 : List Nat := [3, 1, 4, 1, 2, 2, 3, 1, 3]
def baseStart_614442 : Nat := 118140960795 + 614442 * 2 ^ 59
def prefixEnd_614442 : Nat := 4983230072969 + 3 ^ 40 * 614442 * 2
def baseEnd_614442 : Nat := 280448071386657979154879

theorem tailTrace_614442 : CollatzResearch.WordTrace tailWord_614442 prefixEnd_614442 280448071386657979154879 := by
  unfold tailWord_614442
  simp only [CollatzResearch.WordTrace]
  refine ⟨5602635209997261796035395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14940360559992698122761053 5602635209997261796035395)
  ·
    refine ⟨8403952814995892694053093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5602635209997261796035395 8403952814995892694053093)
    ·
      refine ⟨1575741152811729880134955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8403952814995892694053093 1575741152811729880134955)
      ·
        refine ⟨2363611729217594820202433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1575741152811729880134955 2363611729217594820202433)
        ·
          refine ⟨1772708796913196115151825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2363611729217594820202433 1772708796913196115151825)
          ·
            refine ⟨1329531597684897086363869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1772708796913196115151825 1329531597684897086363869)
            ·
              refine ⟨498574349131836407386451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1329531597684897086363869 498574349131836407386451)
              ·
                refine ⟨747861523697754611079677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 498574349131836407386451 747861523697754611079677)
                ·
                  refine ⟨280448071386657979154879, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 747861523697754611079677 280448071386657979154879)
                  ·
                    rfl

theorem cell20_614442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 2, 3, 1, 3].length) (baseStart_614442 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_614442 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_614442 prefixEnd_614442 := by exact prefixLift 614442
  have htrace : WordTrace (prefixWord ++ tailWord_614442) baseStart_614442 baseEnd_614442 := by
    simpa [prefixWord, tailWord_614442, baseEnd_614442] using wordTrace_append hprefix tailTrace_614442
  have hstable : (prefixWord ++ tailWord_614442).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_614442).length < 2 ^ (prefixWord ++ tailWord_614442).sum := by decide
  have hdescent : baseEnd_614442 < baseStart_614442 := by decide
  rcases family_descends (prefixWord ++ tailWord_614442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_614452 : List Nat := [2, 5, 1, 2, 3, 1, 2, 4]
def baseStart_614452 : Nat := 118140960795 + 614452 * 2 ^ 59
def prefixEnd_614452 : Nat := 4983230072969 + 3 ^ 40 * 614452 * 2
def baseEnd_614452 : Nat := 93484211886380796273835

theorem tailTrace_614452 : CollatzResearch.WordTrace tailWord_614452 prefixEnd_614452 93484211886380796273835 := by
  unfold tailWord_614452
  simp only [CollatzResearch.WordTrace]
  refine ⟨11205452784976409446002805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14940603713301879261337073 11205452784976409446002805)
  ·
    refine ⟨1050511198591538385562763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 11205452784976409446002805 1050511198591538385562763)
    ·
      refine ⟨1575766797887307578344145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1050511198591538385562763 1575766797887307578344145)
      ·
        refine ⟨1181825098415480683758109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1575766797887307578344145 1181825098415480683758109)
        ·
          refine ⟨443184411905805256409291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1181825098415480683758109 443184411905805256409291)
          ·
            refine ⟨664776617858707884613937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 443184411905805256409291 664776617858707884613937)
            ·
              refine ⟨498582463394030913460453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 664776617858707884613937 498582463394030913460453)
              ·
                refine ⟨93484211886380796273835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 498582463394030913460453 93484211886380796273835)
                ·
                  rfl

theorem cell20_614452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 3, 1, 2, 4].length) (baseStart_614452 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_614452 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_614452 prefixEnd_614452 := by exact prefixLift 614452
  have htrace : WordTrace (prefixWord ++ tailWord_614452) baseStart_614452 baseEnd_614452 := by
    simpa [prefixWord, tailWord_614452, baseEnd_614452] using wordTrace_append hprefix tailTrace_614452
  have hstable : (prefixWord ++ tailWord_614452).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_614452).length < 2 ^ (prefixWord ++ tailWord_614452).sum := by decide
  have hdescent : baseEnd_614452 < baseStart_614452 := by decide
  rcases family_descends (prefixWord ++ tailWord_614452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_614453 : List Nat := [1, 3, 3, 1, 1, 1, 4, 2, 4]
def baseStart_614453 : Nat := 118140960795 + 614453 * 2 ^ 59
def prefixEnd_614453 : Nat := 4983230072969 + 3 ^ 40 * 614453 * 2
def baseEnd_614453 : Nat := 280453092086390829788167

theorem tailTrace_614453 : CollatzResearch.WordTrace tailWord_614453 prefixEnd_614453 280453092086390829788167 := by
  unfold tailWord_614453
  simp only [CollatzResearch.WordTrace]
  refine ⟨22410942042949196062792013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14940628028632797375194675 22410942042949196062792013)
  ·
    refine ⟨8404103266105948523547005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22410942042949196062792013 8404103266105948523547005)
    ·
      refine ⟨3151538724789730696330127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8404103266105948523547005 3151538724789730696330127)
      ·
        refine ⟨4727308087184596044495191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3151538724789730696330127 4727308087184596044495191)
        ·
          refine ⟨7090962130776894066742787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4727308087184596044495191 7090962130776894066742787)
          ·
            refine ⟨10636443196165341100114181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7090962130776894066742787 10636443196165341100114181)
            ·
              refine ⟨1994333099281001456271409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10636443196165341100114181 1994333099281001456271409)
              ·
                refine ⟨1495749824460751092203557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1994333099281001456271409 1495749824460751092203557)
                ·
                  refine ⟨280453092086390829788167, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1495749824460751092203557 280453092086390829788167)
                  ·
                    rfl

theorem cell20_614453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 4, 2, 4].length) (baseStart_614453 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_614453 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_614453 prefixEnd_614453 := by exact prefixLift 614453
  have htrace : WordTrace (prefixWord ++ tailWord_614453) baseStart_614453 baseEnd_614453 := by
    simpa [prefixWord, tailWord_614453, baseEnd_614453] using wordTrace_append hprefix tailTrace_614453
  have hstable : (prefixWord ++ tailWord_614453).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_614453).length < 2 ^ (prefixWord ++ tailWord_614453).sum := by decide
  have hdescent : baseEnd_614453 < baseStart_614453 := by decide
  rcases family_descends (prefixWord ++ tailWord_614453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_614456 : List Nat := [2, 1, 2, 1, 6, 2, 2, 4]
def baseStart_614456 : Nat := 118140960795 + 614456 * 2 ^ 59
def prefixEnd_614456 : Nat := 4983230072969 + 3 ^ 40 * 614456 * 2
def baseEnd_614456 : Nat := 93484820456045384229385

theorem tailTrace_614456 : CollatzResearch.WordTrace tailWord_614456 prefixEnd_614456 93484820456045384229385 := by
  unfold tailWord_614456
  simp only [CollatzResearch.WordTrace]
  refine ⟨11205525730969163787575611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14940700974625551716767481 11205525730969163787575611)
  ·
    refine ⟨16808288596453745681363417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11205525730969163787575611 16808288596453745681363417)
    ·
      refine ⟨12606216447340309261022563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16808288596453745681363417 12606216447340309261022563)
      ·
        refine ⟨18909324671010463891533845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12606216447340309261022563 18909324671010463891533845)
        ·
          refine ⟨886374593953615494915649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 18909324671010463891533845 886374593953615494915649)
          ·
            refine ⟨664780945465211621186737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 886374593953615494915649 664780945465211621186737)
            ·
              refine ⟨498585709098908715890053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 664780945465211621186737 498585709098908715890053)
              ·
                refine ⟨93484820456045384229385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 498585709098908715890053 93484820456045384229385)
                ·
                  rfl

theorem cell20_614456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 2, 2, 4].length) (baseStart_614456 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_614456 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_614456 prefixEnd_614456 := by exact prefixLift 614456
  have htrace : WordTrace (prefixWord ++ tailWord_614456) baseStart_614456 baseEnd_614456 := by
    simpa [prefixWord, tailWord_614456, baseEnd_614456] using wordTrace_append hprefix tailTrace_614456
  have hstable : (prefixWord ++ tailWord_614456).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_614456).length < 2 ^ (prefixWord ++ tailWord_614456).sum := by decide
  have hdescent : baseEnd_614456 < baseStart_614456 := by decide
  rcases family_descends (prefixWord ++ tailWord_614456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_614460 : List Nat := [2, 2, 2, 2, 2, 1, 3, 6]
def baseStart_614460 : Nat := 118140960795 + 614460 * 2 ^ 59
def prefixEnd_614460 : Nat := 4983230072969 + 3 ^ 40 * 614460 * 2
def baseEnd_614460 : Nat := 93485429025709972184935

theorem tailTrace_614460 : CollatzResearch.WordTrace tailWord_614460 prefixEnd_614460 93485429025709972184935 := by
  unfold tailWord_614460
  simp only [CollatzResearch.WordTrace]
  refine ⟨11205598676961918129148417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14940798235949224172197889 11205598676961918129148417)
  ·
    refine ⟨8404199007721438596861313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11205598676961918129148417 8404199007721438596861313)
    ·
      refine ⟨6303149255791078947645985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8404199007721438596861313 6303149255791078947645985)
      ·
        refine ⟨4727361941843309210734489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6303149255791078947645985 4727361941843309210734489)
        ·
          refine ⟨3545521456382481908050867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4727361941843309210734489 3545521456382481908050867)
          ·
            refine ⟨5318282184573722862076301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3545521456382481908050867 5318282184573722862076301)
            ·
              refine ⟨1994355819215146073278613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5318282184573722862076301 1994355819215146073278613)
              ·
                refine ⟨93485429025709972184935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1994355819215146073278613 93485429025709972184935)
                ·
                  rfl

theorem cell20_614460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 3, 6].length) (baseStart_614460 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_614460 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_614460 prefixEnd_614460 := by exact prefixLift 614460
  have htrace : WordTrace (prefixWord ++ tailWord_614460) baseStart_614460 baseEnd_614460 := by
    simpa [prefixWord, tailWord_614460, baseEnd_614460] using wordTrace_append hprefix tailTrace_614460
  have hstable : (prefixWord ++ tailWord_614460).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_614460).length < 2 ^ (prefixWord ++ tailWord_614460).sum := by decide
  have hdescent : baseEnd_614460 < baseStart_614460 := by decide
  rcases family_descends (prefixWord ++ tailWord_614460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_614484 : List Nat := [2, 4, 1, 1, 1, 1, 1, 6, 3]
def baseStart_614484 : Nat := 118140960795 + 614484 * 2 ^ 59
def prefixEnd_614484 : Nat := 4983230072969 + 3 ^ 40 * 614484 * 2
def baseEnd_614484 : Nat := 280467241331092499754707

theorem tailTrace_614484 : CollatzResearch.WordTrace tailWord_614484 prefixEnd_614484 280467241331092499754707 := by
  unfold tailWord_614484
  simp only [CollatzResearch.WordTrace]
  refine ⟨11206036352918444178585253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14941381803891258904780337 11206036352918444178585253)
  ·
    refine ⟨2101131816172208283484735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11206036352918444178585253 2101131816172208283484735)
    ·
      refine ⟨3151697724258312425227103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2101131816172208283484735 3151697724258312425227103)
      ·
        refine ⟨4727546586387468637840655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3151697724258312425227103 4727546586387468637840655)
        ·
          refine ⟨7091319879581202956760983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4727546586387468637840655 7091319879581202956760983)
          ·
            refine ⟨10636979819371804435141475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7091319879581202956760983 10636979819371804435141475)
            ·
              refine ⟨15955469729057706652712213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10636979819371804435141475 15955469729057706652712213)
              ·
                refine ⟨747912643549579999345885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 15955469729057706652712213 747912643549579999345885)
                ·
                  refine ⟨280467241331092499754707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 747912643549579999345885 280467241331092499754707)
                  ·
                    rfl

theorem cell20_614484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 6, 3].length) (baseStart_614484 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_614484 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_614484 prefixEnd_614484 := by exact prefixLift 614484
  have htrace : WordTrace (prefixWord ++ tailWord_614484) baseStart_614484 baseEnd_614484 := by
    simpa [prefixWord, tailWord_614484, baseEnd_614484] using wordTrace_append hprefix tailTrace_614484
  have hstable : (prefixWord ++ tailWord_614484).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_614484).length < 2 ^ (prefixWord ++ tailWord_614484).sum := by decide
  have hdescent : baseEnd_614484 < baseStart_614484 := by decide
  rcases family_descends (prefixWord ++ tailWord_614484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_614501 : List Nat := [1, 3, 1, 3, 2, 2, 4, 1, 3]
def baseStart_614501 : Nat := 118140960795 + 614501 * 2 ^ 59
def prefixEnd_614501 : Nat := 4983230072969 + 3 ^ 40 * 614501 * 2
def baseEnd_614501 : Nat := 280475000594315996187971

theorem tailTrace_614501 : CollatzResearch.WordTrace tailWord_614501 prefixEnd_614501 280475000594315996187971 := by
  unfold tailWord_614501
  simp only [CollatzResearch.WordTrace]
  refine ⟨22412692746775300260539357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14941795164516866840359571 22412692746775300260539357)
  ·
    refine ⟨8404759780040737597702259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22412692746775300260539357 8404759780040737597702259)
    ·
      refine ⟨12607139670061106396553389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8404759780040737597702259 12607139670061106396553389)
      ·
        refine ⟨4727677376272914898707521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12607139670061106396553389 4727677376272914898707521)
        ·
          refine ⟨3545758032204686174030641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4727677376272914898707521 3545758032204686174030641)
          ·
            refine ⟨2659318524153514630522981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3545758032204686174030641 2659318524153514630522981)
            ·
              refine ⟨498622223278783993223059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2659318524153514630522981 498622223278783993223059)
              ·
                refine ⟨747933334918175989834589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 498622223278783993223059 747933334918175989834589)
                ·
                  refine ⟨280475000594315996187971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 747933334918175989834589 280475000594315996187971)
                  ·
                    rfl

theorem cell20_614501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 4, 1, 3].length) (baseStart_614501 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_614501 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_614501 prefixEnd_614501 := by exact prefixLift 614501
  have htrace : WordTrace (prefixWord ++ tailWord_614501) baseStart_614501 baseEnd_614501 := by
    simpa [prefixWord, tailWord_614501, baseEnd_614501] using wordTrace_append hprefix tailTrace_614501
  have hstable : (prefixWord ++ tailWord_614501).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_614501).length < 2 ^ (prefixWord ++ tailWord_614501).sum := by decide
  have hdescent : baseEnd_614501 < baseStart_614501 := by decide
  rcases family_descends (prefixWord ++ tailWord_614501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_614536 : List Nat := [2, 1, 3, 4, 1, 9]
def baseStart_614536 : Nat := 118140960795 + 614536 * 2 ^ 59
def prefixEnd_614536 : Nat := 4983230072969 + 3 ^ 40 * 614536 * 2
def baseEnd_614536 : Nat := 10388554649926349260043

theorem tailTrace_614536 : CollatzResearch.WordTrace tailWord_614536 prefixEnd_614536 10388554649926349260043 := by
  unfold tailWord_614536
  simp only [CollatzResearch.WordTrace]
  refine ⟨11206984650824250619031731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14942646201099000825375641 11206984650824250619031731)
  ·
    refine ⟨16810476976236375928547597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11206984650824250619031731 16810476976236375928547597)
    ·
      refine ⟨6303928866088640973205349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16810476976236375928547597 6303928866088640973205349)
      ·
        refine ⟨1181986662391620182476003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6303928866088640973205349 1181986662391620182476003)
        ·
          refine ⟨1772979993587430273714005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1181986662391620182476003 1772979993587430273714005)
          ·
            refine ⟨10388554649926349260043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1772979993587430273714005 10388554649926349260043)
            ·
              rfl

theorem cell20_614536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 9].length) (baseStart_614536 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_614536 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_614536 prefixEnd_614536 := by exact prefixLift 614536
  have htrace : WordTrace (prefixWord ++ tailWord_614536) baseStart_614536 baseEnd_614536 := by
    simpa [prefixWord, tailWord_614536, baseEnd_614536] using wordTrace_append hprefix tailTrace_614536
  have hstable : (prefixWord ++ tailWord_614536).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_614536).length < 2 ^ (prefixWord ++ tailWord_614536).sum := by decide
  have hdescent : baseEnd_614536 < baseStart_614536 := by decide
  rcases family_descends (prefixWord ++ tailWord_614536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_614560 : List Nat := [2, 1, 1, 4, 2, 2, 2, 3, 3]
def baseStart_614560 : Nat := 118140960795 + 614560 * 2 ^ 59
def prefixEnd_614560 : Nat := 4983230072969 + 3 ^ 40 * 614560 * 2
def baseEnd_614560 : Nat := 280501929801974013221063

theorem tailTrace_614560 : CollatzResearch.WordTrace tailWord_614560 prefixEnd_614560 280501929801974013221063 := by
  unfold tailWord_614560
  simp only [CollatzResearch.WordTrace]
  refine ⟨11207422326780776668468567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14943229769041035557958089 11207422326780776668468567)
  ·
    refine ⟨16811133490171165002702851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11207422326780776668468567 16811133490171165002702851)
    ·
      refine ⟨25216700235256747504054277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16811133490171165002702851 25216700235256747504054277)
      ·
        refine ⟨4728131294110640157010177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 25216700235256747504054277 4728131294110640157010177)
        ·
          refine ⟨3546098470582980117757633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4728131294110640157010177 3546098470582980117757633)
          ·
            refine ⟨2659573852937235088318225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3546098470582980117757633 2659573852937235088318225)
            ·
              refine ⟨1994680389702926316238669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2659573852937235088318225 1994680389702926316238669)
              ·
                refine ⟨748005146138597368589501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1994680389702926316238669 748005146138597368589501)
                ·
                  refine ⟨280501929801974013221063, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 748005146138597368589501 280501929801974013221063)
                  ·
                    rfl

theorem cell20_614560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 2, 3, 3].length) (baseStart_614560 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_614560 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_614560 prefixEnd_614560 := by exact prefixLift 614560
  have htrace : WordTrace (prefixWord ++ tailWord_614560) baseStart_614560 baseEnd_614560 := by
    simpa [prefixWord, tailWord_614560, baseEnd_614560] using wordTrace_append hprefix tailTrace_614560
  have hstable : (prefixWord ++ tailWord_614560).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_614560).length < 2 ^ (prefixWord ++ tailWord_614560).sum := by decide
  have hdescent : baseEnd_614560 < baseStart_614560 := by decide
  rcases family_descends (prefixWord ++ tailWord_614560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_614584 : List Nat := [2, 1, 2, 1, 2, 1, 6, 3, 2]
def baseStart_614584 : Nat := 118140960795 + 614584 * 2 ^ 59
def prefixEnd_614584 : Nat := 4983230072969 + 3 ^ 40 * 614584 * 2
def baseEnd_614584 : Nat := 280512884055936596420965

theorem tailTrace_614584 : CollatzResearch.WordTrace tailWord_614584 prefixEnd_614584 280512884055936596420965 := by
  unfold tailWord_614584
  simp only [CollatzResearch.WordTrace]
  refine ⟨11207860002737302717905403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14943813336983070290540537 11207860002737302717905403)
  ·
    refine ⟨16811790004105954076858105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11207860002737302717905403 16811790004105954076858105)
    ·
      refine ⟨12608842503079465557643579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16811790004105954076858105 12608842503079465557643579)
      ·
        refine ⟨18913263754619198336465369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12608842503079465557643579 18913263754619198336465369)
        ·
          refine ⟨14184947815964398752349027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18913263754619198336465369 14184947815964398752349027)
          ·
            refine ⟨21277421723946598128523541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14184947815964398752349027 21277421723946598128523541)
            ·
              refine ⟨997379143309996787274541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 21277421723946598128523541 997379143309996787274541)
              ·
                refine ⟨374017178741248795227953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 997379143309996787274541 374017178741248795227953)
                ·
                  refine ⟨280512884055936596420965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 374017178741248795227953 280512884055936596420965)
                  ·
                    rfl

theorem cell20_614584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 6, 3, 2].length) (baseStart_614584 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_614584 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_614584 prefixEnd_614584 := by exact prefixLift 614584
  have htrace : WordTrace (prefixWord ++ tailWord_614584) baseStart_614584 baseEnd_614584 := by
    simpa [prefixWord, tailWord_614584, baseEnd_614584] using wordTrace_append hprefix tailTrace_614584
  have hstable : (prefixWord ++ tailWord_614584).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_614584).length < 2 ^ (prefixWord ++ tailWord_614584).sum := by decide
  have hdescent : baseEnd_614584 < baseStart_614584 := by decide
  rcases family_descends (prefixWord ++ tailWord_614584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_614594 : List Nat := [3, 5, 1, 1, 1, 2, 1, 1, 5]
def baseStart_614594 : Nat := 118140960795 + 614594 * 2 ^ 59
def prefixEnd_614594 : Nat := 4983230072969 + 3 ^ 40 * 614594 * 2
def baseEnd_614594 : Nat := 280517448328421006087591

theorem tailTrace_614594 : CollatzResearch.WordTrace tailWord_614594 prefixEnd_614594 280517448328421006087591 := by
  unfold tailWord_614594
  simp only [CollatzResearch.WordTrace]
  refine ⟨5604021183859594285918709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14944056490292251429116557 5604021183859594285918709)
  ·
    refine ⟨525376985986836964304879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 5604021183859594285918709 525376985986836964304879)
    ·
      refine ⟨788065478980255446457319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 525376985986836964304879 788065478980255446457319)
      ·
        refine ⟨1182098218470383169685979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 788065478980255446457319 1182098218470383169685979)
        ·
          refine ⟨1773147327705574754528969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1182098218470383169685979 1773147327705574754528969)
          ·
            refine ⟨1329860495779181065896727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1773147327705574754528969 1329860495779181065896727)
            ·
              refine ⟨1994790743668771598845091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1329860495779181065896727 1994790743668771598845091)
              ·
                refine ⟨2992186115503157398267637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1994790743668771598845091 2992186115503157398267637)
                ·
                  refine ⟨280517448328421006087591, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2992186115503157398267637 280517448328421006087591)
                  ·
                    rfl

theorem cell20_614594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 2, 1, 1, 5].length) (baseStart_614594 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_614594 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_614594 prefixEnd_614594 := by exact prefixLift 614594
  have htrace : WordTrace (prefixWord ++ tailWord_614594) baseStart_614594 baseEnd_614594 := by
    simpa [prefixWord, tailWord_614594, baseEnd_614594] using wordTrace_append hprefix tailTrace_614594
  have hstable : (prefixWord ++ tailWord_614594).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_614594).length < 2 ^ (prefixWord ++ tailWord_614594).sum := by decide
  have hdescent : baseEnd_614594 < baseStart_614594 := by decide
  rcases family_descends (prefixWord ++ tailWord_614594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_614629 : List Nat := [1, 3, 1, 4, 2, 1, 4, 4]
def baseStart_614629 : Nat := 118140960795 + 614629 * 2 ^ 59
def prefixEnd_614629 : Nat := 4983230072969 + 3 ^ 40 * 614629 * 2
def baseEnd_614629 : Nat := 93511141094038813306927

theorem tailTrace_614629 : CollatzResearch.WordTrace tailWord_614629 prefixEnd_614629 93511141094038813306927 := by
  unfold tailWord_614629
  simp only [CollatzResearch.WordTrace]
  refine ⟨22417361290311578121198941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14944907526874385414132627 22417361290311578121198941)
  ·
    refine ⟨8406510483866841795449603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22417361290311578121198941 8406510483866841795449603)
    ·
      refine ⟨12609765725800262693174405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8406510483866841795449603 12609765725800262693174405)
      ·
        refine ⟨2364331073587549254970201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12609765725800262693174405 2364331073587549254970201)
        ·
          refine ⟨1773248305190661941227651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2364331073587549254970201 1773248305190661941227651)
          ·
            refine ⟨2659872457785992911841477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1773248305190661941227651 2659872457785992911841477)
            ·
              refine ⟨498726085834873670970277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2659872457785992911841477 498726085834873670970277)
              ·
                refine ⟨93511141094038813306927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 498726085834873670970277 93511141094038813306927)
                ·
                  rfl

theorem cell20_614629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 4, 4].length) (baseStart_614629 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_614629 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_614629 prefixEnd_614629 := by exact prefixLift 614629
  have htrace : WordTrace (prefixWord ++ tailWord_614629) baseStart_614629 baseEnd_614629 := by
    simpa [prefixWord, tailWord_614629, baseEnd_614629] using wordTrace_append hprefix tailTrace_614629
  have hstable : (prefixWord ++ tailWord_614629).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_614629).length < 2 ^ (prefixWord ++ tailWord_614629).sum := by decide
  have hdescent : baseEnd_614629 < baseStart_614629 := by decide
  rcases family_descends (prefixWord ++ tailWord_614629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_614633 : List Nat := [1, 2, 1, 1, 1, 2, 2, 10]
def baseStart_614633 : Nat := 118140960795 + 614633 * 2 ^ 59
def prefixEnd_614633 : Nat := 4983230072969 + 3 ^ 40 * 614633 * 2
def baseEnd_614633 : Nat := 93511749663703401262477

theorem tailTrace_614633 : CollatzResearch.WordTrace tailWord_614633 prefixEnd_614633 93511749663703401262477 := by
  unfold tailWord_614633
  simp only [CollatzResearch.WordTrace]
  refine ⟨22417507182297086804344553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14945004788198057869563035 22417507182297086804344553)
  ·
    refine ⟨16813130386722815103258415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22417507182297086804344553 16813130386722815103258415)
    ·
      refine ⟨25219695580084222654887623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16813130386722815103258415 25219695580084222654887623)
      ·
        refine ⟨37829543370126333982331435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25219695580084222654887623 37829543370126333982331435)
        ·
          refine ⟨56744315055189500973497153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37829543370126333982331435 56744315055189500973497153)
          ·
            refine ⟨42558236291392125730122865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56744315055189500973497153 42558236291392125730122865)
            ·
              refine ⟨31918677218544094297592149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42558236291392125730122865 31918677218544094297592149)
              ·
                refine ⟨93511749663703401262477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 31918677218544094297592149 93511749663703401262477)
                ·
                  rfl

theorem cell20_614633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 10].length) (baseStart_614633 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_614633 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_614633 prefixEnd_614633 := by exact prefixLift 614633
  have htrace : WordTrace (prefixWord ++ tailWord_614633) baseStart_614633 baseEnd_614633 := by
    simpa [prefixWord, tailWord_614633, baseEnd_614633] using wordTrace_append hprefix tailTrace_614633
  have hstable : (prefixWord ++ tailWord_614633).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_614633).length < 2 ^ (prefixWord ++ tailWord_614633).sum := by decide
  have hdescent : baseEnd_614633 < baseStart_614633 := by decide
  rcases family_descends (prefixWord ++ tailWord_614633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_614639 : List Nat := [1, 1, 2, 1, 6, 3, 1, 3, 2]
def baseStart_614639 : Nat := 118140960795 + 614639 * 2 ^ 59
def prefixEnd_614639 : Nat := 4983230072969 + 3 ^ 40 * 614639 * 2
def baseEnd_614639 : Nat := 280537987554600849587407

theorem tailTrace_614639 : CollatzResearch.WordTrace tailWord_614639 prefixEnd_614639 280537987554600849587407 := by
  unfold tailWord_614639
  simp only [CollatzResearch.WordTrace]
  refine ⟨22417726020275349829062971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14945150680183566552708647 22417726020275349829062971)
  ·
    refine ⟨33626589030413024743594457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22417726020275349829062971 33626589030413024743594457)
    ·
      refine ⟨25219941772809768557695843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33626589030413024743594457 25219941772809768557695843)
      ·
        refine ⟨37829912659214652836543765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25219941772809768557695843 37829912659214652836543765)
        ·
          refine ⟨1773277155900686851712989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 37829912659214652836543765 1773277155900686851712989)
          ·
            refine ⟨664978933462757569392371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1773277155900686851712989 664978933462757569392371)
            ·
              refine ⟨997468400194136354088557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 664978933462757569392371 997468400194136354088557)
              ·
                refine ⟨374050650072801132783209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 997468400194136354088557 374050650072801132783209)
                ·
                  refine ⟨280537987554600849587407, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 374050650072801132783209 280537987554600849587407)
                  ·
                    rfl

theorem cell20_614639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 3, 1, 3, 2].length) (baseStart_614639 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_614639 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_614639 prefixEnd_614639 := by exact prefixLift 614639
  have htrace : WordTrace (prefixWord ++ tailWord_614639) baseStart_614639 baseEnd_614639 := by
    simpa [prefixWord, tailWord_614639, baseEnd_614639] using wordTrace_append hprefix tailTrace_614639
  have hstable : (prefixWord ++ tailWord_614639).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_614639).length < 2 ^ (prefixWord ++ tailWord_614639).sum := by decide
  have hdescent : baseEnd_614639 < baseStart_614639 := by decide
  rcases family_descends (prefixWord ++ tailWord_614639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_614650 : List Nat := [3, 1, 1, 1, 1, 7, 6]
def baseStart_614650 : Nat := 118140960795 + 614650 * 2 ^ 59
def prefixEnd_614650 : Nat := 4983230072969 + 3 ^ 40 * 614650 * 2
def baseEnd_614650 : Nat := 31171445361592633357855

theorem tailTrace_614650 : CollatzResearch.WordTrace tailWord_614650 prefixEnd_614650 31171445361592633357855 := by
  unfold tailWord_614650
  simp only [CollatzResearch.WordTrace]
  refine ⟨5604531805808874676928351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14945418148823665805142269 5604531805808874676928351)
  ·
    refine ⟨8406797708713312015392527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5604531805808874676928351 8406797708713312015392527)
    ·
      refine ⟨12610196563069968023088791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8406797708713312015392527 12610196563069968023088791)
      ·
        refine ⟨18915294844604952034633187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12610196563069968023088791 18915294844604952034633187)
        ·
          refine ⟨28372942266907428051949781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18915294844604952034633187 28372942266907428051949781)
          ·
            refine ⟨664990834380642844967573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 28372942266907428051949781 664990834380642844967573)
            ·
              refine ⟨31171445361592633357855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 664990834380642844967573 31171445361592633357855)
              ·
                rfl

theorem cell20_614650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 7, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 7, 6].length) (baseStart_614650 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_614650 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_614650 prefixEnd_614650 := by exact prefixLift 614650
  have htrace : WordTrace (prefixWord ++ tailWord_614650) baseStart_614650 baseEnd_614650 := by
    simpa [prefixWord, tailWord_614650, baseEnd_614650] using wordTrace_append hprefix tailTrace_614650
  have hstable : (prefixWord ++ tailWord_614650).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_614650).length < 2 ^ (prefixWord ++ tailWord_614650).sum := by decide
  have hdescent : baseEnd_614650 < baseStart_614650 := by decide
  rcases family_descends (prefixWord ++ tailWord_614650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_614657 : List Nat := [1, 2, 4, 1, 1, 2, 1, 3, 5]
def baseStart_614657 : Nat := 118140960795 + 614657 * 2 ^ 59
def prefixEnd_614657 : Nat := 4983230072969 + 3 ^ 40 * 614657 * 2
def baseEnd_614657 : Nat := 280546203245072786987333

theorem tailTrace_614657 : CollatzResearch.WordTrace tailWord_614657 prefixEnd_614657 280546203245072786987333 := by
  unfold tailWord_614657
  simp only [CollatzResearch.WordTrace]
  refine ⟨22418382534210138903218225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14945588356140092602145483 22418382534210138903218225)
  ·
    refine ⟨16813786900657604177413669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22418382534210138903218225 16813786900657604177413669)
    ·
      refine ⟨3152585043873300783265063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16813786900657604177413669 3152585043873300783265063)
      ·
        refine ⟨4728877565809951174897595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3152585043873300783265063 4728877565809951174897595)
        ·
          refine ⟨7093316348714926762346393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4728877565809951174897595 7093316348714926762346393)
          ·
            refine ⟨5319987261536195071759795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7093316348714926762346393 5319987261536195071759795)
            ·
              refine ⟨7979980892304292607639693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5319987261536195071759795 7979980892304292607639693)
              ·
                refine ⟨2992492834614109727864885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7979980892304292607639693 2992492834614109727864885)
                ·
                  refine ⟨280546203245072786987333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2992492834614109727864885 280546203245072786987333)
                  ·
                    rfl

theorem cell20_614657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 1, 3, 5].length) (baseStart_614657 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_614657 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_614657 prefixEnd_614657 := by exact prefixLift 614657
  have htrace : WordTrace (prefixWord ++ tailWord_614657) baseStart_614657 baseEnd_614657 := by
    simpa [prefixWord, tailWord_614657, baseEnd_614657] using wordTrace_append hprefix tailTrace_614657
  have hstable : (prefixWord ++ tailWord_614657).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_614657).length < 2 ^ (prefixWord ++ tailWord_614657).sum := by decide
  have hdescent : baseEnd_614657 < baseStart_614657 := by decide
  rcases family_descends (prefixWord ++ tailWord_614657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_614688 : List Nat := [2, 1, 1, 5, 2, 1, 2, 6]
def baseStart_614688 : Nat := 118140960795 + 614688 * 2 ^ 59
def prefixEnd_614688 : Nat := 4983230072969 + 3 ^ 40 * 614688 * 2
def baseEnd_614688 : Nat := 93520117496591485651291

theorem tailTrace_614688 : CollatzResearch.WordTrace tailWord_614688 prefixEnd_614688 93520117496591485651291 := by
  unfold tailWord_614688
  simp only [CollatzResearch.WordTrace]
  refine ⟨11209756598548915598798359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14946342131398554131731145 11209756598548915598798359)
  ·
    refine ⟨16814634897823373398197539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11209756598548915598798359 16814634897823373398197539)
    ·
      refine ⟨25221952346735060097296309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16814634897823373398197539 25221952346735060097296309)
      ·
        refine ⟨2364558032506411884121529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 25221952346735060097296309 2364558032506411884121529)
        ·
          refine ⟨1773418524379808913091147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2364558032506411884121529 1773418524379808913091147)
          ·
            refine ⟨2660127786569713369636721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1773418524379808913091147 2660127786569713369636721)
            ·
              refine ⟨1995095839927285027227541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2660127786569713369636721 1995095839927285027227541)
              ·
                refine ⟨93520117496591485651291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1995095839927285027227541 93520117496591485651291)
                ·
                  rfl

theorem cell20_614688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 2, 6].length) (baseStart_614688 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_614688 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_614688 prefixEnd_614688 := by exact prefixLift 614688
  have htrace : WordTrace (prefixWord ++ tailWord_614688) baseStart_614688 baseEnd_614688 := by
    simpa [prefixWord, tailWord_614688, baseEnd_614688] using wordTrace_append hprefix tailTrace_614688
  have hstable : (prefixWord ++ tailWord_614688).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_614688).length < 2 ^ (prefixWord ++ tailWord_614688).sum := by decide
  have hdescent : baseEnd_614688 < baseStart_614688 := by decide
  rcases family_descends (prefixWord ++ tailWord_614688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_614764 : List Nat := [2, 2, 1, 1, 6, 1, 7]
def baseStart_614764 : Nat := 118140960795 + 614764 * 2 ^ 59
def prefixEnd_614764 : Nat := 4983230072969 + 3 ^ 40 * 614764 * 2
def baseEnd_614764 : Nat := 31177226773406218935581

theorem tailTrace_614764 : CollatzResearch.WordTrace tailWord_614764 prefixEnd_614764 31177226773406218935581 := by
  unfold tailWord_614764
  simp only [CollatzResearch.WordTrace]
  refine ⟨11211142572411248088681673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14948190096548330784908897 11211142572411248088681673)
  ·
    refine ⟨8408356929308436066511255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11211142572411248088681673 8408356929308436066511255)
    ·
      refine ⟨12612535393962654099766883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8408356929308436066511255 12612535393962654099766883)
      ·
        refine ⟨18918803090943981149650325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12612535393962654099766883 18918803090943981149650325)
        ·
          refine ⟨886818894887999116389859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 18918803090943981149650325 886818894887999116389859)
          ·
            refine ⟨1330228342331998674584789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 886818894887999116389859 1330228342331998674584789)
            ·
              refine ⟨31177226773406218935581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1330228342331998674584789 31177226773406218935581)
              ·
                rfl

theorem cell20_614764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 1, 7].length) (baseStart_614764 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_614764 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_614764 prefixEnd_614764 := by exact prefixLift 614764
  have htrace : WordTrace (prefixWord ++ tailWord_614764) baseStart_614764 baseEnd_614764 := by
    simpa [prefixWord, tailWord_614764, baseEnd_614764] using wordTrace_append hprefix tailTrace_614764
  have hstable : (prefixWord ++ tailWord_614764).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_614764).length < 2 ^ (prefixWord ++ tailWord_614764).sum := by decide
  have hdescent : baseEnd_614764 < baseStart_614764 := by decide
  rcases family_descends (prefixWord ++ tailWord_614764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_614798 : List Nat := [4, 1, 1, 4, 1, 3, 2, 4]
def baseStart_614798 : Nat := 118140960795 + 614798 * 2 ^ 59
def prefixEnd_614798 : Nat := 4983230072969 + 3 ^ 40 * 614798 * 2
def baseEnd_614798 : Nat := 93536853162367654428919

theorem tailTrace_614798 : CollatzResearch.WordTrace tailWord_614798 prefixEnd_614798 93536853162367654428919 := by
  unfold tailWord_614798
  simp only [CollatzResearch.WordTrace]
  refine ⟨2802940653337414998012631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14949016817799546656067365 2802940653337414998012631)
  ·
    refine ⟨4204410980006122497018947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2802940653337414998012631 4204410980006122497018947)
    ·
      refine ⟨6306616470009183745528421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4204410980006122497018947 6306616470009183745528421)
      ·
        refine ⟨1182490588126721952286579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6306616470009183745528421 1182490588126721952286579)
        ·
          refine ⟨1773735882190082928429869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1182490588126721952286579 1773735882190082928429869)
          ·
            refine ⟨665150955821281098161201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1773735882190082928429869 665150955821281098161201)
            ·
              refine ⟨498863216865960823620901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 665150955821281098161201 498863216865960823620901)
              ·
                refine ⟨93536853162367654428919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 498863216865960823620901 93536853162367654428919)
                ·
                  rfl

theorem cell20_614798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 3, 2, 4].length) (baseStart_614798 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_614798 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_614798 prefixEnd_614798 := by exact prefixLift 614798
  have htrace : WordTrace (prefixWord ++ tailWord_614798) baseStart_614798 baseEnd_614798 := by
    simpa [prefixWord, tailWord_614798, baseEnd_614798] using wordTrace_append hprefix tailTrace_614798
  have hstable : (prefixWord ++ tailWord_614798).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_614798).length < 2 ^ (prefixWord ++ tailWord_614798).sum := by decide
  have hdescent : baseEnd_614798 < baseStart_614798 := by decide
  rcases family_descends (prefixWord ++ tailWord_614798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_614829 : List Nat := [1, 5, 2, 2, 2, 2, 1, 1, 4]
def baseStart_614829 : Nat := 118140960795 + 614829 * 2 ^ 59
def prefixEnd_614829 : Nat := 4983230072969 + 3 ^ 40 * 614829 * 2
def baseEnd_614829 : Nat := 280624708731804633253297

theorem tailTrace_614829 : CollatzResearch.WordTrace tailWord_614829 prefixEnd_614829 280624708731804633253297 := by
  unfold tailWord_614829
  simp only [CollatzResearch.WordTrace]
  refine ⟨22424655889587012278479541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14949770593058008185653027 22424655889587012278479541)
  ·
    refine ⟨2102311489648782401107457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 22424655889587012278479541 2102311489648782401107457)
    ·
      refine ⟨1576733617236586800830593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2102311489648782401107457 1576733617236586800830593)
      ·
        refine ⟨1182550212927440100622945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1576733617236586800830593 1182550212927440100622945)
        ·
          refine ⟨886912659695580075467209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1182550212927440100622945 886912659695580075467209)
          ·
            refine ⟨665184494771685056600407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 886912659695580075467209 665184494771685056600407)
            ·
              refine ⟨997776742157527584900611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 665184494771685056600407 997776742157527584900611)
              ·
                refine ⟨1496665113236291377350917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 997776742157527584900611 1496665113236291377350917)
                ·
                  refine ⟨280624708731804633253297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1496665113236291377350917 280624708731804633253297)
                  ·
                    rfl

theorem cell20_614829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 2, 1, 1, 4].length) (baseStart_614829 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_614829 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_614829 prefixEnd_614829 := by exact prefixLift 614829
  have htrace : WordTrace (prefixWord ++ tailWord_614829) baseStart_614829 baseEnd_614829 := by
    simpa [prefixWord, tailWord_614829, baseEnd_614829] using wordTrace_append hprefix tailTrace_614829
  have hstable : (prefixWord ++ tailWord_614829).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_614829).length < 2 ^ (prefixWord ++ tailWord_614829).sum := by decide
  have hdescent : baseEnd_614829 < baseStart_614829 := by decide
  rcases family_descends (prefixWord ++ tailWord_614829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_614833 : List Nat := [1, 2, 2, 4, 1, 2, 3, 1, 4]
def baseStart_614833 : Nat := 118140960795 + 614833 * 2 ^ 59
def prefixEnd_614833 : Nat := 4983230072969 + 3 ^ 40 * 614833 * 2
def baseEnd_614833 : Nat := 280626534440798397119947

theorem tailTrace_614833 : CollatzResearch.WordTrace tailWord_614833 prefixEnd_614833 280626534440798397119947 := by
  unfold tailWord_614833
  simp only [CollatzResearch.WordTrace]
  refine ⟨22424801781572520961625153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14949867854381680641083435 22424801781572520961625153)
  ·
    refine ⟨16818601336179390721218865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22424801781572520961625153 16818601336179390721218865)
    ·
      refine ⟨12613951002134543040914149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16818601336179390721218865 12613951002134543040914149)
      ·
        refine ⟨2365115812900226820171403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12613951002134543040914149 2365115812900226820171403)
        ·
          refine ⟨3547673719350340230257105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2365115812900226820171403 3547673719350340230257105)
          ·
            refine ⟨2660755289512755172692829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3547673719350340230257105 2660755289512755172692829)
            ·
              refine ⟨997783233567283189759811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2660755289512755172692829 997783233567283189759811)
              ·
                refine ⟨1496674850350924784639717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 997783233567283189759811 1496674850350924784639717)
                ·
                  refine ⟨280626534440798397119947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1496674850350924784639717 280626534440798397119947)
                  ·
                    rfl

theorem cell20_614833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 3, 1, 4].length) (baseStart_614833 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_614833 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_614833 prefixEnd_614833 := by exact prefixLift 614833
  have htrace : WordTrace (prefixWord ++ tailWord_614833) baseStart_614833 baseEnd_614833 := by
    simpa [prefixWord, tailWord_614833, baseEnd_614833] using wordTrace_append hprefix tailTrace_614833
  have hstable : (prefixWord ++ tailWord_614833).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_614833).length < 2 ^ (prefixWord ++ tailWord_614833).sum := by decide
  have hdescent : baseEnd_614833 < baseStart_614833 := by decide
  rcases family_descends (prefixWord ++ tailWord_614833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_614888 : List Nat := [2, 1, 4, 1, 1, 4, 1, 4, 2]
def baseStart_614888 : Nat := 118140960795 + 614888 * 2 ^ 59
def prefixEnd_614888 : Nat := 4983230072969 + 3 ^ 40 * 614888 * 2
def baseEnd_614888 : Nat := 280651637939462650286389

theorem tailTrace_614888 : CollatzResearch.WordTrace tailWord_614888 prefixEnd_614888 280651637939462650286389 := by
  unfold tailWord_614888
  simp only [CollatzResearch.WordTrace]
  refine ⟨11213403898186632677438659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14951205197582176903251545 11213403898186632677438659)
  ·
    refine ⟨16820105847279949016157989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11213403898186632677438659 16820105847279949016157989)
    ·
      refine ⟨3153769846364990440529623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16820105847279949016157989 3153769846364990440529623)
      ·
        refine ⟨4730654769547485660794435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3153769846364990440529623 4730654769547485660794435)
        ·
          refine ⟨7095982154321228491191653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4730654769547485660794435 7095982154321228491191653)
          ·
            refine ⟨1330496653935230342098435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7095982154321228491191653 1330496653935230342098435)
            ·
              refine ⟨1995744980902845513147653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1330496653935230342098435 1995744980902845513147653)
              ·
                refine ⟨374202183919283533715185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1995744980902845513147653 374202183919283533715185)
                ·
                  refine ⟨280651637939462650286389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 374202183919283533715185 280651637939462650286389)
                  ·
                    rfl

theorem cell20_614888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 4, 1, 4, 2].length) (baseStart_614888 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_614888 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_614888 prefixEnd_614888 := by exact prefixLift 614888
  have htrace : WordTrace (prefixWord ++ tailWord_614888) baseStart_614888 baseEnd_614888 := by
    simpa [prefixWord, tailWord_614888, baseEnd_614888] using wordTrace_append hprefix tailTrace_614888
  have hstable : (prefixWord ++ tailWord_614888).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_614888).length < 2 ^ (prefixWord ++ tailWord_614888).sum := by decide
  have hdescent : baseEnd_614888 < baseStart_614888 := by decide
  rcases family_descends (prefixWord ++ tailWord_614888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_614892 : List Nat := [2, 2, 1, 1, 2, 1, 4, 3, 4]
def baseStart_614892 : Nat := 118140960795 + 614892 * 2 ^ 59
def prefixEnd_614892 : Nat := 4983230072969 + 3 ^ 40 * 614892 * 2
def baseEnd_614892 : Nat := 280653463648456414153039

theorem tailTrace_614892 : CollatzResearch.WordTrace tailWord_614892 prefixEnd_614892 280653463648456414153039 := by
  unfold tailWord_614892
  simp only [CollatzResearch.WordTrace]
  refine ⟨11213476844179387019011465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14951302458905849358681953 11213476844179387019011465)
  ·
    refine ⟨8410107633134540264258599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11213476844179387019011465 8410107633134540264258599)
    ·
      refine ⟨12615161449701810396387899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8410107633134540264258599 12615161449701810396387899)
      ·
        refine ⟨18922742174552715594581849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12615161449701810396387899 18922742174552715594581849)
        ·
          refine ⟨14192056630914536695936387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18922742174552715594581849 14192056630914536695936387)
          ·
            refine ⟨21288084946371805043904581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14192056630914536695936387 21288084946371805043904581)
            ·
              refine ⟨3991515927444713445732109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21288084946371805043904581 3991515927444713445732109)
              ·
                refine ⟨1496818472791767542149541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3991515927444713445732109 1496818472791767542149541)
                ·
                  refine ⟨280653463648456414153039, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1496818472791767542149541 280653463648456414153039)
                  ·
                    rfl

theorem cell20_614892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 4].length) (baseStart_614892 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_614892 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_614892 prefixEnd_614892 := by exact prefixLift 614892
  have htrace : WordTrace (prefixWord ++ tailWord_614892) baseStart_614892 baseEnd_614892 := by
    simpa [prefixWord, tailWord_614892, baseEnd_614892] using wordTrace_append hprefix tailTrace_614892
  have hstable : (prefixWord ++ tailWord_614892).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_614892).length < 2 ^ (prefixWord ++ tailWord_614892).sum := by decide
  have hdescent : baseEnd_614892 < baseStart_614892 := by decide
  rcases family_descends (prefixWord ++ tailWord_614892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_614902 : List Nat := [5, 1, 1, 1, 2, 1, 1, 5, 3]
def baseStart_614902 : Nat := 118140960795 + 614902 * 2 ^ 59
def prefixEnd_614902 : Nat := 4983230072969 + 3 ^ 40 * 614902 * 2
def baseEnd_614902 : Nat := 280658027920940823819665

theorem tailTrace_614902 : CollatzResearch.WordTrace tailWord_614902 prefixEnd_614902 280658027920940823819665 := by
  unfold tailWord_614902
  simp only [CollatzResearch.WordTrace]
  refine ⟨1401707401145159109117935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 14951545612215030497257973 1401707401145159109117935)
  ·
    refine ⟨2102561101717738663676903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1401707401145159109117935 2102561101717738663676903)
    ·
      refine ⟨3153841652576607995515355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2102561101717738663676903 3153841652576607995515355)
      ·
        refine ⟨4730762478864911993273033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3153841652576607995515355 4730762478864911993273033)
        ·
          refine ⟨3548071859148683994954775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4730762478864911993273033 3548071859148683994954775)
          ·
            refine ⟨5322107788723025992432163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3548071859148683994954775 5322107788723025992432163)
            ·
              refine ⟨7983161683084538988648245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5322107788723025992432163 7983161683084538988648245)
              ·
                refine ⟨748421407789175530185773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7983161683084538988648245 748421407789175530185773)
                ·
                  refine ⟨280658027920940823819665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 748421407789175530185773 280658027920940823819665)
                  ·
                    rfl

theorem cell20_614902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 1, 5, 3].length) (baseStart_614902 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_614902 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_614902 prefixEnd_614902 := by exact prefixLift 614902
  have htrace : WordTrace (prefixWord ++ tailWord_614902) baseStart_614902 baseEnd_614902 := by
    simpa [prefixWord, tailWord_614902, baseEnd_614902] using wordTrace_append hprefix tailTrace_614902
  have hstable : (prefixWord ++ tailWord_614902).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_614902).length < 2 ^ (prefixWord ++ tailWord_614902).sum := by decide
  have hdescent : baseEnd_614902 < baseStart_614902 := by decide
  rcases family_descends (prefixWord ++ tailWord_614902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_614926 : List Nat := [4, 1, 1, 2, 3, 1, 1, 5, 2]
def baseStart_614926 : Nat := 118140960795 + 614926 * 2 ^ 59
def prefixEnd_614926 : Nat := 4983230072969 + 3 ^ 40 * 614926 * 2
def baseEnd_614926 : Nat := 280668982174903407019567

theorem tailTrace_614926 : CollatzResearch.WordTrace tailWord_614926 prefixEnd_614926 280668982174903407019567 := by
  unfold tailWord_614926
  simp only [CollatzResearch.WordTrace]
  refine ⟨2803524221279449730595079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14952129180157065229840421 2803524221279449730595079)
  ·
    refine ⟨4205286331919174595892619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2803524221279449730595079 4205286331919174595892619)
    ·
      refine ⟨6307929497878761893838929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4205286331919174595892619 6307929497878761893838929)
      ·
        refine ⟨4730947123409071420379197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6307929497878761893838929 4730947123409071420379197)
        ·
          refine ⟨1774105171278401782642199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4730947123409071420379197 1774105171278401782642199)
          ·
            refine ⟨2661157756917602673963299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1774105171278401782642199 2661157756917602673963299)
            ·
              refine ⟨3991736635376404010944949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2661157756917602673963299 3991736635376404010944949)
              ·
                refine ⟨374225309566537876026089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3991736635376404010944949 374225309566537876026089)
                ·
                  refine ⟨280668982174903407019567, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 374225309566537876026089 280668982174903407019567)
                  ·
                    rfl

theorem cell20_614926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 1, 5, 2].length) (baseStart_614926 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_614926 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_614926 prefixEnd_614926 := by exact prefixLift 614926
  have htrace : WordTrace (prefixWord ++ tailWord_614926) baseStart_614926 baseEnd_614926 := by
    simpa [prefixWord, tailWord_614926, baseEnd_614926] using wordTrace_append hprefix tailTrace_614926
  have hstable : (prefixWord ++ tailWord_614926).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_614926).length < 2 ^ (prefixWord ++ tailWord_614926).sum := by decide
  have hdescent : baseEnd_614926 < baseStart_614926 := by decide
  rcases family_descends (prefixWord ++ tailWord_614926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_614940 : List Nat := [2, 2, 3, 1, 2, 2, 3, 2, 3]
def baseStart_614940 : Nat := 118140960795 + 614940 * 2 ^ 59
def prefixEnd_614940 : Nat := 4983230072969 + 3 ^ 40 * 614940 * 2
def baseEnd_614940 : Nat := 280675372156381580552843

theorem tailTrace_614940 : CollatzResearch.WordTrace tailWord_614940 prefixEnd_614940 280675372156381580552843 := by
  unfold tailWord_614940
  simp only [CollatzResearch.WordTrace]
  refine ⟨11214352196092439117885137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14952469594789918823846849 11214352196092439117885137)
  ·
    refine ⟨8410764147069329338413853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11214352196092439117885137 8410764147069329338413853)
    ·
      refine ⟨3154036555150998501905195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8410764147069329338413853 3154036555150998501905195)
      ·
        refine ⟨4731054832726497752857793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3154036555150998501905195 4731054832726497752857793)
        ·
          refine ⟨3548291124544873314643345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4731054832726497752857793 3548291124544873314643345)
          ·
            refine ⟨2661218343408654985982509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3548291124544873314643345 2661218343408654985982509)
            ·
              refine ⟨997956878778245619743441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2661218343408654985982509 997956878778245619743441)
              ·
                refine ⟨748467659083684214807581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 997956878778245619743441 748467659083684214807581)
                ·
                  refine ⟨280675372156381580552843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 748467659083684214807581 280675372156381580552843)
                  ·
                    rfl

theorem cell20_614940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 3, 2, 3].length) (baseStart_614940 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_614940 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_614940 prefixEnd_614940 := by exact prefixLift 614940
  have htrace : WordTrace (prefixWord ++ tailWord_614940) baseStart_614940 baseEnd_614940 := by
    simpa [prefixWord, tailWord_614940, baseEnd_614940] using wordTrace_append hprefix tailTrace_614940
  have hstable : (prefixWord ++ tailWord_614940).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_614940).length < 2 ^ (prefixWord ++ tailWord_614940).sum := by decide
  have hdescent : baseEnd_614940 < baseStart_614940 := by decide
  rcases family_descends (prefixWord ++ tailWord_614940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_614947 : List Nat := [1, 1, 1, 4, 4, 2, 2, 1, 4]
def baseStart_614947 : Nat := 118140960795 + 614947 * 2 ^ 59
def prefixEnd_614947 : Nat := 4983230072969 + 3 ^ 40 * 614947 * 2
def baseEnd_614947 : Nat := 280678567147120667319481

theorem tailTrace_614947 : CollatzResearch.WordTrace tailWord_614947 prefixEnd_614947 280678567147120667319481 := by
  unfold tailWord_614947
  simp only [CollatzResearch.WordTrace]
  refine ⟨22428959703159518431275095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14952639802106345620850063 22428959703159518431275095)
  ·
    refine ⟨33643439554739277646912643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22428959703159518431275095 33643439554739277646912643)
    ·
      refine ⟨50465159332108916470368965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33643439554739277646912643 50465159332108916470368965)
      ·
        refine ⟨9462217374770421838194181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 50465159332108916470368965 9462217374770421838194181)
        ·
          refine ⟨1774165757769454094661409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9462217374770421838194181 1774165757769454094661409)
          ·
            refine ⟨1330624318327090570996057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1774165757769454094661409 1330624318327090570996057)
            ·
              refine ⟨997968238745317928247043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1330624318327090570996057 997968238745317928247043)
              ·
                refine ⟨1496952358117976892370565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 997968238745317928247043 1496952358117976892370565)
                ·
                  refine ⟨280678567147120667319481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1496952358117976892370565 280678567147120667319481)
                  ·
                    rfl

theorem cell20_614947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 2, 2, 1, 4].length) (baseStart_614947 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_614947 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_614947 prefixEnd_614947 := by exact prefixLift 614947
  have htrace : WordTrace (prefixWord ++ tailWord_614947) baseStart_614947 baseEnd_614947 := by
    simpa [prefixWord, tailWord_614947, baseEnd_614947] using wordTrace_append hprefix tailTrace_614947
  have hstable : (prefixWord ++ tailWord_614947).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_614947).length < 2 ^ (prefixWord ++ tailWord_614947).sum := by decide
  have hdescent : baseEnd_614947 < baseStart_614947 := by decide
  rcases family_descends (prefixWord ++ tailWord_614947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_614961 : List Nat := [1, 2, 2, 3, 1, 1, 2, 5, 3]
def baseStart_614961 : Nat := 118140960795 + 614961 * 2 ^ 59
def prefixEnd_614961 : Nat := 4983230072969 + 3 ^ 40 * 614961 * 2
def baseEnd_614961 : Nat := 280684957128598840852757

theorem tailTrace_614961 : CollatzResearch.WordTrace tailWord_614961 prefixEnd_614961 280684957128598840852757 := by
  unfold tailWord_614961
  simp only [CollatzResearch.WordTrace]
  refine ⟨22429470325108798822284737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14952980216739199214856491 22429470325108798822284737)
  ·
    refine ⟨16822102743831599116713553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22429470325108798822284737 16822102743831599116713553)
    ·
      refine ⟨12616577057873699337535165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16822102743831599116713553 12616577057873699337535165)
      ·
        refine ⟨4731216396702637251575687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12616577057873699337535165 4731216396702637251575687)
        ·
          refine ⟨7096824595053955877363531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4731216396702637251575687 7096824595053955877363531)
          ·
            refine ⟨10645236892580933816045297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7096824595053955877363531 10645236892580933816045297)
            ·
              refine ⟨7983927669435700362033973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10645236892580933816045297 7983927669435700362033973)
              ·
                refine ⟨748493219009596908940685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7983927669435700362033973 748493219009596908940685)
                ·
                  refine ⟨280684957128598840852757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 748493219009596908940685 280684957128598840852757)
                  ·
                    rfl

theorem cell20_614961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 2, 5, 3].length) (baseStart_614961 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_614961 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_614961 prefixEnd_614961 := by exact prefixLift 614961
  have htrace : WordTrace (prefixWord ++ tailWord_614961) baseStart_614961 baseEnd_614961 := by
    simpa [prefixWord, tailWord_614961, baseEnd_614961] using wordTrace_append hprefix tailTrace_614961
  have hstable : (prefixWord ++ tailWord_614961).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_614961).length < 2 ^ (prefixWord ++ tailWord_614961).sum := by decide
  have hdescent : baseEnd_614961 < baseStart_614961 := by decide
  rcases family_descends (prefixWord ++ tailWord_614961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_614968 : List Nat := [2, 1, 2, 1, 4, 1, 1, 4, 4]
def baseStart_614968 : Nat := 118140960795 + 614968 * 2 ^ 59
def prefixEnd_614968 : Nat := 4983230072969 + 3 ^ 40 * 614968 * 2
def baseEnd_614968 : Nat := 280688152119337927619395

theorem tailTrace_614968 : CollatzResearch.WordTrace tailWord_614968 prefixEnd_614968 280688152119337927619395 := by
  unfold tailWord_614968
  simp only [CollatzResearch.WordTrace]
  refine ⟨11214862818041719508894779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14953150424055626011859705 11214862818041719508894779)
  ·
    refine ⟨16822294227062579263342169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11214862818041719508894779 16822294227062579263342169)
    ·
      refine ⟨12616720670296934447506627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16822294227062579263342169 12616720670296934447506627)
      ·
        refine ⟨18925081005445401671259941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12616720670296934447506627 18925081005445401671259941)
        ·
          refine ⟨3548452688521012813361239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18925081005445401671259941 3548452688521012813361239)
          ·
            refine ⟨5322679032781519220041859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3548452688521012813361239 5322679032781519220041859)
            ·
              refine ⟨7984018549172278830062789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5322679032781519220041859 7984018549172278830062789)
              ·
                refine ⟨1497003477969802280636773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7984018549172278830062789 1497003477969802280636773)
                ·
                  refine ⟨280688152119337927619395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1497003477969802280636773 280688152119337927619395)
                  ·
                    rfl

theorem cell20_614968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 1, 4, 4].length) (baseStart_614968 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_614968 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_614968 prefixEnd_614968 := by exact prefixLift 614968
  have htrace : WordTrace (prefixWord ++ tailWord_614968) baseStart_614968 baseEnd_614968 := by
    simpa [prefixWord, tailWord_614968, baseEnd_614968] using wordTrace_append hprefix tailTrace_614968
  have hstable : (prefixWord ++ tailWord_614968).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_614968).length < 2 ^ (prefixWord ++ tailWord_614968).sum := by decide
  have hdescent : baseEnd_614968 < baseStart_614968 := by decide
  rcases family_descends (prefixWord ++ tailWord_614968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_614975 : List Nat := [1, 1, 2, 2, 3, 2, 3, 6]
def baseStart_614975 : Nat := 118140960795 + 614975 * 2 ^ 59
def prefixEnd_614975 : Nat := 4983230072969 + 3 ^ 40 * 614975 * 2
def baseEnd_614975 : Nat := 93563782370025671462011

theorem tailTrace_614975 : CollatzResearch.WordTrace tailWord_614975 prefixEnd_614975 93563782370025671462011 := by
  unfold tailWord_614975
  simp only [CollatzResearch.WordTrace]
  refine ⟨22429980947058079213294379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14953320631372052808862919 22429980947058079213294379)
  ·
    refine ⟨33644971420587118819941569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22429980947058079213294379 33644971420587118819941569)
    ·
      refine ⟨25233728565440339114956177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33644971420587118819941569 25233728565440339114956177)
      ·
        refine ⟨18925296424080254336217133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25233728565440339114956177 18925296424080254336217133)
        ·
          refine ⟨7096986159030095376081425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18925296424080254336217133 7096986159030095376081425)
          ·
            refine ⟨5322739619272571532061069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7096986159030095376081425 5322739619272571532061069)
            ·
              refine ⟨1996027357227214324522901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5322739619272571532061069 1996027357227214324522901)
              ·
                refine ⟨93563782370025671462011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1996027357227214324522901 93563782370025671462011)
                ·
                  rfl

theorem cell20_614975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 3, 6].length) (baseStart_614975 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_614975 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_614975 prefixEnd_614975 := by exact prefixLift 614975
  have htrace : WordTrace (prefixWord ++ tailWord_614975) baseStart_614975 baseEnd_614975 := by
    simpa [prefixWord, tailWord_614975, baseEnd_614975] using wordTrace_append hprefix tailTrace_614975
  have hstable : (prefixWord ++ tailWord_614975).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_614975).length < 2 ^ (prefixWord ++ tailWord_614975).sum := by decide
  have hdescent : baseEnd_614975 < baseStart_614975 := by decide
  rcases family_descends (prefixWord ++ tailWord_614975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_614999 : List Nat := [1, 1, 3, 2, 2, 2, 2, 4, 3]
def baseStart_614999 : Nat := 118140960795 + 614999 * 2 ^ 59
def prefixEnd_614999 : Nat := 4983230072969 + 3 ^ 40 * 614999 * 2
def baseEnd_614999 : Nat := 280702301364039597585935

theorem tailTrace_614999 : CollatzResearch.WordTrace tailWord_614999 prefixEnd_614999 280702301364039597585935 := by
  unfold tailWord_614999
  simp only [CollatzResearch.WordTrace]
  refine ⟨22430856298971131312168051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14953904199314087541445367 22430856298971131312168051)
  ·
    refine ⟨33646284448456696968252077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22430856298971131312168051 33646284448456696968252077)
    ·
      refine ⟨12617356668171261363094529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33646284448456696968252077 12617356668171261363094529)
      ·
        refine ⟨9463017501128446022320897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12617356668171261363094529 9463017501128446022320897)
        ·
          refine ⟨7097263125846334516740673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9463017501128446022320897 7097263125846334516740673)
          ·
            refine ⟨5322947344384750887555505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7097263125846334516740673 5322947344384750887555505)
            ·
              refine ⟨3992210508288563165666629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5322947344384750887555505 3992210508288563165666629)
              ·
                refine ⟨748539470304105593562493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3992210508288563165666629 748539470304105593562493)
                ·
                  refine ⟨280702301364039597585935, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 748539470304105593562493 280702301364039597585935)
                  ·
                    rfl

theorem cell20_614999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 2, 4, 3].length) (baseStart_614999 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_614999 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_614999 prefixEnd_614999 := by exact prefixLift 614999
  have htrace : WordTrace (prefixWord ++ tailWord_614999) baseStart_614999 baseEnd_614999 := by
    simpa [prefixWord, tailWord_614999, baseEnd_614999] using wordTrace_append hprefix tailTrace_614999
  have hstable : (prefixWord ++ tailWord_614999).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_614999).length < 2 ^ (prefixWord ++ tailWord_614999).sum := by decide
  have hdescent : baseEnd_614999 < baseStart_614999 := by decide
  rcases family_descends (prefixWord ++ tailWord_614999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_615054 : List Nat := [4, 1, 1, 3, 1, 1, 4, 2, 3]
def baseStart_615054 : Nat := 118140960795 + 615054 * 2 ^ 59
def prefixEnd_615054 : Nat := 4983230072969 + 3 ^ 40 * 615054 * 2
def baseEnd_615054 : Nat := 280727404862703850752377

theorem tailTrace_615054 : CollatzResearch.WordTrace tailWord_615054 prefixEnd_615054 280727404862703850752377 := by
  unfold tailWord_615054
  simp only [CollatzResearch.WordTrace]
  refine ⟨2804107789221484463177527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14955241542514583803613477 2804107789221484463177527)
  ·
    refine ⟨4206161683832226694766291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2804107789221484463177527 4206161683832226694766291)
    ·
      refine ⟨6309242525748340042149437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4206161683832226694766291 6309242525748340042149437)
      ·
        refine ⟨2365965947155627515806039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6309242525748340042149437 2365965947155627515806039)
        ·
          refine ⟨3548948920733441273709059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2365965947155627515806039 3548948920733441273709059)
          ·
            refine ⟨5323423381100161910563589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3548948920733441273709059 5323423381100161910563589)
            ·
              refine ⟨998141883956280358230673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5323423381100161910563589 998141883956280358230673)
              ·
                refine ⟨748606412967210268673005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 998141883956280358230673 748606412967210268673005)
                ·
                  refine ⟨280727404862703850752377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 748606412967210268673005 280727404862703850752377)
                  ·
                    rfl

theorem cell20_615054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 4, 2, 3].length) (baseStart_615054 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_615054 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_615054 prefixEnd_615054 := by exact prefixLift 615054
  have htrace : WordTrace (prefixWord ++ tailWord_615054) baseStart_615054 baseEnd_615054 := by
    simpa [prefixWord, tailWord_615054, baseEnd_615054] using wordTrace_append hprefix tailTrace_615054
  have hstable : (prefixWord ++ tailWord_615054).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_615054).length < 2 ^ (prefixWord ++ tailWord_615054).sum := by decide
  have hdescent : baseEnd_615054 < baseStart_615054 := by decide
  rcases family_descends (prefixWord ++ tailWord_615054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_615068 : List Nat := [2, 2, 3, 2, 2, 1, 3, 5]
def baseStart_615068 : Nat := 118140960795 + 615068 * 2 ^ 59
def prefixEnd_615068 : Nat := 4983230072969 + 3 ^ 40 * 615068 * 2
def baseEnd_615068 : Nat := 93577931614727341428551

theorem tailTrace_615068 : CollatzResearch.WordTrace tailWord_615068 prefixEnd_615068 93577931614727341428551 := by
  unfold tailWord_615068
  simp only [CollatzResearch.WordTrace]
  refine ⟨11216686467860578048214929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14955581957147437397619905 11216686467860578048214929)
  ·
    refine ⟨8412514850895433536161197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11216686467860578048214929 8412514850895433536161197)
    ·
      refine ⟨3154693069085787576060449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8412514850895433536161197 3154693069085787576060449)
      ·
        refine ⟨2366019801814340682045337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3154693069085787576060449 2366019801814340682045337)
        ·
          refine ⟨1774514851360755511534003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2366019801814340682045337 1774514851360755511534003)
          ·
            refine ⟨2661772277041133267301005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1774514851360755511534003 2661772277041133267301005)
            ·
              refine ⟨998164603890424975237877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2661772277041133267301005 998164603890424975237877)
              ·
                refine ⟨93577931614727341428551, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 998164603890424975237877 93577931614727341428551)
                ·
                  rfl

theorem cell20_615068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 3, 5].length) (baseStart_615068 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_615068 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_615068 prefixEnd_615068 := by exact prefixLift 615068
  have htrace : WordTrace (prefixWord ++ tailWord_615068) baseStart_615068 baseEnd_615068 := by
    simpa [prefixWord, tailWord_615068, baseEnd_615068] using wordTrace_append hprefix tailTrace_615068
  have hstable : (prefixWord ++ tailWord_615068).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_615068).length < 2 ^ (prefixWord ++ tailWord_615068).sum := by decide
  have hdescent : baseEnd_615068 < baseStart_615068 := by decide
  rcases family_descends (prefixWord ++ tailWord_615068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_615085 : List Nat := [1, 5, 2, 1, 1, 3, 3, 4]
def baseStart_615085 : Nat := 118140960795 + 615085 * 2 ^ 59
def prefixEnd_615085 : Nat := 4983230072969 + 3 ^ 40 * 615085 * 2
def baseEnd_615085 : Nat := 93580518035801840239639

theorem tailTrace_615085 : CollatzResearch.WordTrace tailWord_615085 prefixEnd_615085 93580518035801840239639 := by
  unfold tailWord_615085
  simp only [CollatzResearch.WordTrace]
  refine ⟨22433992976659567999798709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14955995317773045333199139 22433992976659567999798709)
  ·
    refine ⟨2103186841561834499981129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 22433992976659567999798709 2103186841561834499981129)
    ·
      refine ⟨1577390131171375874985847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2103186841561834499981129 1577390131171375874985847)
      ·
        refine ⟨2366085196757063812478771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1577390131171375874985847 2366085196757063812478771)
        ·
          refine ⟨3549127795135595718718157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2366085196757063812478771 3549127795135595718718157)
          ·
            refine ⟨1330922923175848394519309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3549127795135595718718157 1330922923175848394519309)
            ·
              refine ⟨499096096190943147944741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1330922923175848394519309 499096096190943147944741)
              ·
                refine ⟨93580518035801840239639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 499096096190943147944741 93580518035801840239639)
                ·
                  rfl

theorem cell20_615085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 3, 3, 4].length) (baseStart_615085 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_615085 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_615085 prefixEnd_615085 := by exact prefixLift 615085
  have htrace : WordTrace (prefixWord ++ tailWord_615085) baseStart_615085 baseEnd_615085 := by
    simpa [prefixWord, tailWord_615085, baseEnd_615085] using wordTrace_append hprefix tailTrace_615085
  have hstable : (prefixWord ++ tailWord_615085).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_615085).length < 2 ^ (prefixWord ++ tailWord_615085).sum := by decide
  have hdescent : baseEnd_615085 < baseStart_615085 := by decide
  rcases family_descends (prefixWord ++ tailWord_615085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_615105 : List Nat := [1, 2, 6, 2, 2, 1, 1, 2, 3]
def baseStart_615105 : Nat := 118140960795 + 615105 * 2 ^ 59
def prefixEnd_615105 : Nat := 4983230072969 + 3 ^ 40 * 615105 * 2
def baseEnd_615105 : Nat := 280750682652374340052169

theorem tailTrace_615105 : CollatzResearch.WordTrace tailWord_615105 prefixEnd_615105 280750682652374340052169 := by
  unfold tailWord_615105
  simp only [CollatzResearch.WordTrace]
  refine ⟨22434722436587111415526769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14956481624391407610351179 22434722436587111415526769)
  ·
    refine ⟨16826041827440333561645077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22434722436587111415526769 16826041827440333561645077)
    ·
      refine ⟨788720710661265635702113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 16826041827440333561645077 788720710661265635702113)
      ·
        refine ⟨591540532995949226776585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 788720710661265635702113 591540532995949226776585)
        ·
          refine ⟨443655399746961920082439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 591540532995949226776585 443655399746961920082439)
          ·
            refine ⟨665483099620442880123659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 443655399746961920082439 665483099620442880123659)
            ·
              refine ⟨998224649430664320185489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 665483099620442880123659 998224649430664320185489)
              ·
                refine ⟨748668487072998240139117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 998224649430664320185489 748668487072998240139117)
                ·
                  refine ⟨280750682652374340052169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 748668487072998240139117 280750682652374340052169)
                  ·
                    rfl

theorem cell20_615105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 2, 1, 1, 2, 3].length) (baseStart_615105 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_615105 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_615105 prefixEnd_615105 := by exact prefixLift 615105
  have htrace : WordTrace (prefixWord ++ tailWord_615105) baseStart_615105 baseEnd_615105 := by
    simpa [prefixWord, tailWord_615105, baseEnd_615105] using wordTrace_append hprefix tailTrace_615105
  have hstable : (prefixWord ++ tailWord_615105).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_615105).length < 2 ^ (prefixWord ++ tailWord_615105).sum := by decide
  have hdescent : baseEnd_615105 < baseStart_615105 := by decide
  rcases family_descends (prefixWord ++ tailWord_615105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_615116 : List Nat := [2, 2, 1, 5, 1, 1, 2, 4, 2]
def baseStart_615116 : Nat := 118140960795 + 615116 * 2 ^ 59
def prefixEnd_615116 : Nat := 4983230072969 + 3 ^ 40 * 615116 * 2
def baseEnd_615116 : Nat := 280755703352107190685457

theorem tailTrace_615116 : CollatzResearch.WordTrace tailWord_615116 prefixEnd_615116 280755703352107190685457 := by
  unfold tailWord_615116
  simp only [CollatzResearch.WordTrace]
  refine ⟨11217561819773630147088601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14956749093031506862784801 11217561819773630147088601)
  ·
    refine ⟨8413171364830222610316451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11217561819773630147088601 8413171364830222610316451)
    ·
      refine ⟨12619757047245333915474677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8413171364830222610316451 12619757047245333915474677)
      ·
        refine ⟨1183102223179250054575751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 12619757047245333915474677 1183102223179250054575751)
        ·
          refine ⟨1774653334768875081863627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1183102223179250054575751 1774653334768875081863627)
          ·
            refine ⟨2661980002153312622795441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1774653334768875081863627 2661980002153312622795441)
            ·
              refine ⟨1996485001614984467096581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2661980002153312622795441 1996485001614984467096581)
              ·
                refine ⟨374340937802809587580609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1996485001614984467096581 374340937802809587580609)
                ·
                  refine ⟨280755703352107190685457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 374340937802809587580609 280755703352107190685457)
                  ·
                    rfl

theorem cell20_615116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 2, 4, 2].length) (baseStart_615116 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_615116 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_615116 prefixEnd_615116 := by exact prefixLift 615116
  have htrace : WordTrace (prefixWord ++ tailWord_615116) baseStart_615116 baseEnd_615116 := by
    simpa [prefixWord, tailWord_615116, baseEnd_615116] using wordTrace_append hprefix tailTrace_615116
  have hstable : (prefixWord ++ tailWord_615116).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_615116).length < 2 ^ (prefixWord ++ tailWord_615116).sum := by decide
  have hdescent : baseEnd_615116 < baseStart_615116 := by decide
  rcases family_descends (prefixWord ++ tailWord_615116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_615130 : List Nat := [3, 1, 1, 2, 2, 2, 5, 1, 3]
def baseStart_615130 : Nat := 118140960795 + 615130 * 2 ^ 59
def prefixEnd_615130 : Nat := 4983230072969 + 3 ^ 40 * 615130 * 2
def baseEnd_615130 : Nat := 280762093333585364218733

theorem tailTrace_615130 : CollatzResearch.WordTrace tailWord_615130 prefixEnd_615130 280762093333585364218733 := by
  unfold tailWord_615130
  simp only [CollatzResearch.WordTrace]
  refine ⟨5608908565374135171296711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14957089507664360456791229 5608908565374135171296711)
  ·
    refine ⟨8413362848061202756945067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5608908565374135171296711 8413362848061202756945067)
    ·
      refine ⟨12620044272091804135417601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8413362848061202756945067 12620044272091804135417601)
      ·
        refine ⟨9465033204068853101563201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12620044272091804135417601 9465033204068853101563201)
        ·
          refine ⟨7098774903051639826172401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9465033204068853101563201 7098774903051639826172401)
          ·
            refine ⟨5324081177288729869629301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7098774903051639826172401 5324081177288729869629301)
            ·
              refine ⟨499132610370818425277747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5324081177288729869629301 499132610370818425277747)
              ·
                refine ⟨748698915556227637916621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 499132610370818425277747 748698915556227637916621)
                ·
                  refine ⟨280762093333585364218733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 748698915556227637916621 280762093333585364218733)
                  ·
                    rfl

theorem cell20_615130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 5, 1, 3].length) (baseStart_615130 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_615130 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_615130 prefixEnd_615130 := by exact prefixLift 615130
  have htrace : WordTrace (prefixWord ++ tailWord_615130) baseStart_615130 baseEnd_615130 := by
    simpa [prefixWord, tailWord_615130, baseEnd_615130] using wordTrace_append hprefix tailTrace_615130
  have hstable : (prefixWord ++ tailWord_615130).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_615130).length < 2 ^ (prefixWord ++ tailWord_615130).sum := by decide
  have hdescent : baseEnd_615130 < baseStart_615130 := by decide
  rcases family_descends (prefixWord ++ tailWord_615130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_615144 : List Nat := [2, 1, 4, 1, 4, 1, 1, 6]
def baseStart_615144 : Nat := 118140960795 + 615144 * 2 ^ 59
def prefixEnd_615144 : Nat := 4983230072969 + 3 ^ 40 * 615144 * 2
def baseEnd_615144 : Nat := 93589494438354512584003

theorem tailTrace_615144 : CollatzResearch.WordTrace tailWord_615144 prefixEnd_615144 93589494438354512584003 := by
  unfold tailWord_615144
  simp only [CollatzResearch.WordTrace]
  refine ⟨11218072441722910538098243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14957429922297214050797657 11218072441722910538098243)
  ·
    refine ⟨16827108662584365807147365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11218072441722910538098243 16827108662584365807147365)
    ·
      refine ⟨3155082874234568588840131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16827108662584365807147365 3155082874234568588840131)
      ·
        refine ⟨4732624311351852883260197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3155082874234568588840131 4732624311351852883260197)
        ·
          refine ⟨887367058378472415611287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4732624311351852883260197 887367058378472415611287)
          ·
            refine ⟨1331050587567708623416931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 887367058378472415611287 1331050587567708623416931)
            ·
              refine ⟨1996575881351562935125397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1331050587567708623416931 1996575881351562935125397)
              ·
                refine ⟨93589494438354512584003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1996575881351562935125397 93589494438354512584003)
                ·
                  rfl

theorem cell20_615144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 1, 1, 6].length) (baseStart_615144 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_615144 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_615144 prefixEnd_615144 := by exact prefixLift 615144
  have htrace : WordTrace (prefixWord ++ tailWord_615144) baseStart_615144 baseEnd_615144 := by
    simpa [prefixWord, tailWord_615144, baseEnd_615144] using wordTrace_append hprefix tailTrace_615144
  have hstable : (prefixWord ++ tailWord_615144).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_615144).length < 2 ^ (prefixWord ++ tailWord_615144).sum := by decide
  have hdescent : baseEnd_615144 < baseStart_615144 := by decide
  rcases family_descends (prefixWord ++ tailWord_615144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_615154 : List Nat := [3, 2, 1, 3, 1, 2, 3, 3, 2]
def baseStart_615154 : Nat := 118140960795 + 615154 * 2 ^ 59
def prefixEnd_615154 : Nat := 4983230072969 + 3 ^ 40 * 615154 * 2
def baseEnd_615154 : Nat := 280773047587547947418635

theorem tailTrace_615154 : CollatzResearch.WordTrace tailWord_615154 prefixEnd_615154 280773047587547947418635 := by
  unfold tailWord_615154
  simp only [CollatzResearch.WordTrace]
  refine ⟨5609127403352398196015129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14957673075606395189373677 5609127403352398196015129)
  ·
    refine ⟨4206845552514298647011347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5609127403352398196015129 4206845552514298647011347)
    ·
      refine ⟨6310268328771447970517021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4206845552514298647011347 6310268328771447970517021)
      ·
        refine ⟨2366350623289292988943883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6310268328771447970517021 2366350623289292988943883)
        ·
          refine ⟨3549525934933939483415825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2366350623289292988943883 3549525934933939483415825)
          ·
            refine ⟨2662144451200454612561869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3549525934933939483415825 2662144451200454612561869)
            ·
              refine ⟨998304169200170479710701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2662144451200454612561869 998304169200170479710701)
              ·
                refine ⟨374364063450063929891513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 998304169200170479710701 374364063450063929891513)
                ·
                  refine ⟨280773047587547947418635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 374364063450063929891513 280773047587547947418635)
                  ·
                    rfl

theorem cell20_615154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 3, 3, 2].length) (baseStart_615154 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_615154 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_615154 prefixEnd_615154 := by exact prefixLift 615154
  have htrace : WordTrace (prefixWord ++ tailWord_615154) baseStart_615154 baseEnd_615154 := by
    simpa [prefixWord, tailWord_615154, baseEnd_615154] using wordTrace_append hprefix tailTrace_615154
  have hstable : (prefixWord ++ tailWord_615154).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_615154).length < 2 ^ (prefixWord ++ tailWord_615154).sum := by decide
  have hdescent : baseEnd_615154 < baseStart_615154 := by decide
  rcases family_descends (prefixWord ++ tailWord_615154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_615157 : List Nat := [1, 3, 6, 1, 2, 1, 6]
def baseStart_615157 : Nat := 118140960795 + 615157 * 2 ^ 59
def prefixEnd_615157 : Nat := 4983230072969 + 3 ^ 40 * 615157 * 2
def baseEnd_615157 : Nat := 31197157429921474479847

theorem tailTrace_615157 : CollatzResearch.WordTrace tailWord_615157 prefixEnd_615157 31197157429921474479847 := by
  unfold tailWord_615157
  simp only [CollatzResearch.WordTrace]
  refine ⟨22436619032398724296419725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14957746021599149530946483 22436619032398724296419725)
  ·
    refine ⟨8413732137149521611157397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22436619032398724296419725 8413732137149521611157397)
    ·
      refine ⟨394393693928883825523003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 8413732137149521611157397 394393693928883825523003)
      ·
        refine ⟨591590540893325738284505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 394393693928883825523003 591590540893325738284505)
        ·
          refine ⟨443692905669994303713379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 591590540893325738284505 443692905669994303713379)
          ·
            refine ⟨665539358504991455570069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 443692905669994303713379 665539358504991455570069)
            ·
              refine ⟨31197157429921474479847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 665539358504991455570069 31197157429921474479847)
              ·
                rfl

theorem cell20_615157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 2, 1, 6].length) (baseStart_615157 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_615157 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_615157 prefixEnd_615157 := by exact prefixLift 615157
  have htrace : WordTrace (prefixWord ++ tailWord_615157) baseStart_615157 baseEnd_615157 := by
    simpa [prefixWord, tailWord_615157, baseEnd_615157] using wordTrace_append hprefix tailTrace_615157
  have hstable : (prefixWord ++ tailWord_615157).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_615157).length < 2 ^ (prefixWord ++ tailWord_615157).sum := by decide
  have hdescent : baseEnd_615157 < baseStart_615157 := by decide
  rcases family_descends (prefixWord ++ tailWord_615157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_615175 : List Nat := [1, 1, 4, 4, 1, 1, 3, 1, 4]
def baseStart_615175 : Nat := 118140960795 + 615175 * 2 ^ 59
def prefixEnd_615175 : Nat := 4983230072969 + 3 ^ 40 * 615175 * 2
def baseEnd_615175 : Nat := 280782632559765207718549

theorem tailTrace_615175 : CollatzResearch.WordTrace tailWord_615175 prefixEnd_615175 280782632559765207718549 := by
  unfold tailWord_615175
  simp only [CollatzResearch.WordTrace]
  refine ⟨22437275546333513370574979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14958183697555675580383319 22437275546333513370574979)
  ·
    refine ⟨33655913319500270055862469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22437275546333513370574979 33655913319500270055862469)
    ·
      refine ⟨6310483747406300635474213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 33655913319500270055862469 6310483747406300635474213)
      ·
        refine ⟨1183215702638681369151415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6310483747406300635474213 1183215702638681369151415)
        ·
          refine ⟨1774823553958022053727123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1183215702638681369151415 1774823553958022053727123)
          ·
            refine ⟨2662235330937033080590685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1774823553958022053727123 2662235330937033080590685)
            ·
              refine ⟨998338249101387405221507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2662235330937033080590685 998338249101387405221507)
              ·
                refine ⟨1497507373652081107832261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 998338249101387405221507 1497507373652081107832261)
                ·
                  refine ⟨280782632559765207718549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1497507373652081107832261 280782632559765207718549)
                  ·
                    rfl

theorem cell20_615175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 3, 1, 4].length) (baseStart_615175 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_615175 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_615175 prefixEnd_615175 := by exact prefixLift 615175
  have htrace : WordTrace (prefixWord ++ tailWord_615175) baseStart_615175 baseEnd_615175 := by
    simpa [prefixWord, tailWord_615175, baseEnd_615175] using wordTrace_append hprefix tailTrace_615175
  have hstable : (prefixWord ++ tailWord_615175).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_615175).length < 2 ^ (prefixWord ++ tailWord_615175).sum := by decide
  have hdescent : baseEnd_615175 < baseStart_615175 := by decide
  rcases family_descends (prefixWord ++ tailWord_615175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_615189 : List Nat := [1, 3, 2, 1, 2, 2, 3, 3, 3]
def baseStart_615189 : Nat := 118140960795 + 615189 * 2 ^ 59
def prefixEnd_615189 : Nat := 4983230072969 + 3 ^ 40 * 615189 * 2
def baseEnd_615189 : Nat := 280789022541243381251825

theorem tailTrace_615189 : CollatzResearch.WordTrace tailWord_615189 prefixEnd_615189 280789022541243381251825 := by
  unfold tailWord_615189
  simp only [CollatzResearch.WordTrace]
  refine ⟨22437786168282793761584621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14958524112188529174389747 22437786168282793761584621)
  ·
    refine ⟨8414169813106047660594233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22437786168282793761584621 8414169813106047660594233)
    ·
      refine ⟨6310627359829535745445675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8414169813106047660594233 6310627359829535745445675)
      ·
        refine ⟨9465941039744303618168513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6310627359829535745445675 9465941039744303618168513)
        ·
          refine ⟨7099455779808227713626385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9465941039744303618168513 7099455779808227713626385)
          ·
            refine ⟨5324591834856170785219789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7099455779808227713626385 5324591834856170785219789)
            ·
              refine ⟨1996721938071064044457421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5324591834856170785219789 1996721938071064044457421)
              ·
                refine ⟨748770726776649016671533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1996721938071064044457421 748770726776649016671533)
                ·
                  refine ⟨280789022541243381251825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 748770726776649016671533 280789022541243381251825)
                  ·
                    rfl

theorem cell20_615189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 3, 3, 3].length) (baseStart_615189 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_615189 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_615189 prefixEnd_615189 := by exact prefixLift 615189
  have htrace : WordTrace (prefixWord ++ tailWord_615189) baseStart_615189 baseEnd_615189 := by
    simpa [prefixWord, tailWord_615189, baseEnd_615189] using wordTrace_append hprefix tailTrace_615189
  have hstable : (prefixWord ++ tailWord_615189).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_615189).length < 2 ^ (prefixWord ++ tailWord_615189).sum := by decide
  have hdescent : baseEnd_615189 < baseStart_615189 := by decide
  rcases family_descends (prefixWord ++ tailWord_615189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_615220 : List Nat := [2, 5, 1, 1, 3, 8]
def baseStart_615220 : Nat := 118140960795 + 615220 * 2 ^ 59
def prefixEnd_615220 : Nat := 4983230072969 + 3 ^ 40 * 615220 * 2
def baseEnd_615220 : Nat := 10400117473553520415495

theorem tailTrace_615220 : CollatzResearch.WordTrace tailWord_615220 prefixEnd_615220 10400117473553520415495 := by
  unfold tailWord_615220
  simp only [CollatzResearch.WordTrace]
  refine ⟨11219458415585243027981557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14959277887446990703975409 11219458415585243027981557)
  ·
    refine ⟨1051824226461116533873271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 11219458415585243027981557 1051824226461116533873271)
    ·
      refine ⟨1577736339691674800809907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1051824226461116533873271 1577736339691674800809907)
      ·
        refine ⟨2366604509537512201214861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1577736339691674800809907 2366604509537512201214861)
        ·
          refine ⟨887476691076567075455573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2366604509537512201214861 887476691076567075455573)
          ·
            refine ⟨10400117473553520415495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 887476691076567075455573 10400117473553520415495)
            ·
              rfl

theorem cell20_615220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 8].length) (baseStart_615220 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_615220 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_615220 prefixEnd_615220 := by exact prefixLift 615220
  have htrace : WordTrace (prefixWord ++ tailWord_615220) baseStart_615220 baseEnd_615220 := by
    simpa [prefixWord, tailWord_615220, baseEnd_615220] using wordTrace_append hprefix tailTrace_615220
  have hstable : (prefixWord ++ tailWord_615220).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_615220).length < 2 ^ (prefixWord ++ tailWord_615220).sum := by decide
  have hdescent : baseEnd_615220 < baseStart_615220 := by decide
  rcases family_descends (prefixWord ++ tailWord_615220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_615226 : List Nat := [3, 1, 1, 1, 7, 1, 2, 2, 2]
def baseStart_615226 : Nat := 118140960795 + 615226 * 2 ^ 59
def prefixEnd_615226 : Nat := 4983230072969 + 3 ^ 40 * 615226 * 2
def baseEnd_615226 : Nat := 280805910349435697018341

theorem tailTrace_615226 : CollatzResearch.WordTrace tailWord_615226 prefixEnd_615226 280805910349435697018341 := by
  unfold tailWord_615226
  simp only [CollatzResearch.WordTrace]
  refine ⟨5609783917287187270170383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14959423779432499387121021 5609783917287187270170383)
  ·
    refine ⟨8414675875930780905255575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5609783917287187270170383 8414675875930780905255575)
    ·
      refine ⟨12622013813896171357883363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8414675875930780905255575 12622013813896171357883363)
      ·
        refine ⟨18933020720844257036825045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12622013813896171357883363 18933020720844257036825045)
        ·
          refine ⟨443742673144787274300587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 18933020720844257036825045 443742673144787274300587)
          ·
            refine ⟨665614009717180911450881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 443742673144787274300587 665614009717180911450881)
            ·
              refine ⟨499210507287885683588161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 665614009717180911450881 499210507287885683588161)
              ·
                refine ⟨374407880465914262691121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 499210507287885683588161 374407880465914262691121)
                ·
                  refine ⟨280805910349435697018341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 374407880465914262691121 280805910349435697018341)
                  ·
                    rfl

theorem cell20_615226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 7, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 7, 1, 2, 2, 2].length) (baseStart_615226 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_615226 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_615226 prefixEnd_615226 := by exact prefixLift 615226
  have htrace : WordTrace (prefixWord ++ tailWord_615226) baseStart_615226 baseEnd_615226 := by
    simpa [prefixWord, tailWord_615226, baseEnd_615226] using wordTrace_append hprefix tailTrace_615226
  have hstable : (prefixWord ++ tailWord_615226).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_615226).length < 2 ^ (prefixWord ++ tailWord_615226).sum := by decide
  have hdescent : baseEnd_615226 < baseStart_615226 := by decide
  rcases family_descends (prefixWord ++ tailWord_615226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_615241 : List Nat := [1, 2, 1, 1, 2, 5, 3, 5]
def baseStart_615241 : Nat := 118140960795 + 615241 * 2 ^ 59
def prefixEnd_615241 : Nat := 4983230072969 + 3 ^ 40 * 615241 * 2
def baseEnd_615241 : Nat := 93604252252720770506093

theorem tailTrace_615241 : CollatzResearch.WordTrace tailWord_615241 prefixEnd_615241 93604252252720770506093 := by
  unfold tailWord_615241
  simp only [CollatzResearch.WordTrace]
  refine ⟨22439682764094406642477577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14959788509396271094985051 22439682764094406642477577)
  ·
    refine ⟨16829762073070804981858183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22439682764094406642477577 16829762073070804981858183)
    ·
      refine ⟨25244643109606207472787275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16829762073070804981858183 25244643109606207472787275)
      ·
        refine ⟨37866964664409311209180913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25244643109606207472787275 37866964664409311209180913)
        ·
          refine ⟨28400223498306983406885685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37866964664409311209180913 28400223498306983406885685)
          ·
            refine ⟨2662520952966279694395533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 28400223498306983406885685 2662520952966279694395533)
            ·
              refine ⟨998445357362354885398325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2662520952966279694395533 998445357362354885398325)
              ·
                refine ⟨93604252252720770506093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 998445357362354885398325 93604252252720770506093)
                ·
                  rfl

theorem cell20_615241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 3, 5].length) (baseStart_615241 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_615241 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_615241 prefixEnd_615241 := by exact prefixLift 615241
  have htrace : WordTrace (prefixWord ++ tailWord_615241) baseStart_615241 baseEnd_615241 := by
    simpa [prefixWord, tailWord_615241, baseEnd_615241] using wordTrace_append hprefix tailTrace_615241
  have hstable : (prefixWord ++ tailWord_615241).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_615241).length < 2 ^ (prefixWord ++ tailWord_615241).sum := by decide
  have hdescent : baseEnd_615241 < baseStart_615241 := by decide
  rcases family_descends (prefixWord ++ tailWord_615241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_615258 : List Nat := [3, 1, 1, 2, 1, 5, 3, 4]
def baseStart_615258 : Nat := 118140960795 + 615258 * 2 ^ 59
def prefixEnd_615258 : Nat := 4983230072969 + 3 ^ 40 * 615258 * 2
def baseEnd_615258 : Nat := 93606838673795269317181

theorem tailTrace_615258 : CollatzResearch.WordTrace tailWord_615258 prefixEnd_615258 93606838673795269317181 := by
  unfold tailWord_615258
  simp only [CollatzResearch.WordTrace]
  refine ⟨5610075701258204636461607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14960201870021879030564285 5610075701258204636461607)
  ·
    refine ⟨8415113551887306954692411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5610075701258204636461607 8415113551887306954692411)
    ·
      refine ⟨12622670327830960432038617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8415113551887306954692411 12622670327830960432038617)
      ·
        refine ⟨9467002745873220324028963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12622670327830960432038617 9467002745873220324028963)
        ·
          refine ⟨14200504118809830486043445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9467002745873220324028963 14200504118809830486043445)
          ·
            refine ⟨1331297261138421608066573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 14200504118809830486043445 1331297261138421608066573)
            ·
              refine ⟨499236472926908103024965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1331297261138421608066573 499236472926908103024965)
              ·
                refine ⟨93606838673795269317181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 499236472926908103024965 93606838673795269317181)
                ·
                  rfl

theorem cell20_615258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 5, 3, 4].length) (baseStart_615258 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_615258 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_615258 prefixEnd_615258 := by exact prefixLift 615258
  have htrace : WordTrace (prefixWord ++ tailWord_615258) baseStart_615258 baseEnd_615258 := by
    simpa [prefixWord, tailWord_615258, baseEnd_615258] using wordTrace_append hprefix tailTrace_615258
  have hstable : (prefixWord ++ tailWord_615258).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_615258).length < 2 ^ (prefixWord ++ tailWord_615258).sum := by decide
  have hdescent : baseEnd_615258 < baseStart_615258 := by decide
  rcases family_descends (prefixWord ++ tailWord_615258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_615268 : List Nat := [2, 3, 1, 1, 4, 2, 2, 3, 2]
def baseStart_615268 : Nat := 118140960795 + 615268 * 2 ^ 59
def prefixEnd_615268 : Nat := 4983230072969 + 3 ^ 40 * 615268 * 2
def baseEnd_615268 : Nat := 280825080293870217618169

theorem tailTrace_615268 : CollatzResearch.WordTrace tailWord_615268 prefixEnd_615268 280825080293870217618169 := by
  unfold tailWord_615268
  simp only [CollatzResearch.WordTrace]
  refine ⟨11220333767498295126855229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14960445023331060169140305 11220333767498295126855229)
  ·
    refine ⟨4207625162811860672570711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11220333767498295126855229 4207625162811860672570711)
    ·
      refine ⟨6311437744217791008856067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4207625162811860672570711 6311437744217791008856067)
      ·
        refine ⟨9467156616326686513284101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6311437744217791008856067 9467156616326686513284101)
        ·
          refine ⟨1775091865561253721240769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9467156616326686513284101 1775091865561253721240769)
          ·
            refine ⟨1331318899170940290930577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1775091865561253721240769 1331318899170940290930577)
            ·
              refine ⟨998489174378205218197933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1331318899170940290930577 998489174378205218197933)
              ·
                refine ⟨374433440391826956824225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 998489174378205218197933 374433440391826956824225)
                ·
                  refine ⟨280825080293870217618169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 374433440391826956824225 280825080293870217618169)
                  ·
                    rfl

theorem cell20_615268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 2, 2, 3, 2].length) (baseStart_615268 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_615268 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_615268 prefixEnd_615268 := by exact prefixLift 615268
  have htrace : WordTrace (prefixWord ++ tailWord_615268) baseStart_615268 baseEnd_615268 := by
    simpa [prefixWord, tailWord_615268, baseEnd_615268] using wordTrace_append hprefix tailTrace_615268
  have hstable : (prefixWord ++ tailWord_615268).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_615268).length < 2 ^ (prefixWord ++ tailWord_615268).sum := by decide
  have hdescent : baseEnd_615268 < baseStart_615268 := by decide
  rcases family_descends (prefixWord ++ tailWord_615268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_615278 : List Nat := [4, 1, 2, 3, 3, 1, 1, 2, 3]
def baseStart_615278 : Nat := 118140960795 + 615278 * 2 ^ 59
def prefixEnd_615278 : Nat := 4983230072969 + 3 ^ 40 * 615278 * 2
def baseEnd_615278 : Nat := 280829644566354627284795

theorem tailTrace_615278 : CollatzResearch.WordTrace tailWord_615278 prefixEnd_615278 280829644566354627284795 := by
  unfold tailWord_615278
  simp only [CollatzResearch.WordTrace]
  refine ⟨2805129033120045245196811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14960688176640241307716325 2805129033120045245196811)
  ·
    refine ⟨4207693549680067867795217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2805129033120045245196811 4207693549680067867795217)
    ·
      refine ⟨3155770162260050900846413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4207693549680067867795217 3155770162260050900846413)
      ·
        refine ⟨1183413810847519087817405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3155770162260050900846413 1183413810847519087817405)
        ·
          refine ⟨443780179067819657931527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1183413810847519087817405 443780179067819657931527)
          ·
            refine ⟨665670268601729486897291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 443780179067819657931527 665670268601729486897291)
            ·
              refine ⟨998505402902594230345937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 665670268601729486897291 998505402902594230345937)
              ·
                refine ⟨748879052176945672759453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 998505402902594230345937 748879052176945672759453)
                ·
                  refine ⟨280829644566354627284795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 748879052176945672759453 280829644566354627284795)
                  ·
                    rfl

theorem cell20_615278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 3, 1, 1, 2, 3].length) (baseStart_615278 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_615278 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_615278 prefixEnd_615278 := by exact prefixLift 615278
  have htrace : WordTrace (prefixWord ++ tailWord_615278) baseStart_615278 baseEnd_615278 := by
    simpa [prefixWord, tailWord_615278, baseEnd_615278] using wordTrace_append hprefix tailTrace_615278
  have hstable : (prefixWord ++ tailWord_615278).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_615278).length < 2 ^ (prefixWord ++ tailWord_615278).sum := by decide
  have hdescent : baseEnd_615278 < baseStart_615278 := by decide
  rcases family_descends (prefixWord ++ tailWord_615278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_615289 : List Nat := [1, 2, 1, 3, 2, 3, 2, 4, 2]
def baseStart_615289 : Nat := 118140960795 + 615289 * 2 ^ 59
def prefixEnd_615289 : Nat := 4983230072969 + 3 ^ 40 * 615289 * 2
def baseEnd_615289 : Nat := 280834665266087477918083

theorem tailTrace_615289 : CollatzResearch.WordTrace tailWord_615289 prefixEnd_615289 280834665266087477918083 := by
  unfold tailWord_615289
  simp only [CollatzResearch.WordTrace]
  refine ⟨22441433467920510840224921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14960955645280340560149947 22441433467920510840224921)
  ·
    refine ⟨16831075100940383130168691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22441433467920510840224921 16831075100940383130168691)
    ·
      refine ⟨25246612651410574695253037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16831075100940383130168691 25246612651410574695253037)
      ·
        refine ⟨9467479744278965510719889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25246612651410574695253037 9467479744278965510719889)
        ·
          refine ⟨7100609808209224133039917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9467479744278965510719889 7100609808209224133039917)
          ·
            refine ⟨2662728678078459049889969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7100609808209224133039917 2662728678078459049889969)
            ·
              refine ⟨1997046508558844287417477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2662728678078459049889969 1997046508558844287417477)
              ·
                refine ⟨374446220354783303890777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1997046508558844287417477 374446220354783303890777)
                ·
                  refine ⟨280834665266087477918083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 374446220354783303890777 280834665266087477918083)
                  ·
                    rfl

theorem cell20_615289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 2, 4, 2].length) (baseStart_615289 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_615289 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_615289 prefixEnd_615289 := by exact prefixLift 615289
  have htrace : WordTrace (prefixWord ++ tailWord_615289) baseStart_615289 baseEnd_615289 := by
    simpa [prefixWord, tailWord_615289, baseEnd_615289] using wordTrace_append hprefix tailTrace_615289
  have hstable : (prefixWord ++ tailWord_615289).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_615289).length < 2 ^ (prefixWord ++ tailWord_615289).sum := by decide
  have hdescent : baseEnd_615289 < baseStart_615289 := by decide
  rcases family_descends (prefixWord ++ tailWord_615289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_615317 : List Nat := [1, 3, 2, 1, 1, 5, 1, 6]
def baseStart_615317 : Nat := 118140960795 + 615317 * 2 ^ 59
def prefixEnd_615317 : Nat := 4983230072969 + 3 ^ 40 * 615317 * 2
def baseEnd_615317 : Nat := 93615815076347941661545

theorem tailTrace_615317 : CollatzResearch.WordTrace tailWord_615317 prefixEnd_615317 93615815076347941661545 := by
  unfold tailWord_615317
  simp only [CollatzResearch.WordTrace]
  refine ⟨22442454711819071622244205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14961636474546047748162803 22442454711819071622244205)
  ·
    refine ⟨8415920516932151858341577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22442454711819071622244205 8415920516932151858341577)
    ·
      refine ⟨6311940387699113893756183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8415920516932151858341577 6311940387699113893756183)
      ·
        refine ⟨9467910581548670840634275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6311940387699113893756183 9467910581548670840634275)
        ·
          refine ⟨14201865872323006260951413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9467910581548670840634275 14201865872323006260951413)
          ·
            refine ⟨1331424925530281836964195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 14201865872323006260951413 1331424925530281836964195)
            ·
              refine ⟨1997137388295422755446293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1331424925530281836964195 1997137388295422755446293)
              ·
                refine ⟨93615815076347941661545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1997137388295422755446293 93615815076347941661545)
                ·
                  rfl

theorem cell20_615317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 5, 1, 6].length) (baseStart_615317 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_615317 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_615317 prefixEnd_615317 := by exact prefixLift 615317
  have htrace : WordTrace (prefixWord ++ tailWord_615317) baseStart_615317 baseEnd_615317 := by
    simpa [prefixWord, tailWord_615317, baseEnd_615317] using wordTrace_append hprefix tailTrace_615317
  have hstable : (prefixWord ++ tailWord_615317).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_615317).length < 2 ^ (prefixWord ++ tailWord_615317).sum := by decide
  have hdescent : baseEnd_615317 < baseStart_615317 := by decide
  rcases family_descends (prefixWord ++ tailWord_615317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_615331 : List Nat := [1, 1, 1, 4, 1, 2, 2, 2, 6]
def baseStart_615331 : Nat := 118140960795 + 615331 * 2 ^ 59
def prefixEnd_615331 : Nat := 4983230072969 + 3 ^ 40 * 615331 * 2
def baseEnd_615331 : Nat := 280853835210521998517911

theorem tailTrace_615331 : CollatzResearch.WordTrace tailWord_615331 prefixEnd_615331 280853835210521998517911 := by
  unfold tailWord_615331
  simp only [CollatzResearch.WordTrace]
  refine ⟨22442965333768352013253847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14961976889178901342169231 22442965333768352013253847)
  ·
    refine ⟨33664448000652528019880771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22442965333768352013253847 33664448000652528019880771)
    ·
      refine ⟨50496672000978792029821157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33664448000652528019880771 50496672000978792029821157)
      ·
        refine ⟨9468126000183523505591467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 50496672000978792029821157 9468126000183523505591467)
        ·
          refine ⟨14202189000275285258387201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9468126000183523505591467 14202189000275285258387201)
          ·
            refine ⟨10651641750206463943790401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14202189000275285258387201 10651641750206463943790401)
            ·
              refine ⟨7988731312654847957842801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10651641750206463943790401 7988731312654847957842801)
              ·
                refine ⟨5991548484491135968382101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7988731312654847957842801 5991548484491135968382101)
                ·
                  refine ⟨280853835210521998517911, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5991548484491135968382101 280853835210521998517911)
                  ·
                    rfl

theorem cell20_615331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 2, 2, 6].length) (baseStart_615331 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_615331 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_615331 prefixEnd_615331 := by exact prefixLift 615331
  have htrace : WordTrace (prefixWord ++ tailWord_615331) baseStart_615331 baseEnd_615331 := by
    simpa [prefixWord, tailWord_615331, baseEnd_615331] using wordTrace_append hprefix tailTrace_615331
  have hstable : (prefixWord ++ tailWord_615331).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_615331).length < 2 ^ (prefixWord ++ tailWord_615331).sum := by decide
  have hdescent : baseEnd_615331 < baseStart_615331 := by decide
  rcases family_descends (prefixWord ++ tailWord_615331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_615350 : List Nat := [5, 1, 4, 1, 1, 2, 2, 1, 3]
def baseStart_615350 : Nat := 118140960795 + 615350 * 2 ^ 59
def prefixEnd_615350 : Nat := 4983230072969 + 3 ^ 40 * 615350 * 2
def baseEnd_615350 : Nat := 280862507328242376884501

theorem tailTrace_615350 : CollatzResearch.WordTrace tailWord_615350 prefixEnd_615350 280862507328242376884501 := by
  unfold tailWord_615350
  simp only [CollatzResearch.WordTrace]
  refine ⟨1402728645043719891137219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 14962438880466345505463669 1402728645043719891137219)
  ·
    refine ⟨2104092967565579836705829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1402728645043719891137219 2104092967565579836705829)
    ·
      refine ⟨394517431418546219382343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2104092967565579836705829 394517431418546219382343)
      ·
        refine ⟨591776147127819329073515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 394517431418546219382343 591776147127819329073515)
        ·
          refine ⟨887664220691728993610273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 591776147127819329073515 887664220691728993610273)
          ·
            refine ⟨665748165518796745207705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 887664220691728993610273 665748165518796745207705)
            ·
              refine ⟨499311124139097558905779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 665748165518796745207705 499311124139097558905779)
              ·
                refine ⟨748966686208646338358669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 499311124139097558905779 748966686208646338358669)
                ·
                  refine ⟨280862507328242376884501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 748966686208646338358669 280862507328242376884501)
                  ·
                    rfl

theorem cell20_615350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 2, 2, 1, 3].length) (baseStart_615350 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_615350 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_615350 prefixEnd_615350 := by exact prefixLift 615350
  have htrace : WordTrace (prefixWord ++ tailWord_615350) baseStart_615350 baseEnd_615350 := by
    simpa [prefixWord, tailWord_615350, baseEnd_615350] using wordTrace_append hprefix tailTrace_615350
  have hstable : (prefixWord ++ tailWord_615350).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_615350).length < 2 ^ (prefixWord ++ tailWord_615350).sum := by decide
  have hdescent : baseEnd_615350 < baseStart_615350 := by decide
  rcases family_descends (prefixWord ++ tailWord_615350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_615399 : List Nat := [1, 1, 5, 2, 2, 3, 2, 2, 2]
def baseStart_615399 : Nat := 118140960795 + 615399 * 2 ^ 59
def prefixEnd_615399 : Nat := 4983230072969 + 3 ^ 40 * 615399 * 2
def baseEnd_615399 : Nat := 280884872263415984250967

theorem tailTrace_615399 : CollatzResearch.WordTrace tailWord_615399 prefixEnd_615399 280884872263415984250967 := by
  unfold tailWord_615399
  simp only [CollatzResearch.WordTrace]
  refine ⟨22445445497521999626729251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14963630331681333084486167 22445445497521999626729251)
  ·
    refine ⟨33668168246282999440093877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22445445497521999626729251 33668168246282999440093877)
    ·
      refine ⟨3156390773089031197508801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 33668168246282999440093877 3156390773089031197508801)
      ·
        refine ⟨2367293079816773398131601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3156390773089031197508801 2367293079816773398131601)
        ·
          refine ⟨1775469809862580048598701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2367293079816773398131601 1775469809862580048598701)
          ·
            refine ⟨665801178698467518224513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1775469809862580048598701 665801178698467518224513)
            ·
              refine ⟨499350884023850638668385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 665801178698467518224513 499350884023850638668385)
              ·
                refine ⟨374513163017887979001289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 499350884023850638668385 374513163017887979001289)
                ·
                  refine ⟨280884872263415984250967, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 374513163017887979001289 280884872263415984250967)
                  ·
                    rfl

theorem cell20_615399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 3, 2, 2, 2].length) (baseStart_615399 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_615399 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_615399 prefixEnd_615399 := by exact prefixLift 615399
  have htrace : WordTrace (prefixWord ++ tailWord_615399) baseStart_615399 baseEnd_615399 := by
    simpa [prefixWord, tailWord_615399, baseEnd_615399] using wordTrace_append hprefix tailTrace_615399
  have hstable : (prefixWord ++ tailWord_615399).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_615399).length < 2 ^ (prefixWord ++ tailWord_615399).sum := by decide
  have hdescent : baseEnd_615399 < baseStart_615399 := by decide
  rcases family_descends (prefixWord ++ tailWord_615399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_615400 : List Nat := [2, 1, 4, 1, 1, 1, 2, 3, 5]
def baseStart_615400 : Nat := 118140960795 + 615400 * 2 ^ 59
def prefixEnd_615400 : Nat := 4983230072969 + 3 ^ 40 * 615400 * 2
def baseEnd_615400 : Nat := 280885328690664425217629

theorem tailTrace_615400 : CollatzResearch.WordTrace tailWord_615400 prefixEnd_615400 280885328690664425217629 := by
  unfold tailWord_615400
  simp only [CollatzResearch.WordTrace]
  refine ⟨11222740985259188398757827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14963654647012251198343769 11222740985259188398757827)
  ·
    refine ⟨16834111477888782598136741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11222740985259188398757827 16834111477888782598136741)
    ·
      refine ⟨3156395902104146737150639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16834111477888782598136741 3156395902104146737150639)
      ·
        refine ⟨4734593853156220105725959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3156395902104146737150639 4734593853156220105725959)
        ·
          refine ⟨7101890779734330158588939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4734593853156220105725959 7101890779734330158588939)
          ·
            refine ⟨10652836169601495237883409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7101890779734330158588939 10652836169601495237883409)
            ·
              refine ⟨7989627127201121428412557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10652836169601495237883409 7989627127201121428412557)
              ·
                refine ⟨2996110172700420535654709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7989627127201121428412557 2996110172700420535654709)
                ·
                  refine ⟨280885328690664425217629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2996110172700420535654709 280885328690664425217629)
                  ·
                    rfl

theorem cell20_615400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 2, 3, 5].length) (baseStart_615400 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_615400 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_615400 prefixEnd_615400 := by exact prefixLift 615400
  have htrace : WordTrace (prefixWord ++ tailWord_615400) baseStart_615400 baseEnd_615400 := by
    simpa [prefixWord, tailWord_615400, baseEnd_615400] using wordTrace_append hprefix tailTrace_615400
  have hstable : (prefixWord ++ tailWord_615400).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_615400).length < 2 ^ (prefixWord ++ tailWord_615400).sum := by decide
  have hdescent : baseEnd_615400 < baseStart_615400 := by decide
  rcases family_descends (prefixWord ++ tailWord_615400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_615455 : List Nat := [1, 1, 2, 4, 1, 3, 3, 2, 3]
def baseStart_615455 : Nat := 118140960795 + 615455 * 2 ^ 59
def prefixEnd_615455 : Nat := 4983230072969 + 3 ^ 40 * 615455 * 2
def baseEnd_615455 : Nat := 280910432189328678384071

theorem tailTrace_615455 : CollatzResearch.WordTrace tailWord_615455 prefixEnd_615455 280910432189328678384071 := by
  unfold tailWord_615455
  simp only [CollatzResearch.WordTrace]
  refine ⟨22447487985319121190767819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14964991990212747460511879 22447487985319121190767819)
  ·
    refine ⟨33671231977978681786151729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22447487985319121190767819 33671231977978681786151729)
    ·
      refine ⟨25253423983484011339613797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33671231977978681786151729 25253423983484011339613797)
      ·
        refine ⟨4735016996903252126177587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 25253423983484011339613797 4735016996903252126177587)
        ·
          refine ⟨7102525495354878189266381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4735016996903252126177587 7102525495354878189266381)
          ·
            refine ⟨2663447060758079320974893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7102525495354878189266381 2663447060758079320974893)
            ·
              refine ⟨998792647784279745365585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2663447060758079320974893 998792647784279745365585)
              ·
                refine ⟨749094485838209809024189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 998792647784279745365585 749094485838209809024189)
                ·
                  refine ⟨280910432189328678384071, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 749094485838209809024189 280910432189328678384071)
                  ·
                    rfl

theorem cell20_615455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 3, 2, 3].length) (baseStart_615455 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_615455 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_615455 prefixEnd_615455 := by exact prefixLift 615455
  have htrace : WordTrace (prefixWord ++ tailWord_615455) baseStart_615455 baseEnd_615455 := by
    simpa [prefixWord, tailWord_615455, baseEnd_615455] using wordTrace_append hprefix tailTrace_615455
  have hstable : (prefixWord ++ tailWord_615455).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_615455).length < 2 ^ (prefixWord ++ tailWord_615455).sum := by decide
  have hdescent : baseEnd_615455 < baseStart_615455 := by decide
  rcases family_descends (prefixWord ++ tailWord_615455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_615486 : List Nat := [4, 2, 1, 3, 1, 2, 1, 6]
def baseStart_615486 : Nat := 118140960795 + 615486 * 2 ^ 59
def prefixEnd_615486 : Nat := 4983230072969 + 3 ^ 40 * 615486 * 2
def baseEnd_615486 : Nat := 93641527144676782783537

theorem tailTrace_615486 : CollatzResearch.WordTrace tailWord_615486 prefixEnd_615486 93641527144676782783537 := by
  unfold tailWord_615486
  simp only [CollatzResearch.WordTrace]
  refine ⟨2806077331025851685643289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14965745765471208990097541 2806077331025851685643289)
  ·
    refine ⟨2104557998269388764232467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2806077331025851685643289 2104557998269388764232467)
    ·
      refine ⟨3156836997404083146348701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2104557998269388764232467 3156836997404083146348701)
      ·
        refine ⟨1183813874026531179880763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3156836997404083146348701 1183813874026531179880763)
        ·
          refine ⟨1775720811039796769821145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1183813874026531179880763 1775720811039796769821145)
          ·
            refine ⟨1331790608279847577365859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1775720811039796769821145 1331790608279847577365859)
            ·
              refine ⟨1997685912419771366048789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1331790608279847577365859 1997685912419771366048789)
              ·
                refine ⟨93641527144676782783537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1997685912419771366048789 93641527144676782783537)
                ·
                  rfl

theorem cell20_615486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 2, 1, 6].length) (baseStart_615486 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_615486 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_615486 prefixEnd_615486 := by exact prefixLift 615486
  have htrace : WordTrace (prefixWord ++ tailWord_615486) baseStart_615486 baseEnd_615486 := by
    simpa [prefixWord, tailWord_615486, baseEnd_615486] using wordTrace_append hprefix tailTrace_615486
  have hstable : (prefixWord ++ tailWord_615486).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_615486).length < 2 ^ (prefixWord ++ tailWord_615486).sum := by decide
  have hdescent : baseEnd_615486 < baseStart_615486 := by decide
  rcases family_descends (prefixWord ++ tailWord_615486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_615606 : List Nat := [5, 1, 3, 2, 1, 1, 2, 3, 2]
def baseStart_615606 : Nat := 118140960795 + 615606 * 2 ^ 59
def prefixEnd_615606 : Nat := 4983230072969 + 3 ^ 40 * 615606 * 2
def baseEnd_615606 : Nat := 280979352703843264350121

theorem tailTrace_615606 : CollatzResearch.WordTrace tailWord_615606 prefixEnd_615606 280979352703843264350121 := by
  unfold tailWord_615606
  simp only [CollatzResearch.WordTrace]
  refine ⟨1403312212985754623719667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 14968663605181382653009781 1403312212985754623719667)
  ·
    refine ⟨2104968319478631935579501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1403312212985754623719667 2104968319478631935579501)
    ·
      refine ⟨789363119804486975842313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2104968319478631935579501 789363119804486975842313)
      ·
        refine ⟨592022339853365231881735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 789363119804486975842313 592022339853365231881735)
        ·
          refine ⟨888033509780047847822603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 592022339853365231881735 888033509780047847822603)
          ·
            refine ⟨1332050264670071771733905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 888033509780047847822603 1332050264670071771733905)
            ·
              refine ⟨999037698502553828800429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1332050264670071771733905 999037698502553828800429)
              ·
                refine ⟨374639136938457685800161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 999037698502553828800429 374639136938457685800161)
                ·
                  refine ⟨280979352703843264350121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 374639136938457685800161 280979352703843264350121)
                  ·
                    rfl

theorem cell20_615606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 1, 2, 3, 2].length) (baseStart_615606 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_615606 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_615606 prefixEnd_615606 := by exact prefixLift 615606
  have htrace : WordTrace (prefixWord ++ tailWord_615606) baseStart_615606 baseEnd_615606 := by
    simpa [prefixWord, tailWord_615606, baseEnd_615606] using wordTrace_append hprefix tailTrace_615606
  have hstable : (prefixWord ++ tailWord_615606).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_615606).length < 2 ^ (prefixWord ++ tailWord_615606).sum := by decide
  have hdescent : baseEnd_615606 < baseStart_615606 := by decide
  rcases family_descends (prefixWord ++ tailWord_615606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_615642 : List Nat := [3, 1, 1, 2, 2, 1, 1, 9]
def baseStart_615642 : Nat := 118140960795 + 615642 * 2 ^ 59
def prefixEnd_615642 : Nat := 4983230072969 + 3 ^ 40 * 615642 * 2
def baseEnd_615642 : Nat := 93665261361595713049991

theorem tailTrace_615642 : CollatzResearch.WordTrace tailWord_615642 prefixEnd_615642 93665261361595713049991 := by
  unfold tailWord_615642
  simp only [CollatzResearch.WordTrace]
  refine ⟨5613577108910413031956295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14969538957094434751883453 5613577108910413031956295)
  ·
    refine ⟨8420365663365619547934443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5613577108910413031956295 8420365663365619547934443)
    ·
      refine ⟨12630548495048429321901665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8420365663365619547934443 12630548495048429321901665)
      ·
        refine ⟨9472911371286321991426249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12630548495048429321901665 9472911371286321991426249)
        ·
          refine ⟨7104683528464741493569687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9472911371286321991426249 7104683528464741493569687)
          ·
            refine ⟨10657025292697112240354531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7104683528464741493569687 10657025292697112240354531)
            ·
              refine ⟨15985537939045668360531797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10657025292697112240354531 15985537939045668360531797)
              ·
                refine ⟨93665261361595713049991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 15985537939045668360531797 93665261361595713049991)
                ·
                  rfl

theorem cell20_615642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 9].length) (baseStart_615642 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_615642 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_615642 prefixEnd_615642 := by exact prefixLift 615642
  have htrace : WordTrace (prefixWord ++ tailWord_615642) baseStart_615642 baseEnd_615642 := by
    simpa [prefixWord, tailWord_615642, baseEnd_615642] using wordTrace_append hprefix tailTrace_615642
  have hstable : (prefixWord ++ tailWord_615642).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_615642).length < 2 ^ (prefixWord ++ tailWord_615642).sum := by decide
  have hdescent : baseEnd_615642 < baseStart_615642 := by decide
  rcases family_descends (prefixWord ++ tailWord_615642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_615655 : List Nat := [1, 1, 5, 3, 2, 2, 2, 4]
def baseStart_615655 : Nat := 118140960795 + 615655 * 2 ^ 59
def prefixEnd_615655 : Nat := 4983230072969 + 3 ^ 40 * 615655 * 2
def baseEnd_615655 : Nat := 93667239213005623905529

theorem tailTrace_615655 : CollatzResearch.WordTrace tailWord_615655 prefixEnd_615655 93667239213005623905529 := by
  unfold tailWord_615655
  simp only [CollatzResearch.WordTrace]
  refine ⟨22454782584594555348048419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14969855056396370232032279 22454782584594555348048419)
  ·
    refine ⟨33682173876891833022072629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22454782584594555348048419 33682173876891833022072629)
    ·
      refine ⟨3157703800958609345819309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 33682173876891833022072629 3157703800958609345819309)
      ·
        refine ⟨1184138925359478504682241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3157703800958609345819309 1184138925359478504682241)
        ·
          refine ⟨888104194019608878511681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1184138925359478504682241 888104194019608878511681)
          ·
            refine ⟨666078145514706658883761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 888104194019608878511681 666078145514706658883761)
            ·
              refine ⟨499558609136029994162821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 666078145514706658883761 499558609136029994162821)
              ·
                refine ⟨93667239213005623905529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 499558609136029994162821 93667239213005623905529)
                ·
                  rfl

theorem cell20_615655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 2, 2, 4].length) (baseStart_615655 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_615655 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_615655 prefixEnd_615655 := by exact prefixLift 615655
  have htrace : WordTrace (prefixWord ++ tailWord_615655) baseStart_615655 baseEnd_615655 := by
    simpa [prefixWord, tailWord_615655, baseEnd_615655] using wordTrace_append hprefix tailTrace_615655
  have hstable : (prefixWord ++ tailWord_615655).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_615655).length < 2 ^ (prefixWord ++ tailWord_615655).sum := by decide
  have hdescent : baseEnd_615655 < baseStart_615655 := by decide
  rcases family_descends (prefixWord ++ tailWord_615655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_615659 : List Nat := [1, 1, 1, 1, 2, 6, 4, 4]
def baseStart_615659 : Nat := 118140960795 + 615659 * 2 ^ 59
def prefixEnd_615659 : Nat := 4983230072969 + 3 ^ 40 * 615659 * 2
def baseEnd_615659 : Nat := 93667847782670211861079

theorem tailTrace_615659 : CollatzResearch.WordTrace tailWord_615659 prefixEnd_615659 93667847782670211861079 := by
  unfold tailWord_615659
  simp only [CollatzResearch.WordTrace]
  refine ⟨22454928476580064031194031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14969952317720042687462687 22454928476580064031194031)
  ·
    refine ⟨33682392714870096046791047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22454928476580064031194031 33682392714870096046791047)
    ·
      refine ⟨50523589072305144070186571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33682392714870096046791047 50523589072305144070186571)
      ·
        refine ⟨75785383608457716105279857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50523589072305144070186571 75785383608457716105279857)
        ·
          refine ⟨56839037706343287078959893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 75785383608457716105279857 56839037706343287078959893)
          ·
            refine ⟨2664329892484841581826245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 56839037706343287078959893 2664329892484841581826245)
            ·
              refine ⟨499561854840907796592421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2664329892484841581826245 499561854840907796592421)
              ·
                refine ⟨93667847782670211861079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 499561854840907796592421 93667847782670211861079)
                ·
                  rfl

theorem cell20_615659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 4, 4].length) (baseStart_615659 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_615659 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_615659 prefixEnd_615659 := by exact prefixLift 615659
  have htrace : WordTrace (prefixWord ++ tailWord_615659) baseStart_615659 baseEnd_615659 := by
    simpa [prefixWord, tailWord_615659, baseEnd_615659] using wordTrace_append hprefix tailTrace_615659
  have hstable : (prefixWord ++ tailWord_615659).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_615659).length < 2 ^ (prefixWord ++ tailWord_615659).sum := by decide
  have hdescent : baseEnd_615659 < baseStart_615659 := by decide
  rcases family_descends (prefixWord ++ tailWord_615659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_615676 : List Nat := [2, 2, 2, 1, 6, 1, 6]
def baseStart_615676 : Nat := 118140960795 + 615676 * 2 ^ 59
def prefixEnd_615676 : Nat := 4983230072969 + 3 ^ 40 * 615676 * 2
def baseEnd_615676 : Nat := 31223478067914903557389

theorem tailTrace_615676 : CollatzResearch.WordTrace tailWord_615676 prefixEnd_615676 31223478067914903557389 := by
  unfold tailWord_615676
  simp only [CollatzResearch.WordTrace]
  refine ⟨11227774258759237967281441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14970365678345650623041921 11227774258759237967281441)
  ·
    refine ⟨8420830694069428475461081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11227774258759237967281441 8420830694069428475461081)
    ·
      refine ⟨6315623020552071356595811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8420830694069428475461081 6315623020552071356595811)
      ·
        refine ⟨9473434530828107034893717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6315623020552071356595811 9473434530828107034893717)
        ·
          refine ⟨444067243632567517260643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 9473434530828107034893717 444067243632567517260643)
          ·
            refine ⟨666100865448851275890965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 444067243632567517260643 666100865448851275890965)
            ·
              refine ⟨31223478067914903557389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 666100865448851275890965 31223478067914903557389)
              ·
                rfl

theorem cell20_615676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 6, 1, 6].length) (baseStart_615676 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_615676 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_615676 prefixEnd_615676 := by exact prefixLift 615676
  have htrace : WordTrace (prefixWord ++ tailWord_615676) baseStart_615676 baseEnd_615676 := by
    simpa [prefixWord, tailWord_615676, baseEnd_615676] using wordTrace_append hprefix tailTrace_615676
  have hstable : (prefixWord ++ tailWord_615676).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_615676).length < 2 ^ (prefixWord ++ tailWord_615676).sum := by decide
  have hdescent : baseEnd_615676 < baseStart_615676 := by decide
  rcases family_descends (prefixWord ++ tailWord_615676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_615728 : List Nat := [2, 1, 1, 1, 2, 2, 4, 5, 2]
def baseStart_615728 : Nat := 118140960795 + 615728 * 2 ^ 59
def prefixEnd_615728 : Nat := 4983230072969 + 3 ^ 40 * 615728 * 2
def baseEnd_615728 : Nat := 281035036828153062282955

theorem tailTrace_615728 : CollatzResearch.WordTrace tailWord_615728 prefixEnd_615728 281035036828153062282955 := by
  unfold tailWord_615728
  simp only [CollatzResearch.WordTrace]
  refine ⟨11228722556665044407727919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14971630075553392543637225 11228722556665044407727919)
  ·
    refine ⟨16843083834997566611591879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11228722556665044407727919 16843083834997566611591879)
    ·
      refine ⟨25264625752496349917387819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16843083834997566611591879 25264625752496349917387819)
      ·
        refine ⟨37896938628744524876081729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25264625752496349917387819 37896938628744524876081729)
        ·
          refine ⟨28422703971558393657061297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37896938628744524876081729 28422703971558393657061297)
          ·
            refine ⟨21317027978668795242795973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28422703971558393657061297 21317027978668795242795973)
            ·
              refine ⟨3996942746000399108024245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21317027978668795242795973 3996942746000399108024245)
              ·
                refine ⟨374713382437537416377273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3996942746000399108024245 374713382437537416377273)
                ·
                  refine ⟨281035036828153062282955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 374713382437537416377273 281035036828153062282955)
                  ·
                    rfl

theorem cell20_615728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 4, 5, 2].length) (baseStart_615728 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_615728 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_615728 prefixEnd_615728 := by exact prefixLift 615728
  have htrace : WordTrace (prefixWord ++ tailWord_615728) baseStart_615728 baseEnd_615728 := by
    simpa [prefixWord, tailWord_615728, baseEnd_615728] using wordTrace_append hprefix tailTrace_615728
  have hstable : (prefixWord ++ tailWord_615728).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_615728).length < 2 ^ (prefixWord ++ tailWord_615728).sum := by decide
  have hdescent : baseEnd_615728 < baseStart_615728 := by decide
  rcases family_descends (prefixWord ++ tailWord_615728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_615790 : List Nat := [4, 1, 2, 4, 1, 1, 7]
def baseStart_615790 : Nat := 118140960795 + 615790 * 2 ^ 59
def prefixEnd_615790 : Nat := 4983230072969 + 3 ^ 40 * 615790 * 2
def baseEnd_615790 : Nat := 31229259479728489135115

theorem tailTrace_615790 : CollatzResearch.WordTrace tailWord_615790 prefixEnd_615790 31229259479728489135115 := by
  unfold tailWord_615790
  simp only [CollatzResearch.WordTrace]
  refine ⟨2807463304888184175526603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14973137626070315602808549 2807463304888184175526603)
  ·
    refine ⟨4211194957332276263289905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2807463304888184175526603 4211194957332276263289905)
    ·
      refine ⟨3158396217999207197467429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4211194957332276263289905 3158396217999207197467429)
      ·
        refine ⟨592199290874851349525143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3158396217999207197467429 592199290874851349525143)
        ·
          refine ⟨888298936312277024287715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 592199290874851349525143 888298936312277024287715)
          ·
            refine ⟨1332448404468415536431573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 888298936312277024287715 1332448404468415536431573)
            ·
              refine ⟨31229259479728489135115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1332448404468415536431573 31229259479728489135115)
              ·
                rfl

theorem cell20_615790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 1, 7].length) (baseStart_615790 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_615790 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_615790 prefixEnd_615790 := by exact prefixLift 615790
  have htrace : WordTrace (prefixWord ++ tailWord_615790) baseStart_615790 baseEnd_615790 := by
    simpa [prefixWord, tailWord_615790, baseEnd_615790] using wordTrace_append hprefix tailTrace_615790
  have hstable : (prefixWord ++ tailWord_615790).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_615790).length < 2 ^ (prefixWord ++ tailWord_615790).sum := by decide
  have hdescent : baseEnd_615790 < baseStart_615790 := by decide
  rcases family_descends (prefixWord ++ tailWord_615790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_615794 : List Nat := [3, 2, 1, 2, 1, 2, 9]
def baseStart_615794 : Nat := 118140960795 + 615794 * 2 ^ 59
def prefixEnd_615794 : Nat := 4983230072969 + 3 ^ 40 * 615794 * 2
def baseEnd_615794 : Nat := 31229462336283351786965

theorem tailTrace_615794 : CollatzResearch.WordTrace tailWord_615794 prefixEnd_615794 31229462336283351786965 := by
  unfold tailWord_615794
  simp only [CollatzResearch.WordTrace]
  refine ⟨5614963082772745521839609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14973234887393988058238957 5614963082772745521839609)
  ·
    refine ⟨4211222312079559141379707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5614963082772745521839609 4211222312079559141379707)
    ·
      refine ⟨6316833468119338712069561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4211222312079559141379707 6316833468119338712069561)
      ·
        refine ⟨4737625101089504034052171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6316833468119338712069561 4737625101089504034052171)
        ·
          refine ⟨7106437651634256051078257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4737625101089504034052171 7106437651634256051078257)
          ·
            refine ⟨5329828238725692038308693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7106437651634256051078257 5329828238725692038308693)
            ·
              refine ⟨31229462336283351786965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 5329828238725692038308693 31229462336283351786965)
              ·
                rfl

theorem cell20_615794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 9].length) (baseStart_615794 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_615794 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_615794 prefixEnd_615794 := by exact prefixLift 615794
  have htrace : WordTrace (prefixWord ++ tailWord_615794) baseStart_615794 baseEnd_615794 := by
    simpa [prefixWord, tailWord_615794, baseEnd_615794] using wordTrace_append hprefix tailTrace_615794
  have hstable : (prefixWord ++ tailWord_615794).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_615794).length < 2 ^ (prefixWord ++ tailWord_615794).sum := by decide
  have hdescent : baseEnd_615794 < baseStart_615794 := by decide
  rcases family_descends (prefixWord ++ tailWord_615794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_615797 : List Nat := [1, 3, 4, 1, 3, 1, 1, 1, 5]
def baseStart_615797 : Nat := 118140960795 + 615797 * 2 ^ 59
def prefixEnd_615797 : Nat := 4983230072969 + 3 ^ 40 * 615797 * 2
def baseEnd_615797 : Nat := 281066530308295488982673

theorem tailTrace_615797 : CollatzResearch.WordTrace tailWord_615797 prefixEnd_615797 281066530308295488982673 := by
  unfold tailWord_615797
  simp only [CollatzResearch.WordTrace]
  refine ⟨22459961750080113599717645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14973307833386742399811763 22459961750080113599717645)
  ·
    refine ⟨8422485656280042599894117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22459961750080113599717645 8422485656280042599894117)
    ·
      refine ⟨1579216060552507987480147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8422485656280042599894117 1579216060552507987480147)
      ·
        refine ⟨2368824090828761981220221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1579216060552507987480147 2368824090828761981220221)
        ·
          refine ⟨888309034060785742957583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2368824090828761981220221 888309034060785742957583)
          ·
            refine ⟨1332463551091178614436375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 888309034060785742957583 1332463551091178614436375)
            ·
              refine ⟨1998695326636767921654563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1332463551091178614436375 1998695326636767921654563)
              ·
                refine ⟨2998042989955151882481845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1998695326636767921654563 2998042989955151882481845)
                ·
                  refine ⟨281066530308295488982673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2998042989955151882481845 281066530308295488982673)
                  ·
                    rfl

theorem cell20_615797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 1, 1, 1, 5].length) (baseStart_615797 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_615797 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_615797 prefixEnd_615797 := by exact prefixLift 615797
  have htrace : WordTrace (prefixWord ++ tailWord_615797) baseStart_615797 baseEnd_615797 := by
    simpa [prefixWord, tailWord_615797, baseEnd_615797] using wordTrace_append hprefix tailTrace_615797
  have hstable : (prefixWord ++ tailWord_615797).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_615797).length < 2 ^ (prefixWord ++ tailWord_615797).sum := by decide
  have hdescent : baseEnd_615797 < baseStart_615797 := by decide
  rcases family_descends (prefixWord ++ tailWord_615797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_615804 : List Nat := [2, 2, 2, 1, 1, 1, 3, 6, 2]
def baseStart_615804 : Nat := 118140960795 + 615804 * 2 ^ 59
def prefixEnd_615804 : Nat := 4983230072969 + 3 ^ 40 * 615804 * 2
def baseEnd_615804 : Nat := 281069725299034575749311

theorem tailTrace_615804 : CollatzResearch.WordTrace tailWord_615804 prefixEnd_615804 281069725299034575749311 := by
  unfold tailWord_615804
  simp only [CollatzResearch.WordTrace]
  refine ⟨11230108530527376897611233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14973478040703169196814977 11230108530527376897611233)
  ·
    refine ⟨8422581397895532673208425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11230108530527376897611233 8422581397895532673208425)
    ·
      refine ⟨6316936048421649504906319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8422581397895532673208425 6316936048421649504906319)
      ·
        refine ⟨9475404072632474257359479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6316936048421649504906319 9475404072632474257359479)
        ·
          refine ⟨14213106108948711386039219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9475404072632474257359479 14213106108948711386039219)
          ·
            refine ⟨21319659163423067079058829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14213106108948711386039219 21319659163423067079058829)
            ·
              refine ⟨7994872186283650154647061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21319659163423067079058829 7994872186283650154647061)
              ·
                refine ⟨374759633732046100999081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 7994872186283650154647061 374759633732046100999081)
                ·
                  refine ⟨281069725299034575749311, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 374759633732046100999081 281069725299034575749311)
                  ·
                    rfl

theorem cell20_615804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 3, 6, 2].length) (baseStart_615804 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_615804 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_615804 prefixEnd_615804 := by exact prefixLift 615804
  have htrace : WordTrace (prefixWord ++ tailWord_615804) baseStart_615804 baseEnd_615804 := by
    simpa [prefixWord, tailWord_615804, baseEnd_615804] using wordTrace_append hprefix tailTrace_615804
  have hstable : (prefixWord ++ tailWord_615804).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_615804).length < 2 ^ (prefixWord ++ tailWord_615804).sum := by decide
  have hdescent : baseEnd_615804 < baseStart_615804 := by decide
  rcases family_descends (prefixWord ++ tailWord_615804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_615828 : List Nat := [2, 4, 2, 1, 2, 1, 4, 4]
def baseStart_615828 : Nat := 118140960795 + 615828 * 2 ^ 59
def prefixEnd_615828 : Nat := 4983230072969 + 3 ^ 40 * 615828 * 2
def baseEnd_615828 : Nat := 93693559850999052983071

theorem tailTrace_615828 : CollatzResearch.WordTrace tailWord_615828 prefixEnd_615828 93693559850999052983071 := by
  unfold tailWord_615828
  simp only [CollatzResearch.WordTrace]
  refine ⟨11230546206483902947048069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14974061608645203929397425 11230546206483902947048069)
  ·
    refine ⟨2105727413715731802571513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11230546206483902947048069 2105727413715731802571513)
    ·
      refine ⟨1579295560286798851928635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2105727413715731802571513 1579295560286798851928635)
      ·
        refine ⟨2368943340430198277892953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1579295560286798851928635 2368943340430198277892953)
        ·
          refine ⟨1776707505322648708419715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2368943340430198277892953 1776707505322648708419715)
          ·
            refine ⟨2665061257983973062629573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1776707505322648708419715 2665061257983973062629573)
            ·
              refine ⟨499698985871994949243045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2665061257983973062629573 499698985871994949243045)
              ·
                refine ⟨93693559850999052983071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 499698985871994949243045 93693559850999052983071)
                ·
                  rfl

theorem cell20_615828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 4, 4].length) (baseStart_615828 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_615828 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_615828 prefixEnd_615828 := by exact prefixLift 615828
  have htrace : WordTrace (prefixWord ++ tailWord_615828) baseStart_615828 baseEnd_615828 := by
    simpa [prefixWord, tailWord_615828, baseEnd_615828] using wordTrace_append hprefix tailTrace_615828
  have hstable : (prefixWord ++ tailWord_615828).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_615828).length < 2 ^ (prefixWord ++ tailWord_615828).sum := by decide
  have hdescent : baseEnd_615828 < baseStart_615828 := by decide
  rcases family_descends (prefixWord ++ tailWord_615828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_615911 : List Nat := [1, 1, 5, 2, 1, 3, 2, 2, 3]
def baseStart_615911 : Nat := 118140960795 + 615911 * 2 ^ 59
def prefixEnd_615911 : Nat := 4983230072969 + 3 ^ 40 * 615911 * 2
def baseEnd_615911 : Nat := 281118563014617759182207

theorem tailTrace_615911 : CollatzResearch.WordTrace tailWord_615911 prefixEnd_615911 281118563014617759182207 := by
  unfold tailWord_615911
  simp only [CollatzResearch.WordTrace]
  refine ⟨22464119671667111069367587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14976079781111407379578391 22464119671667111069367587)
  ·
    refine ⟨33696179507500666604051381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22464119671667111069367587 33696179507500666604051381)
    ·
      refine ⟨3159016828828187494129817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 33696179507500666604051381 3159016828828187494129817)
      ·
        refine ⟨2369262621621140620597363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3159016828828187494129817 2369262621621140620597363)
        ·
          refine ⟨3553893932431710930896045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2369262621621140620597363 3553893932431710930896045)
          ·
            refine ⟨1332710224661891599086017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3553893932431710930896045 1332710224661891599086017)
            ·
              refine ⟨999532668496418699314513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1332710224661891599086017 999532668496418699314513)
              ·
                refine ⟨749649501372314024485885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 999532668496418699314513 749649501372314024485885)
                ·
                  refine ⟨281118563014617759182207, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 749649501372314024485885 281118563014617759182207)
                  ·
                    rfl

theorem cell20_615911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 3, 2, 2, 3].length) (baseStart_615911 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_615911 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_615911 prefixEnd_615911 := by exact prefixLift 615911
  have htrace : WordTrace (prefixWord ++ tailWord_615911) baseStart_615911 baseEnd_615911 := by
    simpa [prefixWord, tailWord_615911, baseEnd_615911] using wordTrace_append hprefix tailTrace_615911
  have hstable : (prefixWord ++ tailWord_615911).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_615911).length < 2 ^ (prefixWord ++ tailWord_615911).sum := by decide
  have hdescent : baseEnd_615911 < baseStart_615911 := by decide
  rcases family_descends (prefixWord ++ tailWord_615911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_615932 : List Nat := [2, 2, 2, 1, 2, 1, 4, 3, 3]
def baseStart_615932 : Nat := 118140960795 + 615932 * 2 ^ 59
def prefixEnd_615932 : Nat := 4983230072969 + 3 ^ 40 * 615932 * 2
def baseEnd_615932 : Nat := 281128147986835019482121

theorem tailTrace_615932 : CollatzResearch.WordTrace tailWord_615932 prefixEnd_615932 281128147986835019482121 := by
  unfold tailWord_615932
  simp only [CollatzResearch.WordTrace]
  refine ⟨11232442802295515827941025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14976590403060687770588033 11232442802295515827941025)
  ·
    refine ⟨8424332101721636870955769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11232442802295515827941025 8424332101721636870955769)
    ·
      refine ⟨6318249076291227653216827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8424332101721636870955769 6318249076291227653216827)
      ·
        refine ⟨9477373614436841479825241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6318249076291227653216827 9477373614436841479825241)
        ·
          refine ⟨7108030210827631109868931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9477373614436841479825241 7108030210827631109868931)
          ·
            refine ⟨10662045316241446664803397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7108030210827631109868931 10662045316241446664803397)
            ·
              refine ⟨1999133496795271249650637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10662045316241446664803397 1999133496795271249650637)
              ·
                refine ⟨749675061298226718618989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1999133496795271249650637 749675061298226718618989)
                ·
                  refine ⟨281128147986835019482121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 749675061298226718618989 281128147986835019482121)
                  ·
                    rfl

theorem cell20_615932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 4, 3, 3].length) (baseStart_615932 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_615932 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_615932 prefixEnd_615932 := by exact prefixLift 615932
  have htrace : WordTrace (prefixWord ++ tailWord_615932) baseStart_615932 baseEnd_615932 := by
    simpa [prefixWord, tailWord_615932, baseEnd_615932] using wordTrace_append hprefix tailTrace_615932
  have hstable : (prefixWord ++ tailWord_615932).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_615932).length < 2 ^ (prefixWord ++ tailWord_615932).sum := by decide
  have hdescent : baseEnd_615932 < baseStart_615932 := by decide
  rcases family_descends (prefixWord ++ tailWord_615932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_615953 : List Nat := [1, 2, 2, 1, 1, 2, 4, 2, 5]
def baseStart_615953 : Nat := 118140960795 + 615953 * 2 ^ 59
def prefixEnd_615953 : Nat := 4983230072969 + 3 ^ 40 * 615953 * 2
def baseEnd_615953 : Nat := 281137732959052279782035

theorem tailTrace_615953 : CollatzResearch.WordTrace tailWord_615953 prefixEnd_615953 281137732959052279782035 := by
  unfold tailWord_615953
  simp only [CollatzResearch.WordTrace]
  refine ⟨22465651537514952242396513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14977101025009968161597675 22465651537514952242396513)
  ·
    refine ⟨16849238653136214181797385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22465651537514952242396513 16849238653136214181797385)
    ·
      refine ⟨12636928989852160636348039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16849238653136214181797385 12636928989852160636348039)
      ·
        refine ⟨18955393484778240954522059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12636928989852160636348039 18955393484778240954522059)
        ·
          refine ⟨28433090227167361431783089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18955393484778240954522059 28433090227167361431783089)
          ·
            refine ⟨21324817670375521073837317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28433090227167361431783089 21324817670375521073837317)
            ·
              refine ⟨3998403313195410201344497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21324817670375521073837317 3998403313195410201344497)
              ·
                refine ⟨2998802484896557651008373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3998403313195410201344497 2998802484896557651008373)
                ·
                  refine ⟨281137732959052279782035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2998802484896557651008373 281137732959052279782035)
                  ·
                    rfl

theorem cell20_615953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 4, 2, 5].length) (baseStart_615953 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_615953 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_615953 prefixEnd_615953 := by exact prefixLift 615953
  have htrace : WordTrace (prefixWord ++ tailWord_615953) baseStart_615953 baseEnd_615953 := by
    simpa [prefixWord, tailWord_615953, baseEnd_615953] using wordTrace_append hprefix tailTrace_615953
  have hstable : (prefixWord ++ tailWord_615953).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_615953).length < 2 ^ (prefixWord ++ tailWord_615953).sum := by decide
  have hdescent : baseEnd_615953 < baseStart_615953 := by decide
  rcases family_descends (prefixWord ++ tailWord_615953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_615987 : List Nat := [1, 1, 1, 2, 4, 4, 3, 1, 3]
def baseStart_615987 : Nat := 118140960795 + 615987 * 2 ^ 59
def prefixEnd_615987 : Nat := 4983230072969 + 3 ^ 40 * 615987 * 2
def baseEnd_615987 : Nat := 281153251485499272648563

theorem tailTrace_615987 : CollatzResearch.WordTrace tailWord_615987 prefixEnd_615987 281153251485499272648563 := by
  unfold tailWord_615987
  simp only [CollatzResearch.WordTrace]
  refine ⟨22466891619391776049134215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14977927746261184032756143 22466891619391776049134215)
  ·
    refine ⟨33700337429087664073701323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22466891619391776049134215 33700337429087664073701323)
    ·
      refine ⟨50550506143631496110551985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33700337429087664073701323 50550506143631496110551985)
      ·
        refine ⟨37912879607723622082913989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50550506143631496110551985 37912879607723622082913989)
        ·
          refine ⟨7108664926448179140546373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 37912879607723622082913989 7108664926448179140546373)
          ·
            refine ⟨1332874673709033588852445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7108664926448179140546373 1332874673709033588852445)
            ·
              refine ⟨499828002640887595819667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1332874673709033588852445 499828002640887595819667)
              ·
                refine ⟨749742003961331393729501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 499828002640887595819667 749742003961331393729501)
                ·
                  refine ⟨281153251485499272648563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 749742003961331393729501 281153251485499272648563)
                  ·
                    rfl

theorem cell20_615987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 4, 3, 1, 3].length) (baseStart_615987 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_615987 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_615987 prefixEnd_615987 := by exact prefixLift 615987
  have htrace : WordTrace (prefixWord ++ tailWord_615987) baseStart_615987 baseEnd_615987 := by
    simpa [prefixWord, tailWord_615987, baseEnd_615987] using wordTrace_append hprefix tailTrace_615987
  have hstable : (prefixWord ++ tailWord_615987).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_615987).length < 2 ^ (prefixWord ++ tailWord_615987).sum := by decide
  have hdescent : baseEnd_615987 < baseStart_615987 := by decide
  rcases family_descends (prefixWord ++ tailWord_615987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_615997 : List Nat := [1, 4, 1, 3, 4, 1, 2, 4]
def baseStart_615997 : Nat := 118140960795 + 615997 * 2 ^ 59
def prefixEnd_615997 : Nat := 4983230072969 + 3 ^ 40 * 615997 * 2
def baseEnd_615997 : Nat := 93719271919327894105063

theorem tailTrace_615997 : CollatzResearch.WordTrace tailWord_615997 prefixEnd_615997 93719271919327894105063 := by
  unfold tailWord_615997
  simp only [CollatzResearch.WordTrace]
  refine ⟨22467256349355547756998245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14978170899570365171332163 22467256349355547756998245)
  ·
    refine ⟨4212610565504165204437171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 22467256349355547756998245 4212610565504165204437171)
    ·
      refine ⟨6318915848256247806655757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4212610565504165204437171 6318915848256247806655757)
      ·
        refine ⟨2369593443096092927495909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6318915848256247806655757 2369593443096092927495909)
        ·
          refine ⟨444298770580517423905483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2369593443096092927495909 444298770580517423905483)
          ·
            refine ⟨666448155870776135858225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 444298770580517423905483 666448155870776135858225)
            ·
              refine ⟨499836116903082101893669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 666448155870776135858225 499836116903082101893669)
              ·
                refine ⟨93719271919327894105063, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 499836116903082101893669 93719271919327894105063)
                ·
                  rfl

theorem cell20_615997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 4, 1, 2, 4].length) (baseStart_615997 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_615997 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_615997 prefixEnd_615997 := by exact prefixLift 615997
  have htrace : WordTrace (prefixWord ++ tailWord_615997) baseStart_615997 baseEnd_615997 := by
    simpa [prefixWord, tailWord_615997, baseEnd_615997] using wordTrace_append hprefix tailTrace_615997
  have hstable : (prefixWord ++ tailWord_615997).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_615997).length < 2 ^ (prefixWord ++ tailWord_615997).sum := by decide
  have hdescent : baseEnd_615997 < baseStart_615997 := by decide
  rcases family_descends (prefixWord ++ tailWord_615997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_616028 : List Nat := [2, 2, 4, 1, 2, 2, 3, 2, 2]
def baseStart_616028 : Nat := 118140960795 + 616028 * 2 ^ 59
def prefixEnd_616028 : Nat := 4983230072969 + 3 ^ 40 * 616028 * 2
def baseEnd_616028 : Nat := 281171965002685352281729

theorem tailTrace_616028 : CollatzResearch.WordTrace tailWord_616028 prefixEnd_616028 281171965002685352281729 := by
  unfold tailWord_616028
  simp only [CollatzResearch.WordTrace]
  refine ⟨11234193506121620025688369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14978924674828826700917825 11234193506121620025688369)
  ·
    refine ⟨8425645129591215019266277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11234193506121620025688369 8425645129591215019266277)
    ·
      refine ⟨1579808461798352816112427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8425645129591215019266277 1579808461798352816112427)
      ·
        refine ⟨2369712692697529224168641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1579808461798352816112427 2369712692697529224168641)
        ·
          refine ⟨1777284519523146918126481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2369712692697529224168641 1777284519523146918126481)
          ·
            refine ⟨1332963389642360188594861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1777284519523146918126481 1332963389642360188594861)
            ·
              refine ⟨499861271115885070723073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1332963389642360188594861 499861271115885070723073)
              ·
                refine ⟨374895953336913803042305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 499861271115885070723073 374895953336913803042305)
                ·
                  refine ⟨281171965002685352281729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 374895953336913803042305 281171965002685352281729)
                  ·
                    rfl

theorem cell20_616028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 2, 3, 2, 2].length) (baseStart_616028 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_616028 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_616028 prefixEnd_616028 := by exact prefixLift 616028
  have htrace : WordTrace (prefixWord ++ tailWord_616028) baseStart_616028 baseEnd_616028 := by
    simpa [prefixWord, tailWord_616028, baseEnd_616028] using wordTrace_append hprefix tailTrace_616028
  have hstable : (prefixWord ++ tailWord_616028).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_616028).length < 2 ^ (prefixWord ++ tailWord_616028).sum := by decide
  have hdescent : baseEnd_616028 < baseStart_616028 := by decide
  rcases family_descends (prefixWord ++ tailWord_616028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_616042 : List Nat := [3, 1, 3, 2, 1, 4, 2, 1, 3]
def baseStart_616042 : Nat := 118140960795 + 616042 * 2 ^ 59
def prefixEnd_616042 : Nat := 4983230072969 + 3 ^ 40 * 616042 * 2
def baseEnd_616042 : Nat := 281178354984163525815005

theorem tailTrace_616042 : CollatzResearch.WordTrace tailWord_616042 prefixEnd_616042 281178354984163525815005 := by
  unfold tailWord_616042
  simp only [CollatzResearch.WordTrace]
  refine ⟨5617224408548130110596595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14979265089461680294924253 5617224408548130110596595)
  ·
    refine ⟨8425836612822195165894893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5617224408548130110596595 8425836612822195165894893)
    ·
      refine ⟨3159688729808323187210585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8425836612822195165894893 3159688729808323187210585)
      ·
        refine ⟨2369766547356242390407939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3159688729808323187210585 2369766547356242390407939)
        ·
          refine ⟨3554649821034363585611909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2369766547356242390407939 3554649821034363585611909)
          ·
            refine ⟨666496841443943172302233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3554649821034363585611909 666496841443943172302233)
            ·
              refine ⟨499872631082957379226675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 666496841443943172302233 499872631082957379226675)
              ·
                refine ⟨749808946624436068840013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 499872631082957379226675 749808946624436068840013)
                ·
                  refine ⟨281178354984163525815005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 749808946624436068840013 281178354984163525815005)
                  ·
                    rfl

theorem cell20_616042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 4, 2, 1, 3].length) (baseStart_616042 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_616042 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_616042 prefixEnd_616042 := by exact prefixLift 616042
  have htrace : WordTrace (prefixWord ++ tailWord_616042) baseStart_616042 baseEnd_616042 := by
    simpa [prefixWord, tailWord_616042, baseEnd_616042] using wordTrace_append hprefix tailTrace_616042
  have hstable : (prefixWord ++ tailWord_616042).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_616042).length < 2 ^ (prefixWord ++ tailWord_616042).sum := by decide
  have hdescent : baseEnd_616042 < baseStart_616042 := by decide
  rcases family_descends (prefixWord ++ tailWord_616042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_616087 : List Nat := [1, 1, 3, 3, 2, 2, 4, 2, 2]
def baseStart_616087 : Nat := 118140960795 + 616087 * 2 ^ 59
def prefixEnd_616087 : Nat := 4983230072969 + 3 ^ 40 * 616087 * 2
def baseEnd_616087 : Nat := 281198894210343369314821

theorem tailTrace_616087 : CollatzResearch.WordTrace tailWord_616087 prefixEnd_616087 281198894210343369314821 := by
  unfold tailWord_616087
  simp only [CollatzResearch.WordTrace]
  refine ⟨22470538919029493127774515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14980359279352995418516343 22470538919029493127774515)
  ·
    refine ⟨33705808378544239691661773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22470538919029493127774515 33705808378544239691661773)
    ·
      refine ⟨12639678141954089884373165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33705808378544239691661773 12639678141954089884373165)
      ·
        refine ⟨4739879303232783706639937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12639678141954089884373165 4739879303232783706639937)
        ·
          refine ⟨3554909477424587779979953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4739879303232783706639937 3554909477424587779979953)
          ·
            refine ⟨2666182108068440834984965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3554909477424587779979953 2666182108068440834984965)
            ·
              refine ⟨499909145262832656559681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2666182108068440834984965 499909145262832656559681)
              ·
                refine ⟨374931858947124492419761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 499909145262832656559681 374931858947124492419761)
                ·
                  refine ⟨281198894210343369314821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 374931858947124492419761 281198894210343369314821)
                  ·
                    rfl

theorem cell20_616087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 4, 2, 2].length) (baseStart_616087 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_616087 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_616087 prefixEnd_616087 := by exact prefixLift 616087
  have htrace : WordTrace (prefixWord ++ tailWord_616087) baseStart_616087 baseEnd_616087 := by
    simpa [prefixWord, tailWord_616087, baseEnd_616087] using wordTrace_append hprefix tailTrace_616087
  have hstable : (prefixWord ++ tailWord_616087).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_616087).length < 2 ^ (prefixWord ++ tailWord_616087).sum := by decide
  have hdescent : baseEnd_616087 < baseStart_616087 := by decide
  rcases family_descends (prefixWord ++ tailWord_616087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_616094 : List Nat := [4, 3, 1, 1, 1, 4, 1, 5]
def baseStart_616094 : Nat := 118140960795 + 616094 * 2 ^ 59
def prefixEnd_616094 : Nat := 4983230072969 + 3 ^ 40 * 616094 * 2
def baseEnd_616094 : Nat := 93734029733694152027153

theorem tailTrace_616094 : CollatzResearch.WordTrace tailWord_616094 prefixEnd_616094 93734029733694152027153 := by
  unfold tailWord_616094
  simp only [CollatzResearch.WordTrace]
  refine ⟨2808849278750516665409917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14980529486669422215519557 2808849278750516665409917)
  ·
    refine ⟨1053318479531443749528719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2808849278750516665409917 1053318479531443749528719)
    ·
      refine ⟨1579977719297165624293079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1053318479531443749528719 1579977719297165624293079)
      ·
        refine ⟨2369966578945748436439619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1579977719297165624293079 2369966578945748436439619)
        ·
          refine ⟨3554949868418622654659429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2369966578945748436439619 3554949868418622654659429)
          ·
            refine ⟨666553100328491747748643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3554949868418622654659429 666553100328491747748643)
            ·
              refine ⟨999829650492737621622965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 666553100328491747748643 999829650492737621622965)
              ·
                refine ⟨93734029733694152027153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 999829650492737621622965 93734029733694152027153)
                ·
                  rfl

theorem cell20_616094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 4, 1, 5].length) (baseStart_616094 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_616094 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_616094 prefixEnd_616094 := by exact prefixLift 616094
  have htrace : WordTrace (prefixWord ++ tailWord_616094) baseStart_616094 baseEnd_616094 := by
    simpa [prefixWord, tailWord_616094, baseEnd_616094] using wordTrace_append hprefix tailTrace_616094
  have hstable : (prefixWord ++ tailWord_616094).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_616094).length < 2 ^ (prefixWord ++ tailWord_616094).sum := by decide
  have hdescent : baseEnd_616094 < baseStart_616094 := by decide
  rcases family_descends (prefixWord ++ tailWord_616094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_616104 : List Nat := [2, 1, 7, 1, 1, 1, 1, 2, 4]
def baseStart_616104 : Nat := 118140960795 + 616104 * 2 ^ 59
def prefixEnd_616104 : Nat := 4983230072969 + 3 ^ 40 * 616104 * 2
def baseEnd_616104 : Nat := 281206653473566865748085

theorem tailTrace_616104 : CollatzResearch.WordTrace tailWord_616104 prefixEnd_616104 281206653473566865748085 := by
  unfold tailWord_616104
  simp only [CollatzResearch.WordTrace]
  refine ⟨11235579479983952515571683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14980772639978603354095577 11235579479983952515571683)
  ·
    refine ⟨16853369219975928773357525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11235579479983952515571683 16853369219975928773357525)
    ·
      refine ⟨395000841093185830625567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 16853369219975928773357525 395000841093185830625567)
      ·
        refine ⟨592501261639778745938351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 395000841093185830625567 592501261639778745938351)
        ·
          refine ⟨888751892459668118907527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 592501261639778745938351 888751892459668118907527)
          ·
            refine ⟨1333127838689502178361291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 888751892459668118907527 1333127838689502178361291)
            ·
              refine ⟨1999691758034253267541937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1333127838689502178361291 1999691758034253267541937)
              ·
                refine ⟨1499768818525689950656453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1999691758034253267541937 1499768818525689950656453)
                ·
                  refine ⟨281206653473566865748085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1499768818525689950656453 281206653473566865748085)
                  ·
                    rfl

theorem cell20_616104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 1, 1, 2, 4].length) (baseStart_616104 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_616104 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_616104 prefixEnd_616104 := by exact prefixLift 616104
  have htrace : WordTrace (prefixWord ++ tailWord_616104) baseStart_616104 baseEnd_616104 := by
    simpa [prefixWord, tailWord_616104, baseEnd_616104] using wordTrace_append hprefix tailTrace_616104
  have hstable : (prefixWord ++ tailWord_616104).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_616104).length < 2 ^ (prefixWord ++ tailWord_616104).sum := by decide
  have hdescent : baseEnd_616104 < baseStart_616104 := by decide
  rcases family_descends (prefixWord ++ tailWord_616104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_616112 : List Nat := [2, 1, 1, 1, 2, 1, 5, 1, 6]
def baseStart_616112 : Nat := 118140960795 + 616112 * 2 ^ 59
def prefixEnd_616112 : Nat := 4983230072969 + 3 ^ 40 * 616112 * 2
def baseEnd_616112 : Nat := 281210304891554393481385

theorem tailTrace_616112 : CollatzResearch.WordTrace tailWord_616112 prefixEnd_616112 281210304891554393481385 := by
  unfold tailWord_616112
  simp only [CollatzResearch.WordTrace]
  refine ⟨11235725371969461198717295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14980967162625948264956393 11235725371969461198717295)
  ·
    refine ⟨16853588057954191798075943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11235725371969461198717295 16853588057954191798075943)
    ·
      refine ⟨25280382086931287697113915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16853588057954191798075943 25280382086931287697113915)
      ·
        refine ⟨37920573130396931545670873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25280382086931287697113915 37920573130396931545670873)
        ·
          refine ⟨28440429847797698659253155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37920573130396931545670873 28440429847797698659253155)
          ·
            refine ⟨42660644771696547988879733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28440429847797698659253155 42660644771696547988879733)
            ·
              refine ⟨3999435447346551373957475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 42660644771696547988879733 3999435447346551373957475)
              ·
                refine ⟨5999153171019827060936213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3999435447346551373957475 5999153171019827060936213)
                ·
                  refine ⟨281210304891554393481385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5999153171019827060936213 281210304891554393481385)
                  ·
                    rfl

theorem cell20_616112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 5, 1, 6].length) (baseStart_616112 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_616112 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_616112 prefixEnd_616112 := by exact prefixLift 616112
  have htrace : WordTrace (prefixWord ++ tailWord_616112) baseStart_616112 baseEnd_616112 := by
    simpa [prefixWord, tailWord_616112, baseEnd_616112] using wordTrace_append hprefix tailTrace_616112
  have hstable : (prefixWord ++ tailWord_616112).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_616112).length < 2 ^ (prefixWord ++ tailWord_616112).sum := by decide
  have hdescent : baseEnd_616112 < baseStart_616112 := by decide
  rcases family_descends (prefixWord ++ tailWord_616112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_616146 : List Nat := [3, 2, 2, 2, 2, 2, 2, 1, 4]
def baseStart_616146 : Nat := 118140960795 + 616146 * 2 ^ 59
def prefixEnd_616146 : Nat := 4983230072969 + 3 ^ 40 * 616146 * 2
def baseEnd_616146 : Nat := 281225823418001386347913

theorem tailTrace_616146 : CollatzResearch.WordTrace tailWord_616146 prefixEnd_616146 281225823418001386347913 := by
  unfold tailWord_616146
  simp only [CollatzResearch.WordTrace]
  refine ⟨5618172706453936551043073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14981793883877164136114861 5618172706453936551043073)
  ·
    refine ⟨4213629529840452413282305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5618172706453936551043073 4213629529840452413282305)
    ·
      refine ⟨3160222147380339309961729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4213629529840452413282305 3160222147380339309961729)
      ·
        refine ⟨2370166610535254482471297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3160222147380339309961729 2370166610535254482471297)
        ·
          refine ⟨1777624957901440861853473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2370166610535254482471297 1777624957901440861853473)
          ·
            refine ⟨1333218718426080646390105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1777624957901440861853473 1333218718426080646390105)
            ·
              refine ⟨999914038819560484792579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1333218718426080646390105 999914038819560484792579)
              ·
                refine ⟨1499871058229340727188869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 999914038819560484792579 1499871058229340727188869)
                ·
                  refine ⟨281225823418001386347913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1499871058229340727188869 281225823418001386347913)
                  ·
                    rfl

theorem cell20_616146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 2, 2, 1, 4].length) (baseStart_616146 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_616146 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_616146 prefixEnd_616146 := by exact prefixLift 616146
  have htrace : WordTrace (prefixWord ++ tailWord_616146) baseStart_616146 baseEnd_616146 := by
    simpa [prefixWord, tailWord_616146, baseEnd_616146] using wordTrace_append hprefix tailTrace_616146
  have hstable : (prefixWord ++ tailWord_616146).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_616146).length < 2 ^ (prefixWord ++ tailWord_616146).sum := by decide
  have hdescent : baseEnd_616146 < baseStart_616146 := by decide
  rcases family_descends (prefixWord ++ tailWord_616146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_616174 : List Nat := [4, 1, 2, 1, 1, 2, 3, 6]
def baseStart_616174 : Nat := 118140960795 + 616174 * 2 ^ 59
def prefixEnd_616174 : Nat := 4983230072969 + 3 ^ 40 * 616174 * 2
def baseEnd_616174 : Nat := 93746201126985911138155

theorem tailTrace_616174 : CollatzResearch.WordTrace tailWord_616174 prefixEnd_616174 93746201126985911138155 := by
  unfold tailWord_616174
  simp only [CollatzResearch.WordTrace]
  refine ⟨2809214008714288373273947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14982474713142871324127717 2809214008714288373273947)
  ·
    refine ⟨4213821013071432559910921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2809214008714288373273947 4213821013071432559910921)
    ·
      refine ⟨3160365759803574419933191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4213821013071432559910921 3160365759803574419933191)
      ·
        refine ⟨4740548639705361629899787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3160365759803574419933191 4740548639705361629899787)
        ·
          refine ⟨7110822959558042444849681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4740548639705361629899787 7110822959558042444849681)
          ·
            refine ⟨5333117219668531833637261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7110822959558042444849681 5333117219668531833637261)
            ·
              refine ⟨1999918957375699437613973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5333117219668531833637261 1999918957375699437613973)
              ·
                refine ⟨93746201126985911138155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1999918957375699437613973 93746201126985911138155)
                ·
                  rfl

theorem cell20_616174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 3, 6].length) (baseStart_616174 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_616174 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_616174 prefixEnd_616174 := by exact prefixLift 616174
  have htrace : WordTrace (prefixWord ++ tailWord_616174) baseStart_616174 baseEnd_616174 := by
    simpa [prefixWord, tailWord_616174, baseEnd_616174] using wordTrace_append hprefix tailTrace_616174
  have hstable : (prefixWord ++ tailWord_616174).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_616174).length < 2 ^ (prefixWord ++ tailWord_616174).sum := by decide
  have hdescent : baseEnd_616174 < baseStart_616174 := by decide
  rcases family_descends (prefixWord ++ tailWord_616174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_616195 : List Nat := [1, 1, 1, 3, 2, 2, 10]
def baseStart_616195 : Nat := 118140960795 + 616195 * 2 ^ 59
def prefixEnd_616195 : Nat := 4983230072969 + 3 ^ 40 * 616195 * 2
def baseEnd_616195 : Nat := 31249798705908332634931

theorem tailTrace_616195 : CollatzResearch.WordTrace tailWord_616195 prefixEnd_616195 31249798705908332634931 := by
  unfold tailWord_616195
  simp only [CollatzResearch.WordTrace]
  refine ⟨22474478002638227572706039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14982985335092151715137359 22474478002638227572706039)
  ·
    refine ⟨33711717003957341359059059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22474478002638227572706039 33711717003957341359059059)
    ·
      refine ⟨50567575505936012038588589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33711717003957341359059059 50567575505936012038588589)
      ·
        refine ⟨18962840814726004514470721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 50567575505936012038588589 18962840814726004514470721)
        ·
          refine ⟨14222130611044503385853041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18962840814726004514470721 14222130611044503385853041)
          ·
            refine ⟨10666597958283377539389781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14222130611044503385853041 10666597958283377539389781)
            ·
              refine ⟨31249798705908332634931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 10666597958283377539389781 31249798705908332634931)
              ·
                rfl

theorem cell20_616195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 10].length) (baseStart_616195 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_616195 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_616195 prefixEnd_616195 := by exact prefixLift 616195
  have htrace : WordTrace (prefixWord ++ tailWord_616195) baseStart_616195 baseEnd_616195 := by
    simpa [prefixWord, tailWord_616195, baseEnd_616195] using wordTrace_append hprefix tailTrace_616195
  have hstable : (prefixWord ++ tailWord_616195).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_616195).length < 2 ^ (prefixWord ++ tailWord_616195).sum := by decide
  have hdescent : baseEnd_616195 < baseStart_616195 := by decide
  rcases family_descends (prefixWord ++ tailWord_616195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_616215 : List Nat := [1, 1, 3, 4, 2, 1, 4, 1, 3]
def baseStart_616215 : Nat := 118140960795 + 616215 * 2 ^ 59
def prefixEnd_616215 : Nat := 4983230072969 + 3 ^ 40 * 616215 * 2
def baseEnd_616215 : Nat := 281257316898143813047631

theorem tailTrace_616215 : CollatzResearch.WordTrace tailWord_616215 prefixEnd_616215 281257316898143813047631 := by
  unfold tailWord_616215
  simp only [CollatzResearch.WordTrace]
  refine ⟨22475207462565770988434099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14983471641710513992289399 22475207462565770988434099)
  ·
    refine ⟨33712811193848656482651149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22475207462565770988434099 33712811193848656482651149)
    ·
      refine ⟨12642304197693246180994181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33712811193848656482651149 12642304197693246180994181)
      ·
        refine ⟨2370432037067483658936409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12642304197693246180994181 2370432037067483658936409)
        ·
          refine ⟨1777824027800612744202307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2370432037067483658936409 1777824027800612744202307)
          ·
            refine ⟨2666736041700919116303461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1777824027800612744202307 2666736041700919116303461)
            ·
              refine ⟨500013007818922334306899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2666736041700919116303461 500013007818922334306899)
              ·
                refine ⟨750019511728383501460349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 500013007818922334306899 750019511728383501460349)
                ·
                  refine ⟨281257316898143813047631, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 750019511728383501460349 281257316898143813047631)
                  ·
                    rfl

theorem cell20_616215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 4, 1, 3].length) (baseStart_616215 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_616215 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_616215 prefixEnd_616215 := by exact prefixLift 616215
  have htrace : WordTrace (prefixWord ++ tailWord_616215) baseStart_616215 baseEnd_616215 := by
    simpa [prefixWord, tailWord_616215, baseEnd_616215] using wordTrace_append hprefix tailTrace_616215
  have hstable : (prefixWord ++ tailWord_616215).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_616215).length < 2 ^ (prefixWord ++ tailWord_616215).sum := by decide
  have hdescent : baseEnd_616215 < baseStart_616215 := by decide
  rcases family_descends (prefixWord ++ tailWord_616215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_616219 : List Nat := [1, 1, 1, 1, 1, 1, 4, 7, 3]
def baseStart_616219 : Nat := 118140960795 + 616219 * 2 ^ 59
def prefixEnd_616219 : Nat := 4983230072969 + 3 ^ 40 * 616219 * 2
def baseEnd_616219 : Nat := 281259142607137576914281

theorem tailTrace_616219 : CollatzResearch.WordTrace tailWord_616219 prefixEnd_616219 281259142607137576914281 := by
  unfold tailWord_616219
  simp only [CollatzResearch.WordTrace]
  refine ⟨22475353354551279671579711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14983568903034186447719807 22475353354551279671579711)
  ·
    refine ⟨33713030031826919507369567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22475353354551279671579711 33713030031826919507369567)
    ·
      refine ⟨50569545047740379261054351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33713030031826919507369567 50569545047740379261054351)
      ·
        refine ⟨75854317571610568891581527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50569545047740379261054351 75854317571610568891581527)
        ·
          refine ⟨113781476357415853337372291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75854317571610568891581527 113781476357415853337372291)
          ·
            refine ⟨170672214536123780006058437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 113781476357415853337372291 170672214536123780006058437)
            ·
              refine ⟨32001040225523208751135957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 170672214536123780006058437 32001040225523208751135957)
              ·
                refine ⟨750024380285700205104749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 32001040225523208751135957 750024380285700205104749)
                ·
                  refine ⟨281259142607137576914281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 750024380285700205104749 281259142607137576914281)
                  ·
                    rfl

theorem cell20_616219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 7, 3].length) (baseStart_616219 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_616219 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_616219 prefixEnd_616219 := by exact prefixLift 616219
  have htrace : WordTrace (prefixWord ++ tailWord_616219) baseStart_616219 baseEnd_616219 := by
    simpa [prefixWord, tailWord_616219, baseEnd_616219] using wordTrace_append hprefix tailTrace_616219
  have hstable : (prefixWord ++ tailWord_616219).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_616219).length < 2 ^ (prefixWord ++ tailWord_616219).sum := by decide
  have hdescent : baseEnd_616219 < baseStart_616219 := by decide
  rcases family_descends (prefixWord ++ tailWord_616219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_616253 : List Nat := [1, 4, 1, 4, 1, 2, 2, 2, 3]
def baseStart_616253 : Nat := 118140960795 + 616253 * 2 ^ 59
def prefixEnd_616253 : Nat := 4983230072969 + 3 ^ 40 * 616253 * 2
def baseEnd_616253 : Nat := 281274661133584569780809

theorem tailTrace_616253 : CollatzResearch.WordTrace tailWord_616253 prefixEnd_616253 281274661133584569780809 := by
  unfold tailWord_616253
  simp only [CollatzResearch.WordTrace]
  refine ⟨22476593436428103478317413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14984395624285402318878275 22476593436428103478317413)
  ·
    refine ⟨4214361269330269402184515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 22476593436428103478317413 4214361269330269402184515)
    ·
      refine ⟨6321541903995404103276773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4214361269330269402184515 6321541903995404103276773)
      ·
        refine ⟨1185289106999138269364395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6321541903995404103276773 1185289106999138269364395)
        ·
          refine ⟨1777933660498707404046593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1185289106999138269364395 1777933660498707404046593)
          ·
            refine ⟨1333450245374030553034945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1777933660498707404046593 1333450245374030553034945)
            ·
              refine ⟨1000087684030522914776209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1333450245374030553034945 1000087684030522914776209)
              ·
                refine ⟨750065763022892186082157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1000087684030522914776209 750065763022892186082157)
                ·
                  refine ⟨281274661133584569780809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 750065763022892186082157 281274661133584569780809)
                  ·
                    rfl

theorem cell20_616253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 2, 2, 2, 3].length) (baseStart_616253 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_616253 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_616253 prefixEnd_616253 := by exact prefixLift 616253
  have htrace : WordTrace (prefixWord ++ tailWord_616253) baseStart_616253 baseEnd_616253 := by
    simpa [prefixWord, tailWord_616253, baseEnd_616253] using wordTrace_append hprefix tailTrace_616253
  have hstable : (prefixWord ++ tailWord_616253).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_616253).length < 2 ^ (prefixWord ++ tailWord_616253).sum := by decide
  have hdescent : baseEnd_616253 < baseStart_616253 := by decide
  rcases family_descends (prefixWord ++ tailWord_616253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_616274 : List Nat := [3, 2, 2, 1, 1, 3, 2, 3, 3]
def baseStart_616274 : Nat := 118140960795 + 616274 * 2 ^ 59
def prefixEnd_616274 : Nat := 4983230072969 + 3 ^ 40 * 616274 * 2
def baseEnd_616274 : Nat := 281284246105801830080723

theorem tailTrace_616274 : CollatzResearch.WordTrace tailWord_616274 prefixEnd_616274 281284246105801830080723 := by
  unfold tailWord_616274
  simp only [CollatzResearch.WordTrace]
  refine ⟨5619339842338006016207969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14984906246234682709887917 5619339842338006016207969)
  ·
    refine ⟨4214504881753504512155977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5619339842338006016207969 4214504881753504512155977)
    ·
      refine ⟨3160878661315128384116983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4214504881753504512155977 3160878661315128384116983)
      ·
        refine ⟨4741317991972692576175475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3160878661315128384116983 4741317991972692576175475)
        ·
          refine ⟨7111976987959038864263213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4741317991972692576175475 7111976987959038864263213)
          ·
            refine ⟨2666991370484639574098705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7111976987959038864263213 2666991370484639574098705)
            ·
              refine ⟨2000243527863479680574029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2666991370484639574098705 2000243527863479680574029)
              ·
                refine ⟨750091322948804880215261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2000243527863479680574029 750091322948804880215261)
                ·
                  refine ⟨281284246105801830080723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 750091322948804880215261 281284246105801830080723)
                  ·
                    rfl

theorem cell20_616274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 2, 3, 3].length) (baseStart_616274 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_616274 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_616274 prefixEnd_616274 := by exact prefixLift 616274
  have htrace : WordTrace (prefixWord ++ tailWord_616274) baseStart_616274 baseEnd_616274 := by
    simpa [prefixWord, tailWord_616274, baseEnd_616274] using wordTrace_append hprefix tailTrace_616274
  have hstable : (prefixWord ++ tailWord_616274).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_616274).length < 2 ^ (prefixWord ++ tailWord_616274).sum := by decide
  have hdescent : baseEnd_616274 < baseStart_616274 := by decide
  rcases family_descends (prefixWord ++ tailWord_616274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_616284 : List Nat := [2, 2, 4, 2, 2, 1, 3, 4]
def baseStart_616284 : Nat := 118140960795 + 616284 * 2 ^ 59
def prefixEnd_616284 : Nat := 4983230072969 + 3 ^ 40 * 616284 * 2
def baseEnd_616284 : Nat := 93762936792762079915783

theorem tailTrace_616284 : CollatzResearch.WordTrace tailWord_616284 prefixEnd_616284 93762936792762079915783 := by
  unfold tailWord_616284
  simp only [CollatzResearch.WordTrace]
  refine ⟨11238862049657897886347953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14985149399543863848463937 11238862049657897886347953)
  ·
    refine ⟨8429146537243423414760965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11238862049657897886347953 8429146537243423414760965)
    ·
      refine ⟨1580464975733141890267681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8429146537243423414760965 1580464975733141890267681)
      ·
        refine ⟨1185348731799856417700761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1580464975733141890267681 1185348731799856417700761)
        ·
          refine ⟨889011548849892313275571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1185348731799856417700761 889011548849892313275571)
          ·
            refine ⟨1333517323274838469913357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 889011548849892313275571 1333517323274838469913357)
            ·
              refine ⟨500068996228064426217509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1333517323274838469913357 500068996228064426217509)
              ·
                refine ⟨93762936792762079915783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 500068996228064426217509 93762936792762079915783)
                ·
                  rfl

theorem cell20_616284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 1, 3, 4].length) (baseStart_616284 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_616284 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_616284 prefixEnd_616284 := by exact prefixLift 616284
  have htrace : WordTrace (prefixWord ++ tailWord_616284) baseStart_616284 baseEnd_616284 := by
    simpa [prefixWord, tailWord_616284, baseEnd_616284] using wordTrace_append hprefix tailTrace_616284
  have hstable : (prefixWord ++ tailWord_616284).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_616284).length < 2 ^ (prefixWord ++ tailWord_616284).sum := by decide
  have hdescent : baseEnd_616284 < baseStart_616284 := by decide
  rcases family_descends (prefixWord ++ tailWord_616284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_616295 : List Nat := [1, 1, 5, 1, 2, 1, 2, 2, 5]
def baseStart_616295 : Nat := 118140960795 + 616295 * 2 ^ 59
def prefixEnd_616295 : Nat := 4983230072969 + 3 ^ 40 * 616295 * 2
def baseEnd_616295 : Nat := 281293831078019090380637

theorem tailTrace_616295 : CollatzResearch.WordTrace tailWord_616295 prefixEnd_616295 281293831078019090380637 := by
  unfold tailWord_616295
  simp only [CollatzResearch.WordTrace]
  refine ⟨22478125302275944651346339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14985416868183963100897559 22478125302275944651346339)
  ·
    refine ⟨33717187953413916977019509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22478125302275944651346339 33717187953413916977019509)
    ·
      refine ⟨3160986370632554716595579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 33717187953413916977019509 3160986370632554716595579)
      ·
        refine ⟨4741479555948832074893369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3160986370632554716595579 4741479555948832074893369)
        ·
          refine ⟨3556109666961624056170027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4741479555948832074893369 3556109666961624056170027)
          ·
            refine ⟨5334164500442436084255041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3556109666961624056170027 5334164500442436084255041)
            ·
              refine ⟨4000623375331827063191281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5334164500442436084255041 4000623375331827063191281)
              ·
                refine ⟨3000467531498870297393461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4000623375331827063191281 3000467531498870297393461)
                ·
                  refine ⟨281293831078019090380637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3000467531498870297393461 281293831078019090380637)
                  ·
                    rfl

theorem cell20_616295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 2, 2, 5].length) (baseStart_616295 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_616295 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_616295 prefixEnd_616295 := by exact prefixLift 616295
  have htrace : WordTrace (prefixWord ++ tailWord_616295) baseStart_616295 baseEnd_616295 := by
    simpa [prefixWord, tailWord_616295, baseEnd_616295] using wordTrace_append hprefix tailTrace_616295
  have hstable : (prefixWord ++ tailWord_616295).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_616295).length < 2 ^ (prefixWord ++ tailWord_616295).sum := by decide
  have hdescent : baseEnd_616295 < baseStart_616295 := by decide
  rcases family_descends (prefixWord ++ tailWord_616295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_616343 : List Nat := [1, 1, 3, 3, 1, 5, 2, 4]
def baseStart_616343 : Nat := 118140960795 + 616343 * 2 ^ 59
def prefixEnd_616343 : Nat := 4983230072969 + 3 ^ 40 * 616343 * 2
def baseEnd_616343 : Nat := 93771913195314752260147

theorem tailTrace_616343 : CollatzResearch.WordTrace tailWord_616343 prefixEnd_616343 93771913195314752260147 := by
  unfold tailWord_616343
  simp only [CollatzResearch.WordTrace]
  refine ⟨22479876006102048849093683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14986584004068032566062455 22479876006102048849093683)
  ·
    refine ⟨33719814009153073273640525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22479876006102048849093683 33719814009153073273640525)
    ·
      refine ⟨12644930253432402477615197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33719814009153073273640525 12644930253432402477615197)
      ·
        refine ⟨4741848845037150929105699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12644930253432402477615197 4741848845037150929105699)
        ·
          refine ⟨7112773267555726393658549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4741848845037150929105699 7112773267555726393658549)
          ·
            refine ⟨666822493833349349405489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 7112773267555726393658549 666822493833349349405489)
            ·
              refine ⟨500116870375012012054117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 666822493833349349405489 500116870375012012054117)
              ·
                refine ⟨93771913195314752260147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 500116870375012012054117 93771913195314752260147)
                ·
                  rfl

theorem cell20_616343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 5, 2, 4].length) (baseStart_616343 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_616343 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_616343 prefixEnd_616343 := by exact prefixLift 616343
  have htrace : WordTrace (prefixWord ++ tailWord_616343) baseStart_616343 baseEnd_616343 := by
    simpa [prefixWord, tailWord_616343, baseEnd_616343] using wordTrace_append hprefix tailTrace_616343
  have hstable : (prefixWord ++ tailWord_616343).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_616343).length < 2 ^ (prefixWord ++ tailWord_616343).sum := by decide
  have hdescent : baseEnd_616343 < baseStart_616343 := by decide
  rcases family_descends (prefixWord ++ tailWord_616343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_616360 : List Nat := [2, 1, 6, 2, 1, 2, 6]
def baseStart_616360 : Nat := 118140960795 + 616360 * 2 ^ 59
def prefixEnd_616360 : Nat := 4983230072969 + 3 ^ 40 * 616360 * 2
def baseEnd_616360 : Nat := 31258166538796417023745

theorem tailTrace_616360 : CollatzResearch.WordTrace tailWord_616360 prefixEnd_616360 31258166538796417023745 := by
  unfold tailWord_616360
  simp only [CollatzResearch.WordTrace]
  refine ⟨11240248023520230376231267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14986997364693640501641689 11240248023520230376231267)
  ·
    refine ⟨16860372035280345564346901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11240248023520230376231267 16860372035280345564346901)
    ·
      refine ⟨790329939153766198328761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 16860372035280345564346901 790329939153766198328761)
      ·
        refine ⟨592747454365324648746571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 790329939153766198328761 592747454365324648746571)
        ·
          refine ⟨889121181547986973119857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 592747454365324648746571 889121181547986973119857)
          ·
            refine ⟨666840886160990229839893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 889121181547986973119857 666840886160990229839893)
            ·
              refine ⟨31258166538796417023745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 666840886160990229839893 31258166538796417023745)
              ·
                rfl

theorem cell20_616360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 2, 6].length) (baseStart_616360 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_616360 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_616360 prefixEnd_616360 := by exact prefixLift 616360
  have htrace : WordTrace (prefixWord ++ tailWord_616360) baseStart_616360 baseEnd_616360 := by
    simpa [prefixWord, tailWord_616360, baseEnd_616360] using wordTrace_append hprefix tailTrace_616360
  have hstable : (prefixWord ++ tailWord_616360).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_616360).length < 2 ^ (prefixWord ++ tailWord_616360).sum := by decide
  have hdescent : baseEnd_616360 < baseStart_616360 := by decide
  rcases family_descends (prefixWord ++ tailWord_616360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_616366 : List Nat := [4, 1, 5, 1, 1, 1, 3, 2, 2]
def baseStart_616366 : Nat := 118140960795 + 616366 * 2 ^ 59
def prefixEnd_616366 : Nat := 4983230072969 + 3 ^ 40 * 616366 * 2
def baseEnd_616366 : Nat := 281326237412658399013681

theorem tailTrace_616366 : CollatzResearch.WordTrace tailWord_616366 prefixEnd_616366 281326237412658399013681 := by
  unfold tailWord_616366
  simp only [CollatzResearch.WordTrace]
  refine ⟨2810089360627340472147619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14987143256679149184787301 2810089360627340472147619)
  ·
    refine ⟨4215134040941010708221429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2810089360627340472147619 4215134040941010708221429)
    ·
      refine ⟨395168816338219753895759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 4215134040941010708221429 395168816338219753895759)
      ·
        refine ⟨592753224507329630843639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 395168816338219753895759 592753224507329630843639)
        ·
          refine ⟨889129836760994446265459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 592753224507329630843639 889129836760994446265459)
          ·
            refine ⟨1333694755141491669398189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 889129836760994446265459 1333694755141491669398189)
            ·
              refine ⟨500135533178059376024321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1333694755141491669398189 500135533178059376024321)
              ·
                refine ⟨375101649883544532018241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 500135533178059376024321 375101649883544532018241)
                ·
                  refine ⟨281326237412658399013681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 375101649883544532018241 281326237412658399013681)
                  ·
                    rfl

theorem cell20_616366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 1, 3, 2, 2].length) (baseStart_616366 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_616366 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_616366 prefixEnd_616366 := by exact prefixLift 616366
  have htrace : WordTrace (prefixWord ++ tailWord_616366) baseStart_616366 baseEnd_616366 := by
    simpa [prefixWord, tailWord_616366, baseEnd_616366] using wordTrace_append hprefix tailTrace_616366
  have hstable : (prefixWord ++ tailWord_616366).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_616366).length < 2 ^ (prefixWord ++ tailWord_616366).sum := by decide
  have hdescent : baseEnd_616366 < baseStart_616366 := by decide
  rcases family_descends (prefixWord ++ tailWord_616366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_616371 : List Nat := [1, 1, 1, 2, 3, 1, 4, 4, 3]
def baseStart_616371 : Nat := 118140960795 + 616371 * 2 ^ 59
def prefixEnd_616371 : Nat := 4983230072969 + 3 ^ 40 * 616371 * 2
def baseEnd_616371 : Nat := 281328519548900603846993

theorem tailTrace_616371 : CollatzResearch.WordTrace tailWord_616371 prefixEnd_616371 281328519548900603846993 := by
  unfold tailWord_616371
  simp only [CollatzResearch.WordTrace]
  refine ⟨22480897250000609631112967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14987264833333739754075311 22480897250000609631112967)
  ·
    refine ⟨33721345875000914446669451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22480897250000609631112967 33721345875000914446669451)
    ·
      refine ⟨50582018812501371670004177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33721345875000914446669451 50582018812501371670004177)
      ·
        refine ⟨37936514109376028752503133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50582018812501371670004177 37936514109376028752503133)
        ·
          refine ⟨14226192791016010782188675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37936514109376028752503133 14226192791016010782188675)
          ·
            refine ⟨21339289186524016173283013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14226192791016010782188675 21339289186524016173283013)
            ·
              refine ⟨4001116722473253032490565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21339289186524016173283013 4001116722473253032490565)
              ·
                refine ⟨750209385463734943591981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4001116722473253032490565 750209385463734943591981)
                ·
                  refine ⟨281328519548900603846993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 750209385463734943591981 281328519548900603846993)
                  ·
                    rfl

theorem cell20_616371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 4, 4, 3].length) (baseStart_616371 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_616371 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_616371 prefixEnd_616371 := by exact prefixLift 616371
  have htrace : WordTrace (prefixWord ++ tailWord_616371) baseStart_616371 baseEnd_616371 := by
    simpa [prefixWord, tailWord_616371, baseEnd_616371] using wordTrace_append hprefix tailTrace_616371
  have hstable : (prefixWord ++ tailWord_616371).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_616371).length < 2 ^ (prefixWord ++ tailWord_616371).sum := by decide
  have hdescent : baseEnd_616371 < baseStart_616371 := by decide
  rcases family_descends (prefixWord ++ tailWord_616371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_616378 : List Nat := [3, 1, 1, 1, 2, 1, 2, 5, 4]
def baseStart_616378 : Nat := 118140960795 + 616378 * 2 ^ 59
def prefixEnd_616378 : Nat := 4983230072969 + 3 ^ 40 * 616378 * 2
def baseEnd_616378 : Nat := 281331714539639690613631

theorem tailTrace_616378 : CollatzResearch.WordTrace tailWord_616378 prefixEnd_616378 281331714539639690613631 := by
  unfold tailWord_616378
  simp only [CollatzResearch.WordTrace]
  refine ⟨5620288140243812456654447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14987435040650166551078525 5620288140243812456654447)
  ·
    refine ⟨8430432210365718684981671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5620288140243812456654447 8430432210365718684981671)
    ·
      refine ⟨12645648315548578027472507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8430432210365718684981671 12645648315548578027472507)
      ·
        refine ⟨18968472473322867041208761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12645648315548578027472507 18968472473322867041208761)
        ·
          refine ⟨14226354354992150280906571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18968472473322867041208761 14226354354992150280906571)
          ·
            refine ⟨21339531532488225421359857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14226354354992150280906571 21339531532488225421359857)
            ·
              refine ⟨16004648649366169066019893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21339531532488225421359857 16004648649366169066019893)
              ·
                refine ⟨1500435810878078349939365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 16004648649366169066019893 1500435810878078349939365)
                ·
                  refine ⟨281331714539639690613631, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1500435810878078349939365 281331714539639690613631)
                  ·
                    rfl

theorem cell20_616378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 5, 4].length) (baseStart_616378 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_616378 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_616378 prefixEnd_616378 := by exact prefixLift 616378
  have htrace : WordTrace (prefixWord ++ tailWord_616378) baseStart_616378 baseEnd_616378 := by
    simpa [prefixWord, tailWord_616378, baseEnd_616378] using wordTrace_append hprefix tailTrace_616378
  have hstable : (prefixWord ++ tailWord_616378).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_616378).length < 2 ^ (prefixWord ++ tailWord_616378).sum := by decide
  have hdescent : baseEnd_616378 < baseStart_616378 := by decide
  rcases family_descends (prefixWord ++ tailWord_616378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_616423 : List Nat := [1, 1, 5, 2, 11]
def baseStart_616423 : Nat := 118140960795 + 616423 * 2 ^ 59
def prefixEnd_616423 : Nat := 4983230072969 + 3 ^ 40 * 616423 * 2
def baseEnd_616423 : Nat := 3473484614392833754487

theorem tailTrace_616423 : CollatzResearch.WordTrace tailWord_616423 prefixEnd_616423 3473484614392833754487 := by
  unfold tailWord_616423
  simp only [CollatzResearch.WordTrace]
  refine ⟨22482793845812222512005923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14988529230541481674670615 22482793845812222512005923)
  ·
    refine ⟨33724190768718333768008885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22482793845812222512005923 33724190768718333768008885)
    ·
      refine ⟨3161642884567343790750833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 33724190768718333768008885 3161642884567343790750833)
      ·
        refine ⟨2371232163425507843063125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3161642884567343790750833 2371232163425507843063125)
        ·
          refine ⟨3473484614392833754487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 11 2371232163425507843063125 3473484614392833754487)
          ·
            rfl

theorem cell20_616423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 11].length) (baseStart_616423 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_616423 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_616423 prefixEnd_616423 := by exact prefixLift 616423
  have htrace : WordTrace (prefixWord ++ tailWord_616423) baseStart_616423 baseEnd_616423 := by
    simpa [prefixWord, tailWord_616423, baseEnd_616423] using wordTrace_append hprefix tailTrace_616423
  have hstable : (prefixWord ++ tailWord_616423).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_616423).length < 2 ^ (prefixWord ++ tailWord_616423).sum := by decide
  have hdescent : baseEnd_616423 < baseStart_616423 := by decide
  rcases family_descends (prefixWord ++ tailWord_616423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_616426 : List Nat := [3, 1, 3, 1, 2, 1, 4, 2, 3]
def baseStart_616426 : Nat := 118140960795 + 616426 * 2 ^ 59
def prefixEnd_616426 : Nat := 4983230072969 + 3 ^ 40 * 616426 * 2
def baseEnd_616426 : Nat := 281353623047564857013435

theorem tailTrace_616426 : CollatzResearch.WordTrace tailWord_616426 prefixEnd_616426 281353623047564857013435 := by
  unfold tailWord_616426
  simp only [CollatzResearch.WordTrace]
  refine ⟨5620725816200338506091283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14988602176534236016243421 5620725816200338506091283)
  ·
    refine ⟨8431088724300507759136925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5620725816200338506091283 8431088724300507759136925)
    ·
      refine ⟨3161658271612690409676347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8431088724300507759136925 3161658271612690409676347)
      ·
        refine ⟨4742487407419035614514521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3161658271612690409676347 4742487407419035614514521)
        ·
          refine ⟨3556865555564276710885891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4742487407419035614514521 3556865555564276710885891)
          ·
            refine ⟨5335298333346415066328837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3556865555564276710885891 5335298333346415066328837)
            ·
              refine ⟨1000368437502452824936657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5335298333346415066328837 1000368437502452824936657)
              ·
                refine ⟨750276328126839618702493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1000368437502452824936657 750276328126839618702493)
                ·
                  refine ⟨281353623047564857013435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 750276328126839618702493 281353623047564857013435)
                  ·
                    rfl

theorem cell20_616426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 4, 2, 3].length) (baseStart_616426 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_616426 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_616426 prefixEnd_616426 := by exact prefixLift 616426
  have htrace : WordTrace (prefixWord ++ tailWord_616426) baseStart_616426 baseEnd_616426 := by
    simpa [prefixWord, tailWord_616426, baseEnd_616426] using wordTrace_append hprefix tailTrace_616426
  have hstable : (prefixWord ++ tailWord_616426).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_616426).length < 2 ^ (prefixWord ++ tailWord_616426).sum := by decide
  have hdescent : baseEnd_616426 < baseStart_616426 := by decide
  rcases family_descends (prefixWord ++ tailWord_616426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_616481 : List Nat := [1, 2, 3, 2, 4, 2, 1, 2, 3]
def baseStart_616481 : Nat := 118140960795 + 616481 * 2 ^ 59
def prefixEnd_616481 : Nat := 4983230072969 + 3 ^ 40 * 616481 * 2
def baseEnd_616481 : Nat := 281378726546229110179877

theorem tailTrace_616481 : CollatzResearch.WordTrace tailWord_616481 prefixEnd_616481 281378726546229110179877 := by
  unfold tailWord_616481
  simp only [CollatzResearch.WordTrace]
  refine ⟨22484909279602098417617297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14989939519734732278411531 22484909279602098417617297)
  ·
    refine ⟨16863681959701573813212973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22484909279602098417617297 16863681959701573813212973)
    ·
      refine ⟨6323880734888090179954865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16863681959701573813212973 6323880734888090179954865)
      ·
        refine ⟨4742910551166067634966149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6323880734888090179954865 4742910551166067634966149)
        ·
          refine ⟨889295728343637681556153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4742910551166067634966149 889295728343637681556153)
          ·
            refine ⟨666971796257728261167115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 889295728343637681556153 666971796257728261167115)
            ·
              refine ⟨1000457694386592391750673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 666971796257728261167115 1000457694386592391750673)
              ·
                refine ⟨750343270789944293813005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1000457694386592391750673 750343270789944293813005)
                ·
                  refine ⟨281378726546229110179877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 750343270789944293813005 281378726546229110179877)
                  ·
                    rfl

theorem cell20_616481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 2, 1, 2, 3].length) (baseStart_616481 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_616481 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_616481 prefixEnd_616481 := by exact prefixLift 616481
  have htrace : WordTrace (prefixWord ++ tailWord_616481) baseStart_616481 baseEnd_616481 := by
    simpa [prefixWord, tailWord_616481, baseEnd_616481] using wordTrace_append hprefix tailTrace_616481
  have hstable : (prefixWord ++ tailWord_616481).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_616481).length < 2 ^ (prefixWord ++ tailWord_616481).sum := by decide
  have hdescent : baseEnd_616481 < baseStart_616481 := by decide
  rcases family_descends (prefixWord ++ tailWord_616481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_616485 : List Nat := [1, 3, 1, 2, 2, 4, 1, 1, 5]
def baseStart_616485 : Nat := 118140960795 + 616485 * 2 ^ 59
def prefixEnd_616485 : Nat := 4983230072969 + 3 ^ 40 * 616485 * 2
def baseEnd_616485 : Nat := 281380552255222874046527

theorem tailTrace_616485 : CollatzResearch.WordTrace tailWord_616485 prefixEnd_616485 281380552255222874046527 := by
  unfold tailWord_616485
  simp only [CollatzResearch.WordTrace]
  refine ⟨22485055171587607100762909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14990036781058404733841939 22485055171587607100762909)
  ·
    refine ⟨8431895689345352662786091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22485055171587607100762909 8431895689345352662786091)
    ·
      refine ⟨12647843534018028994179137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8431895689345352662786091 12647843534018028994179137)
      ·
        refine ⟨9485882650513521745634353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12647843534018028994179137 9485882650513521745634353)
        ·
          refine ⟨7114411987885141309225765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9485882650513521745634353 7114411987885141309225765)
          ·
            refine ⟨1333952247728463995479831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7114411987885141309225765 1333952247728463995479831)
            ·
              refine ⟨2000928371592695993219747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1333952247728463995479831 2000928371592695993219747)
              ·
                refine ⟨3001392557389043989829621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2000928371592695993219747 3001392557389043989829621)
                ·
                  refine ⟨281380552255222874046527, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3001392557389043989829621 281380552255222874046527)
                  ·
                    rfl

theorem cell20_616485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 4, 1, 1, 5].length) (baseStart_616485 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_616485 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_616485 prefixEnd_616485 := by exact prefixLift 616485
  have htrace : WordTrace (prefixWord ++ tailWord_616485) baseStart_616485 baseEnd_616485 := by
    simpa [prefixWord, tailWord_616485, baseEnd_616485] using wordTrace_append hprefix tailTrace_616485
  have hstable : (prefixWord ++ tailWord_616485).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_616485).length < 2 ^ (prefixWord ++ tailWord_616485).sum := by decide
  have hdescent : baseEnd_616485 < baseStart_616485 := by decide
  rcases family_descends (prefixWord ++ tailWord_616485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_616526 : List Nat := [4, 1, 1, 1, 1, 4, 3, 3, 2]
def baseStart_616526 : Nat := 118140960795 + 616526 * 2 ^ 59
def prefixEnd_616526 : Nat := 4983230072969 + 3 ^ 40 * 616526 * 2
def baseEnd_616526 : Nat := 281399265772408953679693

theorem tailTrace_616526 : CollatzResearch.WordTrace tailWord_616526 prefixEnd_616526 281399265772408953679693 := by
  unfold tailWord_616526
  simp only [CollatzResearch.WordTrace]
  refine ⟨2810818820554883887875679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14991033709626047402003621 2810818820554883887875679)
  ·
    refine ⟨4216228230832325831813519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2810818820554883887875679 4216228230832325831813519)
    ·
      refine ⟨6324342346248488747720279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4216228230832325831813519 6324342346248488747720279)
      ·
        refine ⟨9486513519372733121580419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6324342346248488747720279 9486513519372733121580419)
        ·
          refine ⟨14229770279059099682370629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9486513519372733121580419 14229770279059099682370629)
          ·
            refine ⟨2668081927323581190444493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14229770279059099682370629 2668081927323581190444493)
            ·
              refine ⟨1000530722746342946416685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2668081927323581190444493 1000530722746342946416685)
              ·
                refine ⟨375199021029878604906257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1000530722746342946416685 375199021029878604906257)
                ·
                  refine ⟨281399265772408953679693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 375199021029878604906257 281399265772408953679693)
                  ·
                    rfl

theorem cell20_616526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 3, 3, 2].length) (baseStart_616526 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_616526 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_616526 prefixEnd_616526 := by exact prefixLift 616526
  have htrace : WordTrace (prefixWord ++ tailWord_616526) baseStart_616526 baseEnd_616526 := by
    simpa [prefixWord, tailWord_616526, baseEnd_616526] using wordTrace_append hprefix tailTrace_616526
  have hstable : (prefixWord ++ tailWord_616526).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_616526).length < 2 ^ (prefixWord ++ tailWord_616526).sum := by decide
  have hdescent : baseEnd_616526 < baseStart_616526 := by decide
  rcases family_descends (prefixWord ++ tailWord_616526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_616547 : List Nat := [1, 1, 1, 5, 1, 1, 2, 6, 2]
def baseStart_616547 : Nat := 118140960795 + 616547 * 2 ^ 59
def prefixEnd_616547 : Nat := 4983230072969 + 3 ^ 40 * 616547 * 2
def baseEnd_616547 : Nat := 281408850744626213979607

theorem tailTrace_616547 : CollatzResearch.WordTrace tailWord_616547 prefixEnd_616547 281408850744626213979607 := by
  unfold tailWord_616547
  simp only [CollatzResearch.WordTrace]
  refine ⟨22487316497362991689519895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14991544331575327793013263 22487316497362991689519895)
  ·
    refine ⟨33730974746044487534279843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22487316497362991689519895 33730974746044487534279843)
    ·
      refine ⟨50596462119066731301419765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33730974746044487534279843 50596462119066731301419765)
      ·
        refine ⟨4743418323662506059508103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 50596462119066731301419765 4743418323662506059508103)
        ·
          refine ⟨7115127485493759089262155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4743418323662506059508103 7115127485493759089262155)
          ·
            refine ⟨10672691228240638633893233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7115127485493759089262155 10672691228240638633893233)
            ·
              refine ⟨8004518421180478975419925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10672691228240638633893233 8004518421180478975419925)
              ·
                refine ⟨375211800992834951972809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 8004518421180478975419925 375211800992834951972809)
                ·
                  refine ⟨281408850744626213979607, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 375211800992834951972809 281408850744626213979607)
                  ·
                    rfl

theorem cell20_616547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 2, 6, 2].length) (baseStart_616547 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_616547 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_616547 prefixEnd_616547 := by exact prefixLift 616547
  have htrace : WordTrace (prefixWord ++ tailWord_616547) baseStart_616547 baseEnd_616547 := by
    simpa [prefixWord, tailWord_616547, baseEnd_616547] using wordTrace_append hprefix tailTrace_616547
  have hstable : (prefixWord ++ tailWord_616547).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_616547).length < 2 ^ (prefixWord ++ tailWord_616547).sum := by decide
  have hdescent : baseEnd_616547 < baseStart_616547 := by decide
  rcases family_descends (prefixWord ++ tailWord_616547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_616561 : List Nat := [1, 2, 2, 2, 1, 1, 5, 3, 3]
def baseStart_616561 : Nat := 118140960795 + 616561 * 2 ^ 59
def prefixEnd_616561 : Nat := 4983230072969 + 3 ^ 40 * 616561 * 2
def baseEnd_616561 : Nat := 281415240726104387512883

theorem tailTrace_616561 : CollatzResearch.WordTrace tailWord_616561 prefixEnd_616561 281415240726104387512883 := by
  unfold tailWord_616561
  simp only [CollatzResearch.WordTrace]
  refine ⟨22487827119312272080529537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14991884746208181387019691 22487827119312272080529537)
  ·
    refine ⟨16865870339484204060397153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22487827119312272080529537 16865870339484204060397153)
    ·
      refine ⟨12649402754613153045297865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16865870339484204060397153 12649402754613153045297865)
      ·
        refine ⟨9487052065959864783973399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12649402754613153045297865 9487052065959864783973399)
        ·
          refine ⟨14230578098939797175960099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9487052065959864783973399 14230578098939797175960099)
          ·
            refine ⟨21345867148409695763940149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14230578098939797175960099 21345867148409695763940149)
            ·
              refine ⟨2001175045163408977869389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 21345867148409695763940149 2001175045163408977869389)
              ·
                refine ⟨750440641936278366701021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2001175045163408977869389 750440641936278366701021)
                ·
                  refine ⟨281415240726104387512883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 750440641936278366701021 281415240726104387512883)
                  ·
                    rfl

theorem cell20_616561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 5, 3, 3].length) (baseStart_616561 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_616561 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_616561 prefixEnd_616561 := by exact prefixLift 616561
  have htrace : WordTrace (prefixWord ++ tailWord_616561) baseStart_616561 baseEnd_616561 := by
    simpa [prefixWord, tailWord_616561, baseEnd_616561] using wordTrace_append hprefix tailTrace_616561
  have hstable : (prefixWord ++ tailWord_616561).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_616561).length < 2 ^ (prefixWord ++ tailWord_616561).sum := by decide
  have hdescent : baseEnd_616561 < baseStart_616561 := by decide
  rcases family_descends (prefixWord ++ tailWord_616561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_616585 : List Nat := [1, 2, 1, 1, 4, 2, 2, 5, 2]
def baseStart_616585 : Nat := 118140960795 + 616585 * 2 ^ 59
def prefixEnd_616585 : Nat := 4983230072969 + 3 ^ 40 * 616585 * 2
def baseEnd_616585 : Nat := 281426194980066970712785

theorem tailTrace_616585 : CollatzResearch.WordTrace tailWord_616585 prefixEnd_616585 281426194980066970712785 := by
  unfold tailWord_616585
  simp only [CollatzResearch.WordTrace]
  refine ⟨22488702471225324179403209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14992468314150216119602139 22488702471225324179403209)
  ·
    refine ⟨16866526853418993134552407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22488702471225324179403209 16866526853418993134552407)
    ·
      refine ⟨25299790280128489701828611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16866526853418993134552407 25299790280128489701828611)
      ·
        refine ⟨37949685420192734552742917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25299790280128489701828611 37949685420192734552742917)
        ·
          refine ⟨7115566016286137728639297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 37949685420192734552742917 7115566016286137728639297)
          ·
            refine ⟨5336674512214603296479473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7115566016286137728639297 5336674512214603296479473)
            ·
              refine ⟨4002505884160952472359605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5336674512214603296479473 4002505884160952472359605)
              ·
                refine ⟨375234926640089294283713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4002505884160952472359605 375234926640089294283713)
                ·
                  refine ⟨281426194980066970712785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 375234926640089294283713 281426194980066970712785)
                  ·
                    rfl

theorem cell20_616585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 2, 5, 2].length) (baseStart_616585 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_616585 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_616585 prefixEnd_616585 := by exact prefixLift 616585
  have htrace : WordTrace (prefixWord ++ tailWord_616585) baseStart_616585 baseEnd_616585 := by
    simpa [prefixWord, tailWord_616585, baseEnd_616585] using wordTrace_append hprefix tailTrace_616585
  have hstable : (prefixWord ++ tailWord_616585).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_616585).length < 2 ^ (prefixWord ++ tailWord_616585).sum := by decide
  have hdescent : baseEnd_616585 < baseStart_616585 := by decide
  rcases family_descends (prefixWord ++ tailWord_616585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_616640 : List Nat := [2, 1, 1, 2, 5, 2, 2, 3, 2]
def baseStart_616640 : Nat := 118140960795 + 616640 * 2 ^ 59
def prefixEnd_616640 : Nat := 4983230072969 + 3 ^ 40 * 616640 * 2
def baseEnd_616640 : Nat := 281451298478731223879227

theorem tailTrace_616640 : CollatzResearch.WordTrace tailWord_616640 prefixEnd_616640 281451298478731223879227 := by
  unfold tailWord_616640
  simp only [CollatzResearch.WordTrace]
  refine ⟨11245354243013034286327687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14993805657350712381770249 11245354243013034286327687)
  ·
    refine ⟨16868031364519551429491531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11245354243013034286327687 16868031364519551429491531)
    ·
      refine ⟨25302047046779327144237297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16868031364519551429491531 25302047046779327144237297)
      ·
        refine ⟨18976535285084495358177973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25302047046779327144237297 18976535285084495358177973)
        ·
          refine ⟨1779050182976671439829185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 18976535285084495358177973 1779050182976671439829185)
          ·
            refine ⟨1334287637232503579871889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1779050182976671439829185 1334287637232503579871889)
            ·
              refine ⟨1000715727924377684903917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1334287637232503579871889 1000715727924377684903917)
              ·
                refine ⟨375268397971641631838969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1000715727924377684903917 375268397971641631838969)
                ·
                  refine ⟨281451298478731223879227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 375268397971641631838969 281451298478731223879227)
                  ·
                    rfl

theorem cell20_616640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 2, 2, 3, 2].length) (baseStart_616640 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_616640 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_616640 prefixEnd_616640 := by exact prefixLift 616640
  have htrace : WordTrace (prefixWord ++ tailWord_616640) baseStart_616640 baseEnd_616640 := by
    simpa [prefixWord, tailWord_616640, baseEnd_616640] using wordTrace_append hprefix tailTrace_616640
  have hstable : (prefixWord ++ tailWord_616640).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_616640).length < 2 ^ (prefixWord ++ tailWord_616640).sum := by decide
  have hdescent : baseEnd_616640 < baseStart_616640 := by decide
  rcases family_descends (prefixWord ++ tailWord_616640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_616654 : List Nat := [4, 1, 1, 1, 4, 1, 3, 2, 3]
def baseStart_616654 : Nat := 118140960795 + 616654 * 2 ^ 59
def prefixEnd_616654 : Nat := 4983230072969 + 3 ^ 40 * 616654 * 2
def baseEnd_616654 : Nat := 281457688460209397412503

theorem tailTrace_616654 : CollatzResearch.WordTrace tailWord_616654 prefixEnd_616654 281457688460209397412503 := by
  unfold tailWord_616654
  simp only [CollatzResearch.WordTrace]
  refine ⟨2811402388496918620458127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14994146071983565975776677 2811402388496918620458127)
  ·
    refine ⟨4217103582745377930687191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2811402388496918620458127 4217103582745377930687191)
    ·
      refine ⟨6325655374118066896030787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4217103582745377930687191 6325655374118066896030787)
      ·
        refine ⟨9488483061177100344046181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6325655374118066896030787 9488483061177100344046181)
        ·
          refine ⟨1779090573970706314508659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9488483061177100344046181 1779090573970706314508659)
          ·
            refine ⟨2668635860956059471762989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1779090573970706314508659 2668635860956059471762989)
            ·
              refine ⟨1000738447858522301911121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2668635860956059471762989 1000738447858522301911121)
              ·
                refine ⟨750553835893891726433341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1000738447858522301911121 750553835893891726433341)
                ·
                  refine ⟨281457688460209397412503, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 750553835893891726433341 281457688460209397412503)
                  ·
                    rfl

theorem cell20_616654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 3, 2, 3].length) (baseStart_616654 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_616654 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_616654 prefixEnd_616654 := by exact prefixLift 616654
  have htrace : WordTrace (prefixWord ++ tailWord_616654) baseStart_616654 baseEnd_616654 := by
    simpa [prefixWord, tailWord_616654, baseEnd_616654] using wordTrace_append hprefix tailTrace_616654
  have hstable : (prefixWord ++ tailWord_616654).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_616654).length < 2 ^ (prefixWord ++ tailWord_616654).sum := by decide
  have hdescent : baseEnd_616654 < baseStart_616654 := by decide
  rcases family_descends (prefixWord ++ tailWord_616654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_616682 : List Nat := [3, 1, 3, 1, 1, 2, 1, 4, 4]
def baseStart_616682 : Nat := 118140960795 + 616682 * 2 ^ 59
def prefixEnd_616682 : Nat := 4983230072969 + 3 ^ 40 * 616682 * 2
def baseEnd_616682 : Nat := 281470468423165744479055

theorem tailTrace_616682 : CollatzResearch.WordTrace tailWord_616682 prefixEnd_616682 281470468423165744479055 := by
  unfold tailWord_616682
  simp only [CollatzResearch.WordTrace]
  refine ⟨5623060087968477436421075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14994826901249273163789533 5623060087968477436421075)
  ·
    refine ⟨8434590131952716154631613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5623060087968477436421075 8434590131952716154631613)
    ·
      refine ⟨3162971299482268557986855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8434590131952716154631613 3162971299482268557986855)
      ·
        refine ⟨4744456949223402836980283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3162971299482268557986855 4744456949223402836980283)
        ·
          refine ⟨7116685423835104255470425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4744456949223402836980283 7116685423835104255470425)
          ·
            refine ⟨5337514067876328191602819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7116685423835104255470425 5337514067876328191602819)
            ·
              refine ⟨8006271101814492287404229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5337514067876328191602819 8006271101814492287404229)
              ·
                refine ⟨1501175831590217303888293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8006271101814492287404229 1501175831590217303888293)
                ·
                  refine ⟨281470468423165744479055, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1501175831590217303888293 281470468423165744479055)
                  ·
                    rfl

theorem cell20_616682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 1, 4, 4].length) (baseStart_616682 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_616682 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_616682 prefixEnd_616682 := by exact prefixLift 616682
  have htrace : WordTrace (prefixWord ++ tailWord_616682) baseStart_616682 baseEnd_616682 := by
    simpa [prefixWord, tailWord_616682, baseEnd_616682] using wordTrace_append hprefix tailTrace_616682
  have hstable : (prefixWord ++ tailWord_616682).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_616682).length < 2 ^ (prefixWord ++ tailWord_616682).sum := by decide
  have hdescent : baseEnd_616682 < baseStart_616682 := by decide
  rcases family_descends (prefixWord ++ tailWord_616682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_616706 : List Nat := [3, 4, 1, 1, 2, 1, 8]
def baseStart_616706 : Nat := 118140960795 + 616706 * 2 ^ 59
def prefixEnd_616706 : Nat := 4983230072969 + 3 ^ 40 * 616706 * 2
def baseEnd_616706 : Nat := 31275713630792036408773

theorem tailTrace_616706 : CollatzResearch.WordTrace tailWord_616706 prefixEnd_616706 31275713630792036408773 := by
  unfold tailWord_616706
  simp only [CollatzResearch.WordTrace]
  refine ⟨5623278925946740461139493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14995410469191307896371981 5623278925946740461139493)
  ·
    refine ⟨1054364798615013836463655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5623278925946740461139493 1054364798615013836463655)
    ·
      refine ⟨1581547197922520754695483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1054364798615013836463655 1581547197922520754695483)
      ·
        refine ⟨2372320796883781132043225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1581547197922520754695483 2372320796883781132043225)
        ·
          refine ⟨1779240597662835849032419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2372320796883781132043225 1779240597662835849032419)
          ·
            refine ⟨2668860896494253773548629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1779240597662835849032419 2668860896494253773548629)
            ·
              refine ⟨31275713630792036408773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2668860896494253773548629 31275713630792036408773)
              ·
                rfl

theorem cell20_616706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 8].length) (baseStart_616706 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_616706 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_616706 prefixEnd_616706 := by exact prefixLift 616706
  have htrace : WordTrace (prefixWord ++ tailWord_616706) baseStart_616706 baseEnd_616706 := by
    simpa [prefixWord, tailWord_616706, baseEnd_616706] using wordTrace_append hprefix tailTrace_616706
  have hstable : (prefixWord ++ tailWord_616706).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_616706).length < 2 ^ (prefixWord ++ tailWord_616706).sum := by decide
  have hdescent : baseEnd_616706 < baseStart_616706 := by decide
  rcases family_descends (prefixWord ++ tailWord_616706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_616716 : List Nat := [2, 2, 1, 2, 2, 2, 5, 2, 2]
def baseStart_616716 : Nat := 118140960795 + 616716 * 2 ^ 59
def prefixEnd_616716 : Nat := 4983230072969 + 3 ^ 40 * 616716 * 2
def baseEnd_616716 : Nat := 281485986949612737345583

theorem tailTrace_616716 : CollatzResearch.WordTrace tailWord_616716 prefixEnd_616716 281485986949612737345583 := by
  unfold tailWord_616716
  simp only [CollatzResearch.WordTrace]
  refine ⟨11246740216875366776211001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14995653622500489034948001 11246740216875366776211001)
  ·
    refine ⟨8435055162656525082158251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11246740216875366776211001 8435055162656525082158251)
    ·
      refine ⟨12652582743984787623237377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8435055162656525082158251 12652582743984787623237377)
      ·
        refine ⟨9489437057988590717428033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12652582743984787623237377 9489437057988590717428033)
        ·
          refine ⟨7117077793491443038071025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9489437057988590717428033 7117077793491443038071025)
          ·
            refine ⟨5337808345118582278553269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7117077793491443038071025 5337808345118582278553269)
            ·
              refine ⟨500419532354867088614369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5337808345118582278553269 500419532354867088614369)
              ·
                refine ⟨375314649266150316460777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 500419532354867088614369 375314649266150316460777)
                ·
                  refine ⟨281485986949612737345583, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 375314649266150316460777 281485986949612737345583)
                  ·
                    rfl

theorem cell20_616716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 5, 2, 2].length) (baseStart_616716 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_616716 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_616716 prefixEnd_616716 := by exact prefixLift 616716
  have htrace : WordTrace (prefixWord ++ tailWord_616716) baseStart_616716 baseEnd_616716 := by
    simpa [prefixWord, tailWord_616716, baseEnd_616716] using wordTrace_append hprefix tailTrace_616716
  have hstable : (prefixWord ++ tailWord_616716).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_616716).length < 2 ^ (prefixWord ++ tailWord_616716).sum := by decide
  have hdescent : baseEnd_616716 < baseStart_616716 := by decide
  rcases family_descends (prefixWord ++ tailWord_616716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_616727 : List Nat := [1, 1, 3, 4, 1, 2, 1, 7]
def baseStart_616727 : Nat := 118140960795 + 616727 * 2 ^ 59
def prefixEnd_616727 : Nat := 4983230072969 + 3 ^ 40 * 616727 * 2
def baseEnd_616727 : Nat := 93830335883115195992957

theorem tailTrace_616727 : CollatzResearch.WordTrace tailWord_616727 prefixEnd_616727 93830335883115195992957 := by
  unfold tailWord_616727
  simp only [CollatzResearch.WordTrace]
  refine ⟨22493881636710882431072435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14995921091140588287381623 22493881636710882431072435)
  ·
    refine ⟨33740822455066323646608653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22493881636710882431072435 33740822455066323646608653)
    ·
      refine ⟨12652808420649871367478245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33740822455066323646608653 12652808420649871367478245)
      ·
        refine ⟨2372401578871850881402171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12652808420649871367478245 2372401578871850881402171)
        ·
          refine ⟨3558602368307776322103257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2372401578871850881402171 3558602368307776322103257)
          ·
            refine ⟨2668951776230832241577443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3558602368307776322103257 2668951776230832241577443)
            ·
              refine ⟨4003427664346248362366165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2668951776230832241577443 4003427664346248362366165)
              ·
                refine ⟨93830335883115195992957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4003427664346248362366165 93830335883115195992957)
                ·
                  rfl

theorem cell20_616727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 1, 7].length) (baseStart_616727 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_616727 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_616727 prefixEnd_616727 := by exact prefixLift 616727
  have htrace : WordTrace (prefixWord ++ tailWord_616727) baseStart_616727 baseEnd_616727 := by
    simpa [prefixWord, tailWord_616727, baseEnd_616727] using wordTrace_append hprefix tailTrace_616727
  have hstable : (prefixWord ++ tailWord_616727).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_616727).length < 2 ^ (prefixWord ++ tailWord_616727).sum := by decide
  have hdescent : baseEnd_616727 < baseStart_616727 := by decide
  rcases family_descends (prefixWord ++ tailWord_616727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_616730 : List Nat := [3, 1, 1, 3, 4, 1, 1, 3, 3]
def baseStart_616730 : Nat := 118140960795 + 616730 * 2 ^ 59
def prefixEnd_616730 : Nat := 4983230072969 + 3 ^ 40 * 616730 * 2
def baseEnd_616730 : Nat := 281492376931090910878859

theorem tailTrace_616730 : CollatzResearch.WordTrace tailWord_616730 prefixEnd_616730 281492376931090910878859 := by
  unfold tailWord_616730
  simp only [CollatzResearch.WordTrace]
  refine ⟨5623497763925003485857911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14995994037133342628954429 5623497763925003485857911)
  ·
    refine ⟨8435246645887505228786867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5623497763925003485857911 8435246645887505228786867)
    ·
      refine ⟨12652869968831257843180301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8435246645887505228786867 12652869968831257843180301)
      ·
        refine ⟨4744826238311721691192613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12652869968831257843180301 4744826238311721691192613)
        ·
          refine ⟨889654919683447817098615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4744826238311721691192613 889654919683447817098615)
          ·
            refine ⟨1334482379525171725647923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 889654919683447817098615 1334482379525171725647923)
            ·
              refine ⟨2001723569287757588471885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1334482379525171725647923 2001723569287757588471885)
              ·
                refine ⟨750646338482909095676957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2001723569287757588471885 750646338482909095676957)
                ·
                  refine ⟨281492376931090910878859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 750646338482909095676957 281492376931090910878859)
                  ·
                    rfl

theorem cell20_616730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 1, 1, 3, 3].length) (baseStart_616730 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_616730 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_616730 prefixEnd_616730 := by exact prefixLift 616730
  have htrace : WordTrace (prefixWord ++ tailWord_616730) baseStart_616730 baseEnd_616730 := by
    simpa [prefixWord, tailWord_616730, baseEnd_616730] using wordTrace_append hprefix tailTrace_616730
  have hstable : (prefixWord ++ tailWord_616730).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_616730).length < 2 ^ (prefixWord ++ tailWord_616730).sum := by decide
  have hdescent : baseEnd_616730 < baseStart_616730 := by decide
  rcases family_descends (prefixWord ++ tailWord_616730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_616775 : List Nat := [1, 1, 4, 1, 2, 2, 3, 4, 2]
def baseStart_616775 : Nat := 118140960795 + 616775 * 2 ^ 59
def prefixEnd_616775 : Nat := 4983230072969 + 3 ^ 40 * 616775 * 2
def baseEnd_616775 : Nat := 281512916157270754378675

theorem tailTrace_616775 : CollatzResearch.WordTrace tailWord_616775 prefixEnd_616775 281512916157270754378675 := by
  unfold tailWord_616775
  simp only [CollatzResearch.WordTrace]
  refine ⟨22495632340536986628819779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14997088227024657752546519 22495632340536986628819779)
  ·
    refine ⟨33743448510805479943229669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22495632340536986628819779 33743448510805479943229669)
    ·
      refine ⟨6326896595776027489355563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 33743448510805479943229669 6326896595776027489355563)
      ·
        refine ⟨9490344893664041234033345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6326896595776027489355563 9490344893664041234033345)
        ·
          refine ⟨7117758670248030925525009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9490344893664041234033345 7117758670248030925525009)
          ·
            refine ⟨5338319002686023194143757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7117758670248030925525009 5338319002686023194143757)
            ·
              refine ⟨2001869626007258697803909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5338319002686023194143757 2001869626007258697803909)
              ·
                refine ⟨375350554876361005838233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2001869626007258697803909 375350554876361005838233)
                ·
                  refine ⟨281512916157270754378675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 375350554876361005838233 281512916157270754378675)
                  ·
                    rfl

theorem cell20_616775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 3, 4, 2].length) (baseStart_616775 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_616775 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_616775 prefixEnd_616775 := by exact prefixLift 616775
  have htrace : WordTrace (prefixWord ++ tailWord_616775) baseStart_616775 baseEnd_616775 := by
    simpa [prefixWord, tailWord_616775, baseEnd_616775] using wordTrace_append hprefix tailTrace_616775
  have hstable : (prefixWord ++ tailWord_616775).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_616775).length < 2 ^ (prefixWord ++ tailWord_616775).sum := by decide
  have hdescent : baseEnd_616775 < baseStart_616775 := by decide
  rcases family_descends (prefixWord ++ tailWord_616775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_616817 : List Nat := [1, 2, 2, 2, 1, 2, 1, 1, 8]
def baseStart_616817 : Nat := 118140960795 + 616817 * 2 ^ 59
def prefixEnd_616817 : Nat := 4983230072969 + 3 ^ 40 * 616817 * 2
def baseEnd_616817 : Nat := 281532086101705274978503

theorem tailTrace_616817 : CollatzResearch.WordTrace tailWord_616817 prefixEnd_616817 281532086101705274978503 := by
  unfold tailWord_616817
  simp only [CollatzResearch.WordTrace]
  refine ⟨22497164206384827801848705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14998109470923218534565803 22497164206384827801848705)
  ·
    refine ⟨16872873154788620851386529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22497164206384827801848705 16872873154788620851386529)
    ·
      refine ⟨12654654866091465638539897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16872873154788620851386529 12654654866091465638539897)
      ·
        refine ⟨9490991149568599228904923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12654654866091465638539897 9490991149568599228904923)
        ·
          refine ⟨14236486724352898843357385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9490991149568599228904923 14236486724352898843357385)
          ·
            refine ⟨10677365043264674132518039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14236486724352898843357385 10677365043264674132518039)
            ·
              refine ⟨16016047564897011198777059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10677365043264674132518039 16016047564897011198777059)
              ·
                refine ⟨24024071347345516798165589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16016047564897011198777059 24024071347345516798165589)
                ·
                  refine ⟨281532086101705274978503, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 24024071347345516798165589 281532086101705274978503)
                  ·
                    rfl

theorem cell20_616817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 1, 8].length) (baseStart_616817 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_616817 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_616817 prefixEnd_616817 := by exact prefixLift 616817
  have htrace : WordTrace (prefixWord ++ tailWord_616817) baseStart_616817 baseEnd_616817 := by
    simpa [prefixWord, tailWord_616817, baseEnd_616817] using wordTrace_append hprefix tailTrace_616817
  have hstable : (prefixWord ++ tailWord_616817).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_616817).length < 2 ^ (prefixWord ++ tailWord_616817).sum := by decide
  have hdescent : baseEnd_616817 < baseStart_616817 := by decide
  rcases family_descends (prefixWord ++ tailWord_616817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_616827 : List Nat := [1, 1, 1, 1, 1, 7, 3, 2, 3]
def baseStart_616827 : Nat := 118140960795 + 616827 * 2 ^ 59
def prefixEnd_616827 : Nat := 4983230072969 + 3 ^ 40 * 616827 * 2
def baseEnd_616827 : Nat := 281536650374189684645129

theorem tailTrace_616827 : CollatzResearch.WordTrace tailWord_616827 prefixEnd_616827 281536650374189684645129 := by
  unfold tailWord_616827
  simp only [CollatzResearch.WordTrace]
  refine ⟨22497528936348599509712735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14998352624232399673141823 22497528936348599509712735)
  ·
    refine ⟨33746293404522899264569103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22497528936348599509712735 33746293404522899264569103)
    ·
      refine ⟨50619440106784348896853655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33746293404522899264569103 50619440106784348896853655)
      ·
        refine ⟨75929160160176523345280483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50619440106784348896853655 75929160160176523345280483)
        ·
          refine ⟨113893740240264785017920725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75929160160176523345280483 113893740240264785017920725)
          ·
            refine ⟨2669384536881205898857517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 113893740240264785017920725 2669384536881205898857517)
            ·
              refine ⟨1001019201330452212071569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2669384536881205898857517 1001019201330452212071569)
              ·
                refine ⟨750764400997839159053677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1001019201330452212071569 750764400997839159053677)
                ·
                  refine ⟨281536650374189684645129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 750764400997839159053677 281536650374189684645129)
                  ·
                    rfl

theorem cell20_616827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 3, 2, 3].length) (baseStart_616827 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_616827 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_616827 prefixEnd_616827 := by exact prefixLift 616827
  have htrace : WordTrace (prefixWord ++ tailWord_616827) baseStart_616827 baseEnd_616827 := by
    simpa [prefixWord, tailWord_616827, baseEnd_616827] using wordTrace_append hprefix tailTrace_616827
  have hstable : (prefixWord ++ tailWord_616827).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_616827).length < 2 ^ (prefixWord ++ tailWord_616827).sum := by decide
  have hdescent : baseEnd_616827 < baseStart_616827 := by decide
  rcases family_descends (prefixWord ++ tailWord_616827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_616844 : List Nat := [2, 2, 1, 2, 1, 5, 3, 1, 3]
def baseStart_616844 : Nat := 118140960795 + 616844 * 2 ^ 59
def prefixEnd_616844 : Nat := 4983230072969 + 3 ^ 40 * 616844 * 2
def baseEnd_616844 : Nat := 281544409637413181078393

theorem tailTrace_616844 : CollatzResearch.WordTrace tailWord_616844 prefixEnd_616844 281544409637413181078393 := by
  unfold tailWord_616844
  simp only [CollatzResearch.WordTrace]
  refine ⟨11249074488643505706540793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14998765984858007608721057 11249074488643505706540793)
  ·
    refine ⟨8436805866482629279905595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11249074488643505706540793 8436805866482629279905595)
    ·
      refine ⟨12655208799723943919858393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8436805866482629279905595 12655208799723943919858393)
      ·
        refine ⟨9491406599792957939893795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12655208799723943919858393 9491406599792957939893795)
        ·
          refine ⟨14237109899689436909840693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9491406599792957939893795 14237109899689436909840693)
          ·
            refine ⟨1334729053095884710297565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 14237109899689436909840693 1334729053095884710297565)
            ·
              refine ⟨500523394910956766361587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1334729053095884710297565 500523394910956766361587)
              ·
                refine ⟨750785092366435149542381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 500523394910956766361587 750785092366435149542381)
                ·
                  refine ⟨281544409637413181078393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 750785092366435149542381 281544409637413181078393)
                  ·
                    rfl

theorem cell20_616844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 5, 3, 1, 3].length) (baseStart_616844 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_616844 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_616844 prefixEnd_616844 := by exact prefixLift 616844
  have htrace : WordTrace (prefixWord ++ tailWord_616844) baseStart_616844 baseEnd_616844 := by
    simpa [prefixWord, tailWord_616844, baseEnd_616844] using wordTrace_append hprefix tailTrace_616844
  have hstable : (prefixWord ++ tailWord_616844).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_616844).length < 2 ^ (prefixWord ++ tailWord_616844).sum := by decide
  have hdescent : baseEnd_616844 < baseStart_616844 := by decide
  rcases family_descends (prefixWord ++ tailWord_616844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_616858 : List Nat := [3, 1, 1, 4, 1, 2, 4, 4]
def baseStart_616858 : Nat := 118140960795 + 616858 * 2 ^ 59
def prefixEnd_616858 : Nat := 4983230072969 + 3 ^ 40 * 616858 * 2
def baseEnd_616858 : Nat := 93850266539630451537223

theorem tailTrace_616858 : CollatzResearch.WordTrace tailWord_616858 prefixEnd_616858 93850266539630451537223 := by
  unfold tailWord_616858
  simp only [CollatzResearch.WordTrace]
  refine ⟨5624664899809072951022807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14999106399490861202727485 5624664899809072951022807)
  ·
    refine ⟨8436997349713609426534211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5624664899809072951022807 8436997349713609426534211)
    ·
      refine ⟨12655496024570414139801317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8436997349713609426534211 12655496024570414139801317)
      ·
        refine ⟨2372905504606952651212747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12655496024570414139801317 2372905504606952651212747)
        ·
          refine ⟨3559358256910428976819121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2372905504606952651212747 3559358256910428976819121)
          ·
            refine ⟨2669518692682821732614341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3559358256910428976819121 2669518692682821732614341)
            ·
              refine ⟨500534754878029074865189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2669518692682821732614341 500534754878029074865189)
              ·
                refine ⟨93850266539630451537223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 500534754878029074865189 93850266539630451537223)
                ·
                  rfl

theorem cell20_616858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 4, 4].length) (baseStart_616858 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_616858 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_616858 prefixEnd_616858 := by exact prefixLift 616858
  have htrace : WordTrace (prefixWord ++ tailWord_616858) baseStart_616858 baseEnd_616858 := by
    simpa [prefixWord, tailWord_616858, baseEnd_616858] using wordTrace_append hprefix tailTrace_616858
  have hstable : (prefixWord ++ tailWord_616858).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_616858).length < 2 ^ (prefixWord ++ tailWord_616858).sum := by decide
  have hdescent : baseEnd_616858 < baseStart_616858 := by decide
  rcases family_descends (prefixWord ++ tailWord_616858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_616885 : List Nat := [1, 3, 3, 2, 3, 1, 3, 2, 2]
def baseStart_616885 : Nat := 118140960795 + 616885 * 2 ^ 59
def prefixEnd_616885 : Nat := 4983230072969 + 3 ^ 40 * 616885 * 2
def baseEnd_616885 : Nat := 281563123154599260711559

theorem tailTrace_616885 : CollatzResearch.WordTrace tailWord_616885 prefixEnd_616885 281563123154599260711559 := by
  unfold tailWord_616885
  simp only [CollatzResearch.WordTrace]
  refine ⟨22499644370138475415324109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14999762913425650276882739 22499644370138475415324109)
  ·
    refine ⟨8437366638801928280746541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22499644370138475415324109 8437366638801928280746541)
    ·
      refine ⟨3164012489550723105279953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8437366638801928280746541 3164012489550723105279953)
      ·
        refine ⟨2373009367163042328959965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3164012489550723105279953 2373009367163042328959965)
        ·
          refine ⟨889878512686140873359987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2373009367163042328959965 889878512686140873359987)
          ·
            refine ⟨1334817769029211310039981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 889878512686140873359987 1334817769029211310039981)
            ·
              refine ⟨500556663385954241264993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1334817769029211310039981 500556663385954241264993)
              ·
                refine ⟨375417497539465680948745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 500556663385954241264993 375417497539465680948745)
                ·
                  refine ⟨281563123154599260711559, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 375417497539465680948745 281563123154599260711559)
                  ·
                    rfl

theorem cell20_616885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 1, 3, 2, 2].length) (baseStart_616885 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_616885 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_616885 prefixEnd_616885 := by exact prefixLift 616885
  have htrace : WordTrace (prefixWord ++ tailWord_616885) baseStart_616885 baseEnd_616885 := by
    simpa [prefixWord, tailWord_616885, baseEnd_616885] using wordTrace_append hprefix tailTrace_616885
  have hstable : (prefixWord ++ tailWord_616885).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_616885).length < 2 ^ (prefixWord ++ tailWord_616885).sum := by decide
  have hdescent : baseEnd_616885 < baseStart_616885 := by decide
  rcases family_descends (prefixWord ++ tailWord_616885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_616889 : List Nat := [1, 2, 1, 4, 3, 3, 1, 1, 4]
def baseStart_616889 : Nat := 118140960795 + 616889 * 2 ^ 59
def prefixEnd_616889 : Nat := 4983230072969 + 3 ^ 40 * 616889 * 2
def baseEnd_616889 : Nat := 281564948863593024578209

theorem tailTrace_616889 : CollatzResearch.WordTrace tailWord_616889 prefixEnd_616889 281564948863593024578209 := by
  unfold tailWord_616889
  simp only [CollatzResearch.WordTrace]
  refine ⟨22499790262123984098469721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14999860174749322732313147 22499790262123984098469721)
  ·
    refine ⟨16874842696592988073852291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22499790262123984098469721 16874842696592988073852291)
    ·
      refine ⟨25312264044889482110778437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16874842696592988073852291 25312264044889482110778437)
      ·
        refine ⟨4746049508416777895770957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 25312264044889482110778437 4746049508416777895770957)
        ·
          refine ⟨1779768565656291710914109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4746049508416777895770957 1779768565656291710914109)
          ·
            refine ⟨667413212121109391592791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1779768565656291710914109 667413212121109391592791)
            ·
              refine ⟨1001119818181664087389187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 667413212121109391592791 1001119818181664087389187)
              ·
                refine ⟨1501679727272496131083781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1001119818181664087389187 1501679727272496131083781)
                ·
                  refine ⟨281564948863593024578209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1501679727272496131083781 281564948863593024578209)
                  ·
                    rfl

theorem cell20_616889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 3, 1, 1, 4].length) (baseStart_616889 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_616889 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_616889 prefixEnd_616889 := by exact prefixLift 616889
  have htrace : WordTrace (prefixWord ++ tailWord_616889) baseStart_616889 baseEnd_616889 := by
    simpa [prefixWord, tailWord_616889, baseEnd_616889] using wordTrace_append hprefix tailTrace_616889
  have hstable : (prefixWord ++ tailWord_616889).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_616889).length < 2 ^ (prefixWord ++ tailWord_616889).sum := by decide
  have hdescent : baseEnd_616889 < baseStart_616889 := by decide
  rcases family_descends (prefixWord ++ tailWord_616889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_616903 : List Nat := [1, 1, 4, 1, 1, 5, 1, 3, 3]
def baseStart_616903 : Nat := 118140960795 + 616903 * 2 ^ 59
def prefixEnd_616903 : Nat := 4983230072969 + 3 ^ 40 * 616903 * 2
def baseEnd_616903 : Nat := 281571338845071198111485

theorem tailTrace_616903 : CollatzResearch.WordTrace tailWord_616903 prefixEnd_616903 281571338845071198111485 := by
  unfold tailWord_616903
  simp only [CollatzResearch.WordTrace]
  refine ⟨22500300884073264489479363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15000200589382176326319575 22500300884073264489479363)
  ·
    refine ⟨33750451326109896734219045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22500300884073264489479363 33750451326109896734219045)
    ·
      refine ⟨6328209623645605637666071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 33750451326109896734219045 6328209623645605637666071)
      ·
        refine ⟨9492314435468408456499107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6328209623645605637666071 9492314435468408456499107)
        ·
          refine ⟨14238471653202612684748661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9492314435468408456499107 14238471653202612684748661)
          ·
            refine ⟨1334856717487744939195187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 14238471653202612684748661 1334856717487744939195187)
            ·
              refine ⟨2002285076231617408792781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1334856717487744939195187 2002285076231617408792781)
              ·
                refine ⟨750856903586856528297293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2002285076231617408792781 750856903586856528297293)
                ·
                  refine ⟨281571338845071198111485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 750856903586856528297293 281571338845071198111485)
                  ·
                    rfl

theorem cell20_616903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 5, 1, 3, 3].length) (baseStart_616903 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_616903 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_616903 prefixEnd_616903 := by exact prefixLift 616903
  have htrace : WordTrace (prefixWord ++ tailWord_616903) baseStart_616903 baseEnd_616903 := by
    simpa [prefixWord, tailWord_616903, baseEnd_616903] using wordTrace_append hprefix tailTrace_616903
  have hstable : (prefixWord ++ tailWord_616903).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_616903).length < 2 ^ (prefixWord ++ tailWord_616903).sum := by decide
  have hdescent : baseEnd_616903 < baseStart_616903 := by decide
  rcases family_descends (prefixWord ++ tailWord_616903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_616917 : List Nat := [1, 3, 2, 3, 1, 2, 2, 6]
def baseStart_616917 : Nat := 118140960795 + 616917 * 2 ^ 59
def prefixEnd_616917 : Nat := 4983230072969 + 3 ^ 40 * 616917 * 2
def baseEnd_616917 : Nat := 93859242942183123881587

theorem tailTrace_616917 : CollatzResearch.WordTrace tailWord_616917 prefixEnd_616917 93859242942183123881587 := by
  unfold tailWord_616917
  simp only [CollatzResearch.WordTrace]
  refine ⟨22500811506022544880489005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15000541004015029920326003 22500811506022544880489005)
  ·
    refine ⟨8437804314758454330183377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22500811506022544880489005 8437804314758454330183377)
    ·
      refine ⟨6328353236068840747637533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8437804314758454330183377 6328353236068840747637533)
      ·
        refine ⟨2373132463525815280364075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6328353236068840747637533 2373132463525815280364075)
        ·
          refine ⟨3559698695288722920546113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2373132463525815280364075 3559698695288722920546113)
          ·
            refine ⟨2669774021466542190409585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3559698695288722920546113 2669774021466542190409585)
            ·
              refine ⟨2002330516099906642807189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2669774021466542190409585 2002330516099906642807189)
              ·
                refine ⟨93859242942183123881587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2002330516099906642807189 93859242942183123881587)
                ·
                  rfl

theorem cell20_616917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 2, 6].length) (baseStart_616917 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_616917 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_616917 prefixEnd_616917 := by exact prefixLift 616917
  have htrace : WordTrace (prefixWord ++ tailWord_616917) baseStart_616917 baseEnd_616917 := by
    simpa [prefixWord, tailWord_616917, baseEnd_616917] using wordTrace_append hprefix tailTrace_616917
  have hstable : (prefixWord ++ tailWord_616917).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_616917).length < 2 ^ (prefixWord ++ tailWord_616917).sum := by decide
  have hdescent : baseEnd_616917 < baseStart_616917 := by decide
  rcases family_descends (prefixWord ++ tailWord_616917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_616972 : List Nat := [2, 2, 1, 2, 4, 2, 3, 4]
def baseStart_616972 : Nat := 118140960795 + 616972 * 2 ^ 59
def prefixEnd_616972 : Nat := 4983230072969 + 3 ^ 40 * 616972 * 2
def baseEnd_616972 : Nat := 93867610775071208270401

theorem tailTrace_616972 : CollatzResearch.WordTrace tailWord_616972 prefixEnd_616972 93867610775071208270401 := by
  unfold tailWord_616972
  simp only [CollatzResearch.WordTrace]
  refine ⟨11251408760411644636870585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15001878347215526182494113 11251408760411644636870585)
  ·
    refine ⟨8438556570308733477652939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11251408760411644636870585 8438556570308733477652939)
    ·
      refine ⟨12657834855463100216479409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8438556570308733477652939 12657834855463100216479409)
      ·
        refine ⟨9493376141597325162359557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12657834855463100216479409 9493376141597325162359557)
        ·
          refine ⟨1780008026549498467942417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9493376141597325162359557 1780008026549498467942417)
          ·
            refine ⟨1335006019912123850956813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1780008026549498467942417 1335006019912123850956813)
            ·
              refine ⟨500627257467046444108805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1335006019912123850956813 500627257467046444108805)
              ·
                refine ⟨93867610775071208270401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 500627257467046444108805 93867610775071208270401)
                ·
                  rfl

theorem cell20_616972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 2, 3, 4].length) (baseStart_616972 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_616972 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_616972 prefixEnd_616972 := by exact prefixLift 616972
  have htrace : WordTrace (prefixWord ++ tailWord_616972) baseStart_616972 baseEnd_616972 := by
    simpa [prefixWord, tailWord_616972, baseEnd_616972] using wordTrace_append hprefix tailTrace_616972
  have hstable : (prefixWord ++ tailWord_616972).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_616972).length < 2 ^ (prefixWord ++ tailWord_616972).sum := by decide
  have hdescent : baseEnd_616972 < baseStart_616972 := by decide
  rcases family_descends (prefixWord ++ tailWord_616972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_616996 : List Nat := [2, 3, 1, 5, 1, 1, 1, 1, 5]
def baseStart_616996 : Nat := 118140960795 + 616996 * 2 ^ 59
def prefixEnd_616996 : Nat := 4983230072969 + 3 ^ 40 * 616996 * 2
def baseEnd_616996 : Nat := 281613786579176208011105

theorem tailTrace_616996 : CollatzResearch.WordTrace tailWord_616996 prefixEnd_616996 281613786579176208011105 := by
  unfold tailWord_616996
  simp only [CollatzResearch.WordTrace]
  refine ⟨11251846436368170686307421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15002461915157560915076561 11251846436368170686307421)
  ·
    refine ⟨4219442413638064007365283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11251846436368170686307421 4219442413638064007365283)
    ·
      refine ⟨6329163620457096011047925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4219442413638064007365283 6329163620457096011047925)
      ·
        refine ⟨593359089417852751035743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 6329163620457096011047925 593359089417852751035743)
        ·
          refine ⟨890038634126779126553615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 593359089417852751035743 890038634126779126553615)
          ·
            refine ⟨1335057951190168689830423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 890038634126779126553615 1335057951190168689830423)
            ·
              refine ⟨2002586926785253034745635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1335057951190168689830423 2002586926785253034745635)
              ·
                refine ⟨3003880390177879552118453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2002586926785253034745635 3003880390177879552118453)
                ·
                  refine ⟨281613786579176208011105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3003880390177879552118453 281613786579176208011105)
                  ·
                    rfl

theorem cell20_616996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 1, 1, 1, 5].length) (baseStart_616996 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_616996 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_616996 prefixEnd_616996 := by exact prefixLift 616996
  have htrace : WordTrace (prefixWord ++ tailWord_616996) baseStart_616996 baseEnd_616996 := by
    simpa [prefixWord, tailWord_616996, baseEnd_616996] using wordTrace_append hprefix tailTrace_616996
  have hstable : (prefixWord ++ tailWord_616996).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_616996).length < 2 ^ (prefixWord ++ tailWord_616996).sum := by decide
  have hdescent : baseEnd_616996 < baseStart_616996 := by decide
  rcases family_descends (prefixWord ++ tailWord_616996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_617031 : List Nat := [1, 1, 4, 1, 4, 2, 1, 6]
def baseStart_617031 : Nat := 118140960795 + 617031 * 2 ^ 59
def prefixEnd_617031 : Nat := 4983230072969 + 3 ^ 40 * 617031 * 2
def baseEnd_617031 : Nat := 93876587177623880614765

theorem tailTrace_617031 : CollatzResearch.WordTrace tailWord_617031 prefixEnd_617031 93876587177623880614765 := by
  unfold tailWord_617031
  simp only [CollatzResearch.WordTrace]
  refine ⟨22504969427609542350138947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15003312951739694900092631 22504969427609542350138947)
  ·
    refine ⟨33757454141414313525208421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22504969427609542350138947 33757454141414313525208421)
    ·
      refine ⟨6329522651515183785976579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 33757454141414313525208421 6329522651515183785976579)
      ·
        refine ⟨9494283977272775678964869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6329522651515183785976579 9494283977272775678964869)
        ·
          refine ⟨1780178245738645439805913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9494283977272775678964869 1780178245738645439805913)
          ·
            refine ⟨1335133684303984079854435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1780178245738645439805913 1335133684303984079854435)
            ·
              refine ⟨2002700526455976119781653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1335133684303984079854435 2002700526455976119781653)
              ·
                refine ⟨93876587177623880614765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2002700526455976119781653 93876587177623880614765)
                ·
                  rfl

theorem cell20_617031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 2, 1, 6].length) (baseStart_617031 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_617031 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_617031 prefixEnd_617031 := by exact prefixLift 617031
  have htrace : WordTrace (prefixWord ++ tailWord_617031) baseStart_617031 baseEnd_617031 := by
    simpa [prefixWord, tailWord_617031, baseEnd_617031] using wordTrace_append hprefix tailTrace_617031
  have hstable : (prefixWord ++ tailWord_617031).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_617031).length < 2 ^ (prefixWord ++ tailWord_617031).sum := by decide
  have hdescent : baseEnd_617031 < baseStart_617031 := by decide
  rcases family_descends (prefixWord ++ tailWord_617031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_617037 : List Nat := [1, 6, 1, 1, 2, 3, 1, 3, 2]
def baseStart_617037 : Nat := 118140960795 + 617037 * 2 ^ 59
def prefixEnd_617037 : Nat := 4983230072969 + 3 ^ 40 * 617037 * 2
def baseEnd_617037 : Nat := 281632500096362287644271

theorem tailTrace_617037 : CollatzResearch.WordTrace tailWord_617037 prefixEnd_617037 281632500096362287644271 := by
  unfold tailWord_617037
  simp only [CollatzResearch.WordTrace]
  refine ⟨22505188265587805374857365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15003458843725203583238243 22505188265587805374857365)
  ·
    refine ⟨1054930699949428376946439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 22505188265587805374857365 1054930699949428376946439)
    ·
      refine ⟨1582396049924142565419659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1054930699949428376946439 1582396049924142565419659)
      ·
        refine ⟨2373594074886213848129489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1582396049924142565419659 2373594074886213848129489)
        ·
          refine ⟨1780195556164660386097117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2373594074886213848129489 1780195556164660386097117)
          ·
            refine ⟨667573333561747644786419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1780195556164660386097117 667573333561747644786419)
            ·
              refine ⟨1001360000342621467179629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 667573333561747644786419 1001360000342621467179629)
              ·
                refine ⟨375510000128483050192361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1001360000342621467179629 375510000128483050192361)
                ·
                  refine ⟨281632500096362287644271, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 375510000128483050192361 281632500096362287644271)
                  ·
                    rfl

theorem cell20_617037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 3, 1, 3, 2].length) (baseStart_617037 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_617037 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_617037 prefixEnd_617037 := by exact prefixLift 617037
  have htrace : WordTrace (prefixWord ++ tailWord_617037) baseStart_617037 baseEnd_617037 := by
    simpa [prefixWord, tailWord_617037, baseEnd_617037] using wordTrace_append hprefix tailTrace_617037
  have hstable : (prefixWord ++ tailWord_617037).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_617037).length < 2 ^ (prefixWord ++ tailWord_617037).sum := by decide
  have hdescent : baseEnd_617037 < baseStart_617037 := by decide
  rcases family_descends (prefixWord ++ tailWord_617037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_617038 : List Nat := [4, 1, 1, 1, 1, 2, 3, 2, 5]
def baseStart_617038 : Nat := 118140960795 + 617038 * 2 ^ 59
def prefixEnd_617038 : Nat := 4983230072969 + 3 ^ 40 * 617038 * 2
def baseEnd_617038 : Nat := 281632956523610728610933

theorem tailTrace_617038 : CollatzResearch.WordTrace tailWord_617038 prefixEnd_617038 281632956523610728610933 := by
  unfold tailWord_617038
  simp only [CollatzResearch.WordTrace]
  refine ⟨2813153092323022818205471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15003483159056121697095845 2813153092323022818205471)
  ·
    refine ⟨4219729638484534227308207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2813153092323022818205471 4219729638484534227308207)
    ·
      refine ⟨6329594457726801340962311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4219729638484534227308207 6329594457726801340962311)
      ·
        refine ⟨9494391686590202011443467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6329594457726801340962311 9494391686590202011443467)
        ·
          refine ⟨14241587529885303017165201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9494391686590202011443467 14241587529885303017165201)
          ·
            refine ⟨10681190647413977262873901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14241587529885303017165201 10681190647413977262873901)
            ·
              refine ⟨4005446492780241473577713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10681190647413977262873901 4005446492780241473577713)
              ·
                refine ⟨3004084869585181105183285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4005446492780241473577713 3004084869585181105183285)
                ·
                  refine ⟨281632956523610728610933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3004084869585181105183285 281632956523610728610933)
                  ·
                    rfl

theorem cell20_617038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 3, 2, 5].length) (baseStart_617038 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_617038 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_617038 prefixEnd_617038 := by exact prefixLift 617038
  have htrace : WordTrace (prefixWord ++ tailWord_617038) baseStart_617038 baseEnd_617038 := by
    simpa [prefixWord, tailWord_617038, baseEnd_617038] using wordTrace_append hprefix tailTrace_617038
  have hstable : (prefixWord ++ tailWord_617038).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_617038).length < 2 ^ (prefixWord ++ tailWord_617038).sum := by decide
  have hdescent : baseEnd_617038 < baseStart_617038 := by decide
  rcases family_descends (prefixWord ++ tailWord_617038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_617041 : List Nat := [1, 2, 2, 1, 3, 3, 3, 3, 2]
def baseStart_617041 : Nat := 118140960795 + 617041 * 2 ^ 59
def prefixEnd_617041 : Nat := 4983230072969 + 3 ^ 40 * 617041 * 2
def baseEnd_617041 : Nat := 281634325805356051510921

theorem tailTrace_617041 : CollatzResearch.WordTrace tailWord_617041 prefixEnd_617041 281634325805356051510921 := by
  unfold tailWord_617041
  simp only [CollatzResearch.WordTrace]
  refine ⟨22505334157573314058002977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15003556105048876038668651 22505334157573314058002977)
  ·
    refine ⟨16879000618179985543502233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22505334157573314058002977 16879000618179985543502233)
    ·
      refine ⟨12659250463634989157626675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16879000618179985543502233 12659250463634989157626675)
      ·
        refine ⟨18988875695452483736440013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12659250463634989157626675 18988875695452483736440013)
        ·
          refine ⟨7120828385794681401165005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18988875695452483736440013 7120828385794681401165005)
          ·
            refine ⟨2670310644673005525436877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7120828385794681401165005 2670310644673005525436877)
            ·
              refine ⟨1001366491752377072038829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2670310644673005525436877 1001366491752377072038829)
              ·
                refine ⟨375512434407141402014561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1001366491752377072038829 375512434407141402014561)
                ·
                  refine ⟨281634325805356051510921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 375512434407141402014561 281634325805356051510921)
                  ·
                    rfl

theorem cell20_617041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 3, 3, 2].length) (baseStart_617041 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_617041 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_617041 prefixEnd_617041 := by exact prefixLift 617041
  have htrace : WordTrace (prefixWord ++ tailWord_617041) baseStart_617041 baseEnd_617041 := by
    simpa [prefixWord, tailWord_617041, baseEnd_617041] using wordTrace_append hprefix tailTrace_617041
  have hstable : (prefixWord ++ tailWord_617041).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_617041).length < 2 ^ (prefixWord ++ tailWord_617041).sum := by decide
  have hdescent : baseEnd_617041 < baseStart_617041 := by decide
  rcases family_descends (prefixWord ++ tailWord_617041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_617045 : List Nat := [1, 3, 2, 2, 1, 1, 2, 2, 6]
def baseStart_617045 : Nat := 118140960795 + 617045 * 2 ^ 59
def prefixEnd_617045 : Nat := 4983230072969 + 3 ^ 40 * 617045 * 2
def baseEnd_617045 : Nat := 281636151514349815377571

theorem tailTrace_617045 : CollatzResearch.WordTrace tailWord_617045 prefixEnd_617045 281636151514349815377571 := by
  unfold tailWord_617045
  simp only [CollatzResearch.WordTrace]
  refine ⟨22505480049558822741148589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15003653366372548494099059 22505480049558822741148589)
  ·
    refine ⟨8439555018584558527930721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22505480049558822741148589 8439555018584558527930721)
    ·
      refine ⟨6329666263938418895948041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8439555018584558527930721 6329666263938418895948041)
      ·
        refine ⟨4747249697953814171961031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6329666263938418895948041 4747249697953814171961031)
        ·
          refine ⟨7120874546930721257941547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4747249697953814171961031 7120874546930721257941547)
          ·
            refine ⟨10681311820396081886912321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7120874546930721257941547 10681311820396081886912321)
            ·
              refine ⟨8010983865297061415184241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10681311820396081886912321 8010983865297061415184241)
              ·
                refine ⟨6008237898972796061388181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8010983865297061415184241 6008237898972796061388181)
                ·
                  refine ⟨281636151514349815377571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6008237898972796061388181 281636151514349815377571)
                  ·
                    rfl

theorem cell20_617045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 2, 2, 6].length) (baseStart_617045 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_617045 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_617045 prefixEnd_617045 := by exact prefixLift 617045
  have htrace : WordTrace (prefixWord ++ tailWord_617045) baseStart_617045 baseEnd_617045 := by
    simpa [prefixWord, tailWord_617045, baseEnd_617045] using wordTrace_append hprefix tailTrace_617045
  have hstable : (prefixWord ++ tailWord_617045).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_617045).length < 2 ^ (prefixWord ++ tailWord_617045).sum := by decide
  have hdescent : baseEnd_617045 < baseStart_617045 := by decide
  rcases family_descends (prefixWord ++ tailWord_617045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_617054 : List Nat := [4, 4, 1, 2, 1, 2, 1, 1, 4]
def baseStart_617054 : Nat := 118140960795 + 617054 * 2 ^ 59
def prefixEnd_617054 : Nat := 4983230072969 + 3 ^ 40 * 617054 * 2
def baseEnd_617054 : Nat := 281640259359585784077535

theorem tailTrace_617054 : CollatzResearch.WordTrace tailWord_617054 prefixEnd_617054 281640259359585784077535 := by
  unfold tailWord_617054
  simp only [CollatzResearch.WordTrace]
  refine ⟨2813226038315777159778277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15003872204350811518817477 2813226038315777159778277)
  ·
    refine ⟨527479882184208217458427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2813226038315777159778277 527479882184208217458427)
    ·
      refine ⟨791219823276312326187641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 527479882184208217458427 791219823276312326187641)
      ·
        refine ⟨593414867457234244640731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 791219823276312326187641 593414867457234244640731)
        ·
          refine ⟨890122301185851366961097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 593414867457234244640731 890122301185851366961097)
          ·
            refine ⟨667591725889388525220823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 890122301185851366961097 667591725889388525220823)
            ·
              refine ⟨1001387588834082787831235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 667591725889388525220823 1001387588834082787831235)
              ·
                refine ⟨1502081383251124181746853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1001387588834082787831235 1502081383251124181746853)
                ·
                  refine ⟨281640259359585784077535, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1502081383251124181746853 281640259359585784077535)
                  ·
                    rfl

theorem cell20_617054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 2, 1, 1, 4].length) (baseStart_617054 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_617054 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_617054 prefixEnd_617054 := by exact prefixLift 617054
  have htrace : WordTrace (prefixWord ++ tailWord_617054) baseStart_617054 baseEnd_617054 := by
    simpa [prefixWord, tailWord_617054, baseEnd_617054] using wordTrace_append hprefix tailTrace_617054
  have hstable : (prefixWord ++ tailWord_617054).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_617054).length < 2 ^ (prefixWord ++ tailWord_617054).sum := by decide
  have hdescent : baseEnd_617054 < baseStart_617054 := by decide
  rcases family_descends (prefixWord ++ tailWord_617054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_617069 : List Nat := [1, 5, 1, 1, 3, 1, 1, 7]
def baseStart_617069 : Nat := 118140960795 + 617069 * 2 ^ 59
def prefixEnd_617069 : Nat := 4983230072969 + 3 ^ 40 * 617069 * 2
def baseEnd_617069 : Nat := 93882368589437466192491

theorem tailTrace_617069 : CollatzResearch.WordTrace tailWord_617069 prefixEnd_617069 93882368589437466192491 := by
  unfold tailWord_617069
  simp only [CollatzResearch.WordTrace]
  refine ⟨22506355401471874840022261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15004236934314583226681507 22506355401471874840022261)
  ·
    refine ⟨2109970818887988266252087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 22506355401471874840022261 2109970818887988266252087)
    ·
      refine ⟨3164956228331982399378131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2109970818887988266252087 3164956228331982399378131)
      ·
        refine ⟨4747434342497973599067197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3164956228331982399378131 4747434342497973599067197)
        ·
          refine ⟨1780287878436740099650199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4747434342497973599067197 1780287878436740099650199)
          ·
            refine ⟨2670431817655110149475299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1780287878436740099650199 2670431817655110149475299)
            ·
              refine ⟨4005647726482665224212949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2670431817655110149475299 4005647726482665224212949)
              ·
                refine ⟨93882368589437466192491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4005647726482665224212949 93882368589437466192491)
                ·
                  rfl

theorem cell20_617069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 1, 7].length) (baseStart_617069 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_617069 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_617069 prefixEnd_617069 := by exact prefixLift 617069
  have htrace : WordTrace (prefixWord ++ tailWord_617069) baseStart_617069 baseEnd_617069 := by
    simpa [prefixWord, tailWord_617069, baseEnd_617069] using wordTrace_append hprefix tailTrace_617069
  have hstable : (prefixWord ++ tailWord_617069).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_617069).length < 2 ^ (prefixWord ++ tailWord_617069).sum := by decide
  have hdescent : baseEnd_617069 < baseStart_617069 := by decide
  rcases family_descends (prefixWord ++ tailWord_617069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_617176 : List Nat := [2, 1, 2, 2, 3, 3, 2, 1, 4]
def baseStart_617176 : Nat := 118140960795 + 617176 * 2 ^ 59
def prefixEnd_617176 : Nat := 4983230072969 + 3 ^ 40 * 617176 * 2
def baseEnd_617176 : Nat := 281695943483895582010369

theorem tailTrace_617176 : CollatzResearch.WordTrace tailWord_617176 prefixEnd_617176 281695943483895582010369 := by
  unfold tailWord_617176
  simp only [CollatzResearch.WordTrace]
  refine ⟨11255129006042116057083691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15006838674722821409444921 11255129006042116057083691)
  ·
    refine ⟨16882693509063174085625537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11255129006042116057083691 16882693509063174085625537)
    ·
      refine ⟨12662020131797380564219153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16882693509063174085625537 12662020131797380564219153)
      ·
        refine ⟨9496515098848035423164365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12662020131797380564219153 9496515098848035423164365)
        ·
          refine ⟨3561193162068013283686637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9496515098848035423164365 3561193162068013283686637)
          ·
            refine ⟨1335447435775504981382489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3561193162068013283686637 1335447435775504981382489)
            ·
              refine ⟨1001585576831628736036867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1335447435775504981382489 1001585576831628736036867)
              ·
                refine ⟨1502378365247443104055301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1001585576831628736036867 1502378365247443104055301)
                ·
                  refine ⟨281695943483895582010369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1502378365247443104055301 281695943483895582010369)
                  ·
                    rfl

theorem cell20_617176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 3, 2, 1, 4].length) (baseStart_617176 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_617176 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_617176 prefixEnd_617176 := by exact prefixLift 617176
  have htrace : WordTrace (prefixWord ++ tailWord_617176) baseStart_617176 baseEnd_617176 := by
    simpa [prefixWord, tailWord_617176, baseEnd_617176] using wordTrace_append hprefix tailTrace_617176
  have hstable : (prefixWord ++ tailWord_617176).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_617176).length < 2 ^ (prefixWord ++ tailWord_617176).sum := by decide
  have hdescent : baseEnd_617176 < baseStart_617176 := by decide
  rcases family_descends (prefixWord ++ tailWord_617176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_617228 : List Nat := [2, 2, 1, 2, 2, 1, 1, 6, 3]
def baseStart_617228 : Nat := 118140960795 + 617228 * 2 ^ 59
def prefixEnd_617228 : Nat := 4983230072969 + 3 ^ 40 * 617228 * 2
def baseEnd_617228 : Nat := 281719677700814512276823

theorem tailTrace_617228 : CollatzResearch.WordTrace tailWord_617228 prefixEnd_617228 281719677700814512276823 := by
  unfold tailWord_617228
  simp only [CollatzResearch.WordTrace]
  refine ⟨11256077303947922497530169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15008103071930563330040225 11256077303947922497530169)
  ·
    refine ⟨8442057977960941873147627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11256077303947922497530169 8442057977960941873147627)
    ·
      refine ⟨12663086966941412809721441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8442057977960941873147627 12663086966941412809721441)
      ·
        refine ⟨9497315225206059607291081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12663086966941412809721441 9497315225206059607291081)
        ·
          refine ⟨7122986418904544705468311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9497315225206059607291081 7122986418904544705468311)
          ·
            refine ⟨10684479628356817058202467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7122986418904544705468311 10684479628356817058202467)
            ·
              refine ⟨16026719442535225587303701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10684479628356817058202467 16026719442535225587303701)
              ·
                refine ⟨751252473868838699404861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 16026719442535225587303701 751252473868838699404861)
                ·
                  refine ⟨281719677700814512276823, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 751252473868838699404861 281719677700814512276823)
                  ·
                    rfl

theorem cell20_617228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 6, 3].length) (baseStart_617228 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_617228 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_617228 prefixEnd_617228 := by exact prefixLift 617228
  have htrace : WordTrace (prefixWord ++ tailWord_617228) baseStart_617228 baseEnd_617228 := by
    simpa [prefixWord, tailWord_617228, baseEnd_617228] using wordTrace_append hprefix tailTrace_617228
  have hstable : (prefixWord ++ tailWord_617228).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_617228).length < 2 ^ (prefixWord ++ tailWord_617228).sum := by decide
  have hdescent : baseEnd_617228 < baseStart_617228 := by decide
  rcases family_descends (prefixWord ++ tailWord_617228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_617231 : List Nat := [1, 1, 2, 1, 1, 1, 9, 2, 2]
def baseStart_617231 : Nat := 118140960795 + 617231 * 2 ^ 59
def prefixEnd_617231 : Nat := 4983230072969 + 3 ^ 40 * 617231 * 2
def baseEnd_617231 : Nat := 281721046982559835176811

theorem tailTrace_617231 : CollatzResearch.WordTrace tailWord_617231 prefixEnd_617231 281721046982559835176811 := by
  unfold tailWord_617231
  simp only [CollatzResearch.WordTrace]
  refine ⟨22512264026884976507419547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15008176017923317671613031 22512264026884976507419547)
  ·
    refine ⟨33768396040327464761129321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22512264026884976507419547 33768396040327464761129321)
    ·
      refine ⟨25326297030245598570846991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33768396040327464761129321 25326297030245598570846991)
      ·
        refine ⟨37989445545368397856270487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25326297030245598570846991 37989445545368397856270487)
        ·
          refine ⟨56984168318052596784405731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37989445545368397856270487 56984168318052596784405731)
          ·
            refine ⟨85476252477078895176608597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56984168318052596784405731 85476252477078895176608597)
            ·
              refine ⟨500837416857884151425441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 85476252477078895176608597 500837416857884151425441)
              ·
                refine ⟨375628062643413113569081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 500837416857884151425441 375628062643413113569081)
                ·
                  refine ⟨281721046982559835176811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 375628062643413113569081 281721046982559835176811)
                  ·
                    rfl

theorem cell20_617231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 9, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 9, 2, 2].length) (baseStart_617231 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_617231 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_617231 prefixEnd_617231 := by exact prefixLift 617231
  have htrace : WordTrace (prefixWord ++ tailWord_617231) baseStart_617231 baseEnd_617231 := by
    simpa [prefixWord, tailWord_617231, baseEnd_617231] using wordTrace_append hprefix tailTrace_617231
  have hstable : (prefixWord ++ tailWord_617231).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_617231).length < 2 ^ (prefixWord ++ tailWord_617231).sum := by decide
  have hdescent : baseEnd_617231 < baseStart_617231 := by decide
  rcases family_descends (prefixWord ++ tailWord_617231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_617293 : List Nat := [1, 6, 1, 2, 2, 2, 1, 5]
def baseStart_617293 : Nat := 118140960795 + 617293 * 2 ^ 59
def prefixEnd_617293 : Nat := 4983230072969 + 3 ^ 40 * 617293 * 2
def baseEnd_617293 : Nat := 93916448490654391703297

theorem tailTrace_617293 : CollatzResearch.WordTrace tailWord_617293 prefixEnd_617293 93916448490654391703297 := by
  unfold tailWord_617293
  simp only [CollatzResearch.WordTrace]
  refine ⟨22514525352660361096176533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15009683568440240730784355 22514525352660361096176533)
  ·
    refine ⟨1055368375905954426383275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 22514525352660361096176533 1055368375905954426383275)
    ·
      refine ⟨1583052563858931639574913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1055368375905954426383275 1583052563858931639574913)
      ·
        refine ⟨1187289422894198729681185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1583052563858931639574913 1187289422894198729681185)
        ·
          refine ⟨890467067170649047260889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1187289422894198729681185 890467067170649047260889)
          ·
            refine ⟨667850300377986785445667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 890467067170649047260889 667850300377986785445667)
            ·
              refine ⟨1001775450566980178168501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 667850300377986785445667 1001775450566980178168501)
              ·
                refine ⟨93916448490654391703297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1001775450566980178168501 93916448490654391703297)
                ·
                  rfl

theorem cell20_617293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 2, 1, 5].length) (baseStart_617293 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_617293 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_617293 prefixEnd_617293 := by exact prefixLift 617293
  have htrace : WordTrace (prefixWord ++ tailWord_617293) baseStart_617293 baseEnd_617293 := by
    simpa [prefixWord, tailWord_617293, baseEnd_617293] using wordTrace_append hprefix tailTrace_617293
  have hstable : (prefixWord ++ tailWord_617293).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_617293).length < 2 ^ (prefixWord ++ tailWord_617293).sum := by decide
  have hdescent : baseEnd_617293 < baseStart_617293 := by decide
  rcases family_descends (prefixWord ++ tailWord_617293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_617311 : List Nat := [1, 1, 2, 3, 1, 3, 3, 2, 4]
def baseStart_617311 : Nat := 118140960795 + 617311 * 2 ^ 59
def prefixEnd_617311 : Nat := 4983230072969 + 3 ^ 40 * 617311 * 2
def baseEnd_617311 : Nat := 281757561162435112509817

theorem tailTrace_617311 : CollatzResearch.WordTrace tailWord_617311 prefixEnd_617311 281757561162435112509817 := by
  unfold tailWord_617311
  simp only [CollatzResearch.WordTrace]
  refine ⟨22515181866595150170331787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15010121244396766780221191 22515181866595150170331787)
  ·
    refine ⟨33772772799892725255497681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22515181866595150170331787 33772772799892725255497681)
    ·
      refine ⟨25329579599919543941623261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33772772799892725255497681 25329579599919543941623261)
      ·
        refine ⟨9498592349969828978108723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25329579599919543941623261 9498592349969828978108723)
        ·
          refine ⟨14247888524954743467163085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9498592349969828978108723 14247888524954743467163085)
          ·
            refine ⟨5342958196858028800186157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14247888524954743467163085 5342958196858028800186157)
            ·
              refine ⟨2003609323821760800069809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5342958196858028800186157 2003609323821760800069809)
              ·
                refine ⟨1502706992866320600052357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2003609323821760800069809 1502706992866320600052357)
                ·
                  refine ⟨281757561162435112509817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1502706992866320600052357 281757561162435112509817)
                  ·
                    rfl

theorem cell20_617311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 3, 2, 4].length) (baseStart_617311 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_617311 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_617311 prefixEnd_617311 := by exact prefixLift 617311
  have htrace : WordTrace (prefixWord ++ tailWord_617311) baseStart_617311 baseEnd_617311 := by
    simpa [prefixWord, tailWord_617311, baseEnd_617311] using wordTrace_append hprefix tailTrace_617311
  have hstable : (prefixWord ++ tailWord_617311).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_617311).length < 2 ^ (prefixWord ++ tailWord_617311).sum := by decide
  have hdescent : baseEnd_617311 < baseStart_617311 := by decide
  rcases family_descends (prefixWord ++ tailWord_617311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_617328 : List Nat := [2, 1, 1, 1, 4, 1, 3, 5, 2]
def baseStart_617328 : Nat := 118140960795 + 617328 * 2 ^ 59
def prefixEnd_617328 : Nat := 4983230072969 + 3 ^ 40 * 617328 * 2
def baseEnd_617328 : Nat := 281765320425658608943081

theorem tailTrace_617328 : CollatzResearch.WordTrace tailWord_617328 prefixEnd_617328 281765320425658608943081 := by
  unfold tailWord_617328
  simp only [CollatzResearch.WordTrace]
  refine ⟨11257900953766781036850319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15010534605022374715800425 11257900953766781036850319)
  ·
    refine ⟨16886851430650171555275479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11257900953766781036850319 16886851430650171555275479)
    ·
      refine ⟨25330277145975257332913219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16886851430650171555275479 25330277145975257332913219)
      ·
        refine ⟨37995415718962885999369829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25330277145975257332913219 37995415718962885999369829)
        ·
          refine ⟨7124140447305541124881843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 37995415718962885999369829 7124140447305541124881843)
          ·
            refine ⟨10686210670958311687322765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7124140447305541124881843 10686210670958311687322765)
            ·
              refine ⟨4007329001609366882746037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10686210670958311687322765 4007329001609366882746037)
              ·
                refine ⟨375687093900878145257441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4007329001609366882746037 375687093900878145257441)
                ·
                  refine ⟨281765320425658608943081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 375687093900878145257441 281765320425658608943081)
                  ·
                    rfl

theorem cell20_617328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 3, 5, 2].length) (baseStart_617328 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_617328 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_617328 prefixEnd_617328 := by exact prefixLift 617328
  have htrace : WordTrace (prefixWord ++ tailWord_617328) baseStart_617328 baseEnd_617328 := by
    simpa [prefixWord, tailWord_617328, baseEnd_617328] using wordTrace_append hprefix tailTrace_617328
  have hstable : (prefixWord ++ tailWord_617328).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_617328).length < 2 ^ (prefixWord ++ tailWord_617328).sum := by decide
  have hdescent : baseEnd_617328 < baseStart_617328 := by decide
  rcases family_descends (prefixWord ++ tailWord_617328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_617349 : List Nat := [1, 3, 1, 1, 3, 3, 1, 3, 4]
def baseStart_617349 : Nat := 118140960795 + 617349 * 2 ^ 59
def prefixEnd_617349 : Nat := 4983230072969 + 3 ^ 40 * 617349 * 2
def baseEnd_617349 : Nat := 281774905397875869242995

theorem tailTrace_617349 : CollatzResearch.WordTrace tailWord_617349 prefixEnd_617349 281774905397875869242995 := by
  unfold tailWord_617349
  simp only [CollatzResearch.WordTrace]
  refine ⟨22516567840457482660215101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15011045226971655106810067 22516567840457482660215101)
  ·
    refine ⟨8443712940171555997580663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22516567840457482660215101 8443712940171555997580663)
    ·
      refine ⟨12665569410257333996370995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8443712940171555997580663 12665569410257333996370995)
      ·
        refine ⟨18998354115386000994556493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12665569410257333996370995 18998354115386000994556493)
        ·
          refine ⟨7124382793269750372958685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18998354115386000994556493 7124382793269750372958685)
          ·
            refine ⟨2671643547476156389859507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7124382793269750372958685 2671643547476156389859507)
            ·
              refine ⟨4007465321214234584789261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2671643547476156389859507 4007465321214234584789261)
              ·
                refine ⟨1502799495455337969295973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4007465321214234584789261 1502799495455337969295973)
                ·
                  refine ⟨281774905397875869242995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1502799495455337969295973 281774905397875869242995)
                  ·
                    rfl

theorem cell20_617349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 1, 3, 4].length) (baseStart_617349 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_617349 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_617349 prefixEnd_617349 := by exact prefixLift 617349
  have htrace : WordTrace (prefixWord ++ tailWord_617349) baseStart_617349 baseEnd_617349 := by
    simpa [prefixWord, tailWord_617349, baseEnd_617349] using wordTrace_append hprefix tailTrace_617349
  have hstable : (prefixWord ++ tailWord_617349).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_617349).length < 2 ^ (prefixWord ++ tailWord_617349).sum := by decide
  have hdescent : baseEnd_617349 < baseStart_617349 := by decide
  rcases family_descends (prefixWord ++ tailWord_617349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_617432 : List Nat := [2, 1, 2, 2, 2, 3, 2, 6]
def baseStart_617432 : Nat := 118140960795 + 617432 * 2 ^ 59
def prefixEnd_617432 : Nat := 4983230072969 + 3 ^ 40 * 617432 * 2
def baseEnd_617432 : Nat := 93937596286498823158663

theorem tailTrace_617432 : CollatzResearch.WordTrace tailWord_617432 prefixEnd_617432 93937596286498823158663 := by
  unfold tailWord_617432
  simp only [CollatzResearch.WordTrace]
  refine ⟨11259797549578393917743275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15013063399437858556991033 11259797549578393917743275)
  ·
    refine ⟨16889696324367590876614913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11259797549578393917743275 16889696324367590876614913)
    ·
      refine ⟨12667272243275693157461185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16889696324367590876614913 12667272243275693157461185)
      ·
        refine ⟨9500454182456769868095889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12667272243275693157461185 9500454182456769868095889)
        ·
          refine ⟨7125340636842577401071917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9500454182456769868095889 7125340636842577401071917)
          ·
            refine ⟨2672002738815966525401969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7125340636842577401071917 2672002738815966525401969)
            ·
              refine ⟨2004002054111974894051477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2672002738815966525401969 2004002054111974894051477)
              ·
                refine ⟨93937596286498823158663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2004002054111974894051477 93937596286498823158663)
                ·
                  rfl

theorem cell20_617432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 2, 6].length) (baseStart_617432 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_617432 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_617432 prefixEnd_617432 := by exact prefixLift 617432
  have htrace : WordTrace (prefixWord ++ tailWord_617432) baseStart_617432 baseEnd_617432 := by
    simpa [prefixWord, tailWord_617432, baseEnd_617432] using wordTrace_append hprefix tailTrace_617432
  have hstable : (prefixWord ++ tailWord_617432).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_617432).length < 2 ^ (prefixWord ++ tailWord_617432).sum := by decide
  have hdescent : baseEnd_617432 < baseStart_617432 := by decide
  rcases family_descends (prefixWord ++ tailWord_617432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_617511 : List Nat := [1, 1, 7, 1, 1, 2, 1, 1, 5]
def baseStart_617511 : Nat := 118140960795 + 617511 * 2 ^ 59
def prefixEnd_617511 : Nat := 4983230072969 + 3 ^ 40 * 617511 * 2
def baseEnd_617511 : Nat := 281848846612123305842333

theorem tailTrace_617511 : CollatzResearch.WordTrace tailWord_617511 prefixEnd_617511 281848846612123305842333 := by
  unfold tailWord_617511
  simp only [CollatzResearch.WordTrace]
  refine ⟨22522476465870584327612387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15014984310580389551741591 22522476465870584327612387)
  ·
    refine ⟨33783714698805876491418581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22522476465870584327612387 33783714698805876491418581)
    ·
      refine ⟨791805813253262730267623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 33783714698805876491418581 791805813253262730267623)
      ·
        refine ⟨1187708719879894095401435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 791805813253262730267623 1187708719879894095401435)
        ·
          refine ⟨1781563079819841143102153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1187708719879894095401435 1781563079819841143102153)
          ·
            refine ⟨1336172309864880857326615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1781563079819841143102153 1336172309864880857326615)
            ·
              refine ⟨2004258464797321285989923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1336172309864880857326615 2004258464797321285989923)
              ·
                refine ⟨3006387697195981928984885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2004258464797321285989923 3006387697195981928984885)
                ·
                  refine ⟨281848846612123305842333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3006387697195981928984885 281848846612123305842333)
                  ·
                    rfl

theorem cell20_617511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 2, 1, 1, 5].length) (baseStart_617511 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_617511 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_617511 prefixEnd_617511 := by exact prefixLift 617511
  have htrace : WordTrace (prefixWord ++ tailWord_617511) baseStart_617511 baseEnd_617511 := by
    simpa [prefixWord, tailWord_617511, baseEnd_617511] using wordTrace_append hprefix tailTrace_617511
  have hstable : (prefixWord ++ tailWord_617511).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_617511).length < 2 ^ (prefixWord ++ tailWord_617511).sum := by decide
  have hdescent : baseEnd_617511 < baseStart_617511 := by decide
  rcases family_descends (prefixWord ++ tailWord_617511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_617515 : List Nat := [1, 1, 1, 1, 2, 1, 7, 1, 5]
def baseStart_617515 : Nat := 118140960795 + 617515 * 2 ^ 59
def prefixEnd_617515 : Nat := 4983230072969 + 3 ^ 40 * 617515 * 2
def baseEnd_617515 : Nat := 281850672321117069708983

theorem tailTrace_617515 : CollatzResearch.WordTrace tailWord_617515 prefixEnd_617515 281850672321117069708983 := by
  unfold tailWord_617515
  simp only [CollatzResearch.WordTrace]
  refine ⟨22522622357856093010757999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15015081571904062007171999 22522622357856093010757999)
  ·
    refine ⟨33783933536784139516136999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22522622357856093010757999 33783933536784139516136999)
    ·
      refine ⟨50675900305176209274205499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33783933536784139516136999 50675900305176209274205499)
      ·
        refine ⟨76013850457764313911308249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50675900305176209274205499 76013850457764313911308249)
        ·
          refine ⟨57010387843323235433481187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 76013850457764313911308249 57010387843323235433481187)
          ·
            refine ⟨85515581764984853150221781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57010387843323235433481187 85515581764984853150221781)
            ·
              refine ⟨2004271447616832495708323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 85515581764984853150221781 2004271447616832495708323)
              ·
                refine ⟨3006407171425248743562485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2004271447616832495708323 3006407171425248743562485)
                ·
                  refine ⟨281850672321117069708983, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3006407171425248743562485 281850672321117069708983)
                  ·
                    rfl

theorem cell20_617515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 7, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 7, 1, 5].length) (baseStart_617515 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_617515 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_617515 prefixEnd_617515 := by exact prefixLift 617515
  have htrace : WordTrace (prefixWord ++ tailWord_617515) baseStart_617515 baseEnd_617515 := by
    simpa [prefixWord, tailWord_617515, baseEnd_617515] using wordTrace_append hprefix tailTrace_617515
  have hstable : (prefixWord ++ tailWord_617515).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_617515).length < 2 ^ (prefixWord ++ tailWord_617515).sum := by decide
  have hdescent : baseEnd_617515 < baseStart_617515 := by decide
  rcases family_descends (prefixWord ++ tailWord_617515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_617518 : List Nat := [4, 1, 3, 1, 1, 1, 4, 1, 4]
def baseStart_617518 : Nat := 118140960795 + 617518 * 2 ^ 59
def prefixEnd_617518 : Nat := 4983230072969 + 3 ^ 40 * 617518 * 2
def baseEnd_617518 : Nat := 281852041602862392608971

theorem tailTrace_617518 : CollatzResearch.WordTrace tailWord_617518 prefixEnd_617518 281852041602862392608971 := by
  unfold tailWord_617518
  simp only [CollatzResearch.WordTrace]
  refine ⟨2815341472105653065389651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15015154517896816348744805 2815341472105653065389651)
  ·
    refine ⟨4223012208158479598084477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2815341472105653065389651 4223012208158479598084477)
    ·
      refine ⟨1583629578059429849281679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4223012208158479598084477 1583629578059429849281679)
      ·
        refine ⟨2375444367089144773922519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1583629578059429849281679 2375444367089144773922519)
        ·
          refine ⟨3563166550633717160883779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2375444367089144773922519 3563166550633717160883779)
          ·
            refine ⟨5344749825950575741325669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3563166550633717160883779 5344749825950575741325669)
            ·
              refine ⟨1002140592365732951498563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5344749825950575741325669 1002140592365732951498563)
              ·
                refine ⟨1503210888548599427247845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1002140592365732951498563 1503210888548599427247845)
                ·
                  refine ⟨281852041602862392608971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1503210888548599427247845 281852041602862392608971)
                  ·
                    rfl

theorem cell20_617518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 4, 1, 4].length) (baseStart_617518 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_617518 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_617518 prefixEnd_617518 := by exact prefixLift 617518
  have htrace : WordTrace (prefixWord ++ tailWord_617518) baseStart_617518 baseEnd_617518 := by
    simpa [prefixWord, tailWord_617518, baseEnd_617518] using wordTrace_append hprefix tailTrace_617518
  have hstable : (prefixWord ++ tailWord_617518).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_617518).length < 2 ^ (prefixWord ++ tailWord_617518).sum := by decide
  have hdescent : baseEnd_617518 < baseStart_617518 := by decide
  rcases family_descends (prefixWord ++ tailWord_617518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_617542 : List Nat := [6, 1, 1, 1, 1, 3, 1, 6]
def baseStart_617542 : Nat := 118140960795 + 617542 * 2 ^ 59
def prefixEnd_617542 : Nat := 4983230072969 + 3 ^ 40 * 617542 * 2
def baseEnd_617542 : Nat := 93954331952274991936291

theorem tailTrace_617542 : CollatzResearch.WordTrace tailWord_617542 prefixEnd_617542 93954331952274991936291 := by
  unfold tailWord_617542
  simp only [CollatzResearch.WordTrace]
  refine ⟨703862722773696144437215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 15015738085838851081327253 703862722773696144437215)
  ·
    refine ⟨1055794084160544216655823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 703862722773696144437215 1055794084160544216655823)
    ·
      refine ⟨1583691126240816324983735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1055794084160544216655823 1583691126240816324983735)
      ·
        refine ⟨2375536689361224487475603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1583691126240816324983735 2375536689361224487475603)
        ·
          refine ⟨3563305034041836731213405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2375536689361224487475603 3563305034041836731213405)
          ·
            refine ⟨1336239387765688774205027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3563305034041836731213405 1336239387765688774205027)
            ·
              refine ⟨2004359081648533161307541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1336239387765688774205027 2004359081648533161307541)
              ·
                refine ⟨93954331952274991936291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2004359081648533161307541 93954331952274991936291)
                ·
                  rfl

theorem cell20_617542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 3, 1, 6].length) (baseStart_617542 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_617542 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_617542 prefixEnd_617542 := by exact prefixLift 617542
  have htrace : WordTrace (prefixWord ++ tailWord_617542) baseStart_617542 baseEnd_617542 := by
    simpa [prefixWord, tailWord_617542, baseEnd_617542] using wordTrace_append hprefix tailTrace_617542
  have hstable : (prefixWord ++ tailWord_617542).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_617542).length < 2 ^ (prefixWord ++ tailWord_617542).sum := by decide
  have hdescent : baseEnd_617542 < baseStart_617542 := by decide
  rcases family_descends (prefixWord ++ tailWord_617542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_617553 : List Nat := [1, 2, 2, 1, 3, 1, 3, 2, 5]
def baseStart_617553 : Nat := 118140960795 + 617553 * 2 ^ 59
def prefixEnd_617553 : Nat := 4983230072969 + 3 ^ 40 * 617553 * 2
def baseEnd_617553 : Nat := 281868016556557826442161

theorem tailTrace_617553 : CollatzResearch.WordTrace tailWord_617553 prefixEnd_617553 281868016556557826442161 := by
  unfold tailWord_617553
  simp only [CollatzResearch.WordTrace]
  refine ⟨22524008331718425500641313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15016005554478950333760875 22524008331718425500641313)
  ·
    refine ⟨16893006248788819125480985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22524008331718425500641313 16893006248788819125480985)
    ·
      refine ⟨12669754686591614344110739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16893006248788819125480985 12669754686591614344110739)
      ·
        refine ⟨19004632029887421516166109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12669754686591614344110739 19004632029887421516166109)
        ·
          refine ⟨7126737011207783068562291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19004632029887421516166109 7126737011207783068562291)
          ·
            refine ⟨10690105516811674602843437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7126737011207783068562291 10690105516811674602843437)
            ·
              refine ⟨4008789568804377976066289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10690105516811674602843437 4008789568804377976066289)
              ·
                refine ⟨3006592176603283482049717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4008789568804377976066289 3006592176603283482049717)
                ·
                  refine ⟨281868016556557826442161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3006592176603283482049717 281868016556557826442161)
                  ·
                    rfl

theorem cell20_617553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 3, 2, 5].length) (baseStart_617553 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_617553 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_617553 prefixEnd_617553 := by exact prefixLift 617553
  have htrace : WordTrace (prefixWord ++ tailWord_617553) baseStart_617553 baseEnd_617553 := by
    simpa [prefixWord, tailWord_617553, baseEnd_617553] using wordTrace_append hprefix tailTrace_617553
  have hstable : (prefixWord ++ tailWord_617553).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_617553).length < 2 ^ (prefixWord ++ tailWord_617553).sum := by decide
  have hdescent : baseEnd_617553 < baseStart_617553 := by decide
  rcases family_descends (prefixWord ++ tailWord_617553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_617566 : List Nat := [4, 4, 1, 1, 1, 1, 2, 1, 5]
def baseStart_617566 : Nat := 118140960795 + 617566 * 2 ^ 59
def prefixEnd_617566 : Nat := 4983230072969 + 3 ^ 40 * 617566 * 2
def baseEnd_617566 : Nat := 281873950110787559008775

theorem tailTrace_617566 : CollatzResearch.WordTrace tailWord_617566 prefixEnd_617566 281873950110787559008775 := by
  unfold tailWord_617566
  simp only [CollatzResearch.WordTrace]
  refine ⟨2815560310083916090108069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15016321653780885813909701 2815560310083916090108069)
  ·
    refine ⟨527917558140734266895263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2815560310083916090108069 527917558140734266895263)
    ·
      refine ⟨791876337211101400342895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 527917558140734266895263 791876337211101400342895)
      ·
        refine ⟨1187814505816652100514343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 791876337211101400342895 1187814505816652100514343)
        ·
          refine ⟨1781721758724978150771515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1187814505816652100514343 1781721758724978150771515)
          ·
            refine ⟨2672582638087467226157273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1781721758724978150771515 2672582638087467226157273)
            ·
              refine ⟨2004436978565600419617955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2672582638087467226157273 2004436978565600419617955)
              ·
                refine ⟨3006655467848400629426933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2004436978565600419617955 3006655467848400629426933)
                ·
                  refine ⟨281873950110787559008775, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3006655467848400629426933 281873950110787559008775)
                  ·
                    rfl

theorem cell20_617566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 2, 1, 5].length) (baseStart_617566 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_617566 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_617566 prefixEnd_617566 := by exact prefixLift 617566
  have htrace : WordTrace (prefixWord ++ tailWord_617566) baseStart_617566 baseEnd_617566 := by
    simpa [prefixWord, tailWord_617566, baseEnd_617566] using wordTrace_append hprefix tailTrace_617566
  have hstable : (prefixWord ++ tailWord_617566).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_617566).length < 2 ^ (prefixWord ++ tailWord_617566).sum := by decide
  have hdescent : baseEnd_617566 < baseStart_617566 := by decide
  rcases family_descends (prefixWord ++ tailWord_617566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_617573 : List Nat := [1, 3, 1, 3, 2, 1, 5, 2, 2]
def baseStart_617573 : Nat := 118140960795 + 617573 * 2 ^ 59
def prefixEnd_617573 : Nat := 4983230072969 + 3 ^ 40 * 617573 * 2
def baseEnd_617573 : Nat := 281877145101526645775413

theorem tailTrace_617573 : CollatzResearch.WordTrace tailWord_617573 prefixEnd_617573 281877145101526645775413 := by
  unfold tailWord_617573
  simp only [CollatzResearch.WordTrace]
  refine ⟨22524737791645968916369373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15016491861097312610912915 22524737791645968916369373)
  ·
    refine ⟨8446776671867238343638515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22524737791645968916369373 8446776671867238343638515)
    ·
      refine ⟨12670165007800857515457773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8446776671867238343638515 12670165007800857515457773)
      ·
        refine ⟨4751311877925321568296665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12670165007800857515457773 4751311877925321568296665)
        ·
          refine ⟨3563483908443991176222499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4751311877925321568296665 3563483908443991176222499)
          ·
            refine ⟨5345225862665986764333749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3563483908443991176222499 5345225862665986764333749)
            ·
              refine ⟨501114924624936259156289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5345225862665986764333749 501114924624936259156289)
              ·
                refine ⟨375836193468702194367217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 501114924624936259156289 375836193468702194367217)
                ·
                  refine ⟨281877145101526645775413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 375836193468702194367217 281877145101526645775413)
                  ·
                    rfl

theorem cell20_617573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 5, 2, 2].length) (baseStart_617573 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_617573 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_617573 prefixEnd_617573 := by exact prefixLift 617573
  have htrace : WordTrace (prefixWord ++ tailWord_617573) baseStart_617573 baseEnd_617573 := by
    simpa [prefixWord, tailWord_617573, baseEnd_617573] using wordTrace_append hprefix tailTrace_617573
  have hstable : (prefixWord ++ tailWord_617573).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_617573).length < 2 ^ (prefixWord ++ tailWord_617573).sum := by decide
  have hdescent : baseEnd_617573 < baseStart_617573 := by decide
  rcases family_descends (prefixWord ++ tailWord_617573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_617577 : List Nat := [1, 2, 1, 1, 1, 6, 3, 1, 4]
def baseStart_617577 : Nat := 118140960795 + 617577 * 2 ^ 59
def prefixEnd_617577 : Nat := 4983230072969 + 3 ^ 40 * 617577 * 2
def baseEnd_617577 : Nat := 281878970810520409642063

theorem tailTrace_617577 : CollatzResearch.WordTrace tailWord_617577 prefixEnd_617577 281878970810520409642063 := by
  unfold tailWord_617577
  simp only [CollatzResearch.WordTrace]
  refine ⟨22524883683631477599514985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15016589122420985066343323 22524883683631477599514985)
  ·
    refine ⟨16893662762723608199636239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22524883683631477599514985 16893662762723608199636239)
    ·
      refine ⟨25340494144085412299454359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16893662762723608199636239 25340494144085412299454359)
      ·
        refine ⟨38010741216128118449181539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25340494144085412299454359 38010741216128118449181539)
        ·
          refine ⟨57016111824192177673772309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38010741216128118449181539 57016111824192177673772309)
          ·
            refine ⟨2672630241759008328458077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 57016111824192177673772309 2672630241759008328458077)
            ·
              refine ⟨1002236340659628123171779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2672630241759008328458077 1002236340659628123171779)
              ·
                refine ⟨1503354510989442184757669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1002236340659628123171779 1503354510989442184757669)
                ·
                  refine ⟨281878970810520409642063, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1503354510989442184757669 281878970810520409642063)
                  ·
                    rfl

theorem cell20_617577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 3, 1, 4].length) (baseStart_617577 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_617577 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_617577 prefixEnd_617577 := by exact prefixLift 617577
  have htrace : WordTrace (prefixWord ++ tailWord_617577) baseStart_617577 baseEnd_617577 := by
    simpa [prefixWord, tailWord_617577, baseEnd_617577] using wordTrace_append hprefix tailTrace_617577
  have hstable : (prefixWord ++ tailWord_617577).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_617577).length < 2 ^ (prefixWord ++ tailWord_617577).sum := by decide
  have hdescent : baseEnd_617577 < baseStart_617577 := by decide
  rcases family_descends (prefixWord ++ tailWord_617577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_617584 : List Nat := [2, 1, 1, 1, 5, 1, 4, 5]
def baseStart_617584 : Nat := 118140960795 + 617584 * 2 ^ 59
def prefixEnd_617584 : Nat := 4983230072969 + 3 ^ 40 * 617584 * 2
def baseEnd_617584 : Nat := 93960721933753165469567

theorem tailTrace_617584 : CollatzResearch.WordTrace tailWord_617584 prefixEnd_617584 93960721933753165469567 := by
  unfold tailWord_617584
  simp only [CollatzResearch.WordTrace]
  refine ⟨11262569497303058897509903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15016759329737411863346537 11262569497303058897509903)
  ·
    refine ⟨16893854245954588346264855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11262569497303058897509903 16893854245954588346264855)
    ·
      refine ⟨25340781368931882519397283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16893854245954588346264855 25340781368931882519397283)
      ·
        refine ⟨38011172053397823779095925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25340781368931882519397283 38011172053397823779095925)
        ·
          refine ⟨3563547380006045979290243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 38011172053397823779095925 3563547380006045979290243)
          ·
            refine ⟨5345321070009068968935365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3563547380006045979290243 5345321070009068968935365)
            ·
              refine ⟨1002247700626700431675381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5345321070009068968935365 1002247700626700431675381)
              ·
                refine ⟨93960721933753165469567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1002247700626700431675381 93960721933753165469567)
                ·
                  rfl

theorem cell20_617584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 4, 5].length) (baseStart_617584 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_617584 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_617584 prefixEnd_617584 := by exact prefixLift 617584
  have htrace : WordTrace (prefixWord ++ tailWord_617584) baseStart_617584 baseEnd_617584 := by
    simpa [prefixWord, tailWord_617584, baseEnd_617584] using wordTrace_append hprefix tailTrace_617584
  have hstable : (prefixWord ++ tailWord_617584).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_617584).length < 2 ^ (prefixWord ++ tailWord_617584).sum := by decide
  have hdescent : baseEnd_617584 < baseStart_617584 := by decide
  rcases family_descends (prefixWord ++ tailWord_617584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_617628 : List Nat := [2, 2, 3, 2, 1, 4, 2, 2, 2]
def baseStart_617628 : Nat := 118140960795 + 617628 * 2 ^ 59
def prefixEnd_617628 : Nat := 4983230072969 + 3 ^ 40 * 617628 * 2
def baseEnd_617628 : Nat := 281902248600190898941855

theorem tailTrace_617628 : CollatzResearch.WordTrace tailWord_617628 prefixEnd_617628 281902248600190898941855 := by
  unfold tailWord_617628
  simp only [CollatzResearch.WordTrace]
  refine ⟨11263371903223356654810769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15017829204297808873081025 11263371903223356654810769)
  ·
    refine ⟨8447528927417517491108077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11263371903223356654810769 8447528927417517491108077)
    ·
      refine ⟨3167823347781569059165529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8447528927417517491108077 3167823347781569059165529)
      ·
        refine ⟨2375867510836176794374147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3167823347781569059165529 2375867510836176794374147)
        ·
          refine ⟨3563801266254265191561221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2375867510836176794374147 3563801266254265191561221)
          ·
            refine ⟨668212737422674723417729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3563801266254265191561221 668212737422674723417729)
            ·
              refine ⟨501159553067006042563297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 668212737422674723417729 501159553067006042563297)
              ·
                refine ⟨375869664800254531922473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 501159553067006042563297 375869664800254531922473)
                ·
                  refine ⟨281902248600190898941855, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 375869664800254531922473 281902248600190898941855)
                  ·
                    rfl

theorem cell20_617628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 4, 2, 2, 2].length) (baseStart_617628 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_617628 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_617628 prefixEnd_617628 := by exact prefixLift 617628
  have htrace : WordTrace (prefixWord ++ tailWord_617628) baseStart_617628 baseEnd_617628 := by
    simpa [prefixWord, tailWord_617628, baseEnd_617628] using wordTrace_append hprefix tailTrace_617628
  have hstable : (prefixWord ++ tailWord_617628).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_617628).length < 2 ^ (prefixWord ++ tailWord_617628).sum := by decide
  have hdescent : baseEnd_617628 < baseStart_617628 := by decide
  rcases family_descends (prefixWord ++ tailWord_617628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_617632 : List Nat := [2, 1, 1, 4, 2, 1, 3, 4, 2]
def baseStart_617632 : Nat := 118140960795 + 617632 * 2 ^ 59
def prefixEnd_617632 : Nat := 4983230072969 + 3 ^ 40 * 617632 * 2
def baseEnd_617632 : Nat := 281904074309184662808505

theorem tailTrace_617632 : CollatzResearch.WordTrace tailWord_617632 prefixEnd_617632 281904074309184662808505 := by
  unfold tailWord_617632
  simp only [CollatzResearch.WordTrace]
  refine ⟨11263444849216110996383575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15017926465621481328511433 11263444849216110996383575)
  ·
    refine ⟨16895167273824166494575363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11263444849216110996383575 16895167273824166494575363)
    ·
      refine ⟨25342750910736249741863045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16895167273824166494575363 25342750910736249741863045)
      ·
        refine ⟨4751765795763046826599321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 25342750910736249741863045 4751765795763046826599321)
        ·
          refine ⟨3563824346822285119949491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4751765795763046826599321 3563824346822285119949491)
          ·
            refine ⟨5345736520233427679924237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3563824346822285119949491 5345736520233427679924237)
            ·
              refine ⟨2004651195087535379971589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5345736520233427679924237 2004651195087535379971589)
              ·
                refine ⟨375872099078912883744673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2004651195087535379971589 375872099078912883744673)
                ·
                  refine ⟨281904074309184662808505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 375872099078912883744673 281904074309184662808505)
                  ·
                    rfl

theorem cell20_617632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 3, 4, 2].length) (baseStart_617632 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_617632 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_617632 prefixEnd_617632 := by exact prefixLift 617632
  have htrace : WordTrace (prefixWord ++ tailWord_617632) baseStart_617632 baseEnd_617632 := by
    simpa [prefixWord, tailWord_617632, baseEnd_617632] using wordTrace_append hprefix tailTrace_617632
  have hstable : (prefixWord ++ tailWord_617632).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_617632).length < 2 ^ (prefixWord ++ tailWord_617632).sum := by decide
  have hdescent : baseEnd_617632 < baseStart_617632 := by decide
  rcases family_descends (prefixWord ++ tailWord_617632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_617639 : List Nat := [1, 1, 6, 2, 1, 1, 3, 5]
def baseStart_617639 : Nat := 118140960795 + 617639 * 2 ^ 59
def prefixEnd_617639 : Nat := 4983230072969 + 3 ^ 40 * 617639 * 2
def baseEnd_617639 : Nat := 93969089766641249858381

theorem tailTrace_617639 : CollatzResearch.WordTrace tailWord_617639 prefixEnd_617639 93969089766641249858381 := by
  unfold tailWord_617639
  simp only [CollatzResearch.WordTrace]
  refine ⟨22527145009406862188271971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15018096672937908125514647 22527145009406862188271971)
  ·
    refine ⟨33790717514110293282407957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22527145009406862188271971 33790717514110293282407957)
    ·
      refine ⟨1583939883473919997612873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 33790717514110293282407957 1583939883473919997612873)
      ·
        refine ⟨1187954912605439998209655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1583939883473919997612873 1187954912605439998209655)
        ·
          refine ⟨1781932368908159997314483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1187954912605439998209655 1781932368908159997314483)
          ·
            refine ⟨2672898553362239995971725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1781932368908159997314483 2672898553362239995971725)
            ·
              refine ⟨1002336957510839998489397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2672898553362239995971725 1002336957510839998489397)
              ·
                refine ⟨93969089766641249858381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1002336957510839998489397 93969089766641249858381)
                ·
                  rfl

theorem cell20_617639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 3, 5].length) (baseStart_617639 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_617639 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_617639 prefixEnd_617639 := by exact prefixLift 617639
  have htrace : WordTrace (prefixWord ++ tailWord_617639) baseStart_617639 baseEnd_617639 := by
    simpa [prefixWord, tailWord_617639, baseEnd_617639] using wordTrace_append hprefix tailTrace_617639
  have hstable : (prefixWord ++ tailWord_617639).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_617639).length < 2 ^ (prefixWord ++ tailWord_617639).sum := by decide
  have hdescent : baseEnd_617639 < baseStart_617639 := by decide
  rcases family_descends (prefixWord ++ tailWord_617639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_617715 : List Nat := [1, 1, 1, 2, 2, 7, 2, 4]
def baseStart_617715 : Nat := 118140960795 + 617715 * 2 ^ 59
def prefixEnd_617715 : Nat := 4983230072969 + 3 ^ 40 * 617715 * 2
def baseEnd_617715 : Nat := 93980652590268421013833

theorem tailTrace_617715 : CollatzResearch.WordTrace tailWord_617715 prefixEnd_617715 93980652590268421013833 := by
  unfold tailWord_617715
  simp only [CollatzResearch.WordTrace]
  refine ⟨22529916957131527168038599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15019944638087684778692399 22529916957131527168038599)
  ·
    refine ⟨33794875435697290752057899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22529916957131527168038599 33794875435697290752057899)
    ·
      refine ⟨50692313153545936128086849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33794875435697290752057899 50692313153545936128086849)
      ·
        refine ⟨38019234865159452096065137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50692313153545936128086849 38019234865159452096065137)
        ·
          refine ⟨28514426148869589072048853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38019234865159452096065137 28514426148869589072048853)
          ·
            refine ⟨668306862864130993876145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 28514426148869589072048853 668306862864130993876145)
            ·
              refine ⟨501230147148098245407109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 668306862864130993876145 501230147148098245407109)
              ·
                refine ⟨93980652590268421013833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 501230147148098245407109 93980652590268421013833)
                ·
                  rfl

theorem cell20_617715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 7, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 7, 2, 4].length) (baseStart_617715 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_617715 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_617715 prefixEnd_617715 := by exact prefixLift 617715
  have htrace : WordTrace (prefixWord ++ tailWord_617715) baseStart_617715 baseEnd_617715 := by
    simpa [prefixWord, tailWord_617715, baseEnd_617715] using wordTrace_append hprefix tailTrace_617715
  have hstable : (prefixWord ++ tailWord_617715).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_617715).length < 2 ^ (prefixWord ++ tailWord_617715).sum := by decide
  have hdescent : baseEnd_617715 < baseStart_617715 := by decide
  rcases family_descends (prefixWord ++ tailWord_617715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_617719 : List Nat := [1, 1, 3, 1, 1, 1, 2, 10]
def baseStart_617719 : Nat := 118140960795 + 617719 * 2 ^ 59
def prefixEnd_617719 : Nat := 4983230072969 + 3 ^ 40 * 617719 * 2
def baseEnd_617719 : Nat := 93981261159933008969383

theorem tailTrace_617719 : CollatzResearch.WordTrace tailWord_617719 prefixEnd_617719 93981261159933008969383 := by
  unfold tailWord_617719
  simp only [CollatzResearch.WordTrace]
  refine ⟨22530062849117035851184211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15020041899411357234122807 22530062849117035851184211)
  ·
    refine ⟨33795094273675553776776317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22530062849117035851184211 33795094273675553776776317)
    ·
      refine ⟨12673160352628332666291119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33795094273675553776776317 12673160352628332666291119)
      ·
        refine ⟨19009740528942498999436679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12673160352628332666291119 19009740528942498999436679)
        ·
          refine ⟨28514610793413748499155019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19009740528942498999436679 28514610793413748499155019)
          ·
            refine ⟨42771916190120622748732529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28514610793413748499155019 42771916190120622748732529)
            ·
              refine ⟨32078937142590467061549397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42771916190120622748732529 32078937142590467061549397)
              ·
                refine ⟨93981261159933008969383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 32078937142590467061549397 93981261159933008969383)
                ·
                  rfl

theorem cell20_617719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 10].length) (baseStart_617719 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_617719 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_617719 prefixEnd_617719 := by exact prefixLift 617719
  have htrace : WordTrace (prefixWord ++ tailWord_617719) baseStart_617719 baseEnd_617719 := by
    simpa [prefixWord, tailWord_617719, baseEnd_617719] using wordTrace_append hprefix tailTrace_617719
  have hstable : (prefixWord ++ tailWord_617719).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_617719).length < 2 ^ (prefixWord ++ tailWord_617719).sum := by decide
  have hdescent : baseEnd_617719 < baseStart_617719 := by decide
  rcases family_descends (prefixWord ++ tailWord_617719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_617860 : List Nat := [2, 3, 2, 1, 1, 3, 2, 4, 2]
def baseStart_617860 : Nat := 118140960795 + 617860 * 2 ^ 59
def prefixEnd_617860 : Nat := 4983230072969 + 3 ^ 40 * 617860 * 2
def baseEnd_617860 : Nat := 282008139721829203207573

theorem tailTrace_617860 : CollatzResearch.WordTrace tailWord_617860 prefixEnd_617860 282008139721829203207573 := by
  unfold tailWord_617860
  simp only [CollatzResearch.WordTrace]
  refine ⟨11267602770803108466033517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15023470361070811288044689 11267602770803108466033517)
  ·
    refine ⟨4225351039051165674762569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11267602770803108466033517 4225351039051165674762569)
    ·
      refine ⟨3169013279288374256071927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4225351039051165674762569 3169013279288374256071927)
      ·
        refine ⟨4753519918932561384107891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3169013279288374256071927 4753519918932561384107891)
        ·
          refine ⟨7130279878398842076161837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4753519918932561384107891 7130279878398842076161837)
          ·
            refine ⟨2673854954399565778560689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7130279878398842076161837 2673854954399565778560689)
            ·
              refine ⟨2005391215799674333920517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2673854954399565778560689 2005391215799674333920517)
              ·
                refine ⟨376010852962438937610097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2005391215799674333920517 376010852962438937610097)
                ·
                  refine ⟨282008139721829203207573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 376010852962438937610097 282008139721829203207573)
                  ·
                    rfl

theorem cell20_617860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 2, 4, 2].length) (baseStart_617860 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_617860 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_617860 prefixEnd_617860 := by exact prefixLift 617860
  have htrace : WordTrace (prefixWord ++ tailWord_617860) baseStart_617860 baseEnd_617860 := by
    simpa [prefixWord, tailWord_617860, baseEnd_617860] using wordTrace_append hprefix tailTrace_617860
  have hstable : (prefixWord ++ tailWord_617860).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_617860).length < 2 ^ (prefixWord ++ tailWord_617860).sum := by decide
  have hdescent : baseEnd_617860 < baseStart_617860 := by decide
  rcases family_descends (prefixWord ++ tailWord_617860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_617870 : List Nat := [4, 1, 1, 4, 2, 1, 3, 1, 3]
def baseStart_617870 : Nat := 118140960795 + 617870 * 2 ^ 59
def prefixEnd_617870 : Nat := 4983230072969 + 3 ^ 40 * 617870 * 2
def baseEnd_617870 : Nat := 282012703994313612874199

theorem tailTrace_617870 : CollatzResearch.WordTrace tailWord_617870 prefixEnd_617870 282012703994313612874199 := by
  unfold tailWord_617870
  simp only [CollatzResearch.WordTrace]
  refine ⟨2816946283946248579991383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15023713514379992426620709 2816946283946248579991383)
  ·
    refine ⟨4225419425919372869987075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2816946283946248579991383 4225419425919372869987075)
    ·
      refine ⟨6338129138879059304980613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4225419425919372869987075 6338129138879059304980613)
      ·
        refine ⟨1188399213539823619683865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6338129138879059304980613 1188399213539823619683865)
        ·
          refine ⟨891299410154867714762899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1188399213539823619683865 891299410154867714762899)
          ·
            refine ⟨1336949115232301572144349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 891299410154867714762899 1336949115232301572144349)
            ·
              refine ⟨501355918212113089554131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1336949115232301572144349 501355918212113089554131)
              ·
                refine ⟨752033877318169634331197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 501355918212113089554131 752033877318169634331197)
                ·
                  refine ⟨282012703994313612874199, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 752033877318169634331197 282012703994313612874199)
                  ·
                    rfl

theorem cell20_617870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 1, 3, 1, 3].length) (baseStart_617870 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_617870 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_617870 prefixEnd_617870 := by exact prefixLift 617870
  have htrace : WordTrace (prefixWord ++ tailWord_617870) baseStart_617870 baseEnd_617870 := by
    simpa [prefixWord, tailWord_617870, baseEnd_617870] using wordTrace_append hprefix tailTrace_617870
  have hstable : (prefixWord ++ tailWord_617870).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_617870).length < 2 ^ (prefixWord ++ tailWord_617870).sum := by decide
  have hdescent : baseEnd_617870 < baseStart_617870 := by decide
  rcases family_descends (prefixWord ++ tailWord_617870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_617895 : List Nat := [1, 1, 6, 1, 1, 1, 1, 1, 7]
def baseStart_617895 : Nat := 118140960795 + 617895 * 2 ^ 59
def prefixEnd_617895 : Nat := 4983230072969 + 3 ^ 40 * 617895 * 2
def baseEnd_617895 : Nat := 282024114675524637040763

theorem tailTrace_617895 : CollatzResearch.WordTrace tailWord_617895 prefixEnd_617895 282024114675524637040763 := by
  unfold tailWord_617895
  simp only [CollatzResearch.WordTrace]
  refine ⟨22536482096479417909591139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15024321397652945273060759 22536482096479417909591139)
  ·
    refine ⟨33804723144719126864386709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22536482096479417909591139 33804723144719126864386709)
    ·
      refine ⟨1584596397408709071768127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 33804723144719126864386709 1584596397408709071768127)
      ·
        refine ⟨2376894596113063607652191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1584596397408709071768127 2376894596113063607652191)
        ·
          refine ⟨3565341894169595411478287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2376894596113063607652191 3565341894169595411478287)
          ·
            refine ⟨5348012841254393117217431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3565341894169595411478287 5348012841254393117217431)
            ·
              refine ⟨8022019261881589675826147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5348012841254393117217431 8022019261881589675826147)
              ·
                refine ⟨12033028892822384513739221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8022019261881589675826147 12033028892822384513739221)
                ·
                  refine ⟨282024114675524637040763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12033028892822384513739221 282024114675524637040763)
                  ·
                    rfl

theorem cell20_617895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 1, 1, 7].length) (baseStart_617895 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_617895 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_617895 prefixEnd_617895 := by exact prefixLift 617895
  have htrace : WordTrace (prefixWord ++ tailWord_617895) baseStart_617895 baseEnd_617895 := by
    simpa [prefixWord, tailWord_617895, baseEnd_617895] using wordTrace_append hprefix tailTrace_617895
  have hstable : (prefixWord ++ tailWord_617895).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_617895).length < 2 ^ (prefixWord ++ tailWord_617895).sum := by decide
  have hdescent : baseEnd_617895 < baseStart_617895 := by decide
  rcases family_descends (prefixWord ++ tailWord_617895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_617919 : List Nat := [1, 1, 2, 2, 2, 1, 1, 8, 2]
def baseStart_617919 : Nat := 118140960795 + 617919 * 2 ^ 59
def prefixEnd_617919 : Nat := 4983230072969 + 3 ^ 40 * 617919 * 2
def baseEnd_617919 : Nat := 282035068929487220240665

theorem tailTrace_617919 : CollatzResearch.WordTrace tailWord_617919 prefixEnd_617919 282035068929487220240665 := by
  unfold tailWord_617919
  simp only [CollatzResearch.WordTrace]
  refine ⟨22537357448392470008464811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15024904965594980005643207 22537357448392470008464811)
  ·
    refine ⟨33806036172588705012697217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22537357448392470008464811 33806036172588705012697217)
    ·
      refine ⟨25354527129441528759522913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33806036172588705012697217 25354527129441528759522913)
      ·
        refine ⟨19015895347081146569642185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25354527129441528759522913 19015895347081146569642185)
        ·
          refine ⟨14261921510310859927231639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19015895347081146569642185 14261921510310859927231639)
          ·
            refine ⟨21392882265466289890847459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14261921510310859927231639 21392882265466289890847459)
            ·
              refine ⟨32089323398199434836271189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21392882265466289890847459 32089323398199434836271189)
              ·
                refine ⟨376046758572649626987553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 32089323398199434836271189 376046758572649626987553)
                ·
                  refine ⟨282035068929487220240665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 376046758572649626987553 282035068929487220240665)
                  ·
                    rfl

theorem cell20_617919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 8, 2].length) (baseStart_617919 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_617919 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_617919 prefixEnd_617919 := by exact prefixLift 617919
  have htrace : WordTrace (prefixWord ++ tailWord_617919) baseStart_617919 baseEnd_617919 := by
    simpa [prefixWord, tailWord_617919, baseEnd_617919] using wordTrace_append hprefix tailTrace_617919
  have hstable : (prefixWord ++ tailWord_617919).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_617919).length < 2 ^ (prefixWord ++ tailWord_617919).sum := by decide
  have hdescent : baseEnd_617919 < baseStart_617919 := by decide
  rcases family_descends (prefixWord ++ tailWord_617919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_617970 : List Nat := [3, 2, 1, 4, 1, 3, 2, 2, 2]
def baseStart_617970 : Nat := 118140960795 + 617970 * 2 ^ 59
def prefixEnd_617970 : Nat := 4983230072969 + 3 ^ 40 * 617970 * 2
def baseEnd_617970 : Nat := 282058346719157709540457

theorem tailTrace_617970 : CollatzResearch.WordTrace tailWord_617970 prefixEnd_617970 282058346719157709540457 := by
  unfold tailWord_617970
  simp only [CollatzResearch.WordTrace]
  refine ⟨5634804392801926429642841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15026145047471803812380909 5634804392801926429642841)
  ·
    refine ⟨4226103294601444822232131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5634804392801926429642841 4226103294601444822232131)
    ·
      refine ⟨6339154941902167233348197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4226103294601444822232131 6339154941902167233348197)
      ·
        refine ⟨1188591551606656356252787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6339154941902167233348197 1188591551606656356252787)
        ·
          refine ⟨1782887327409984534379181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1188591551606656356252787 1782887327409984534379181)
          ·
            refine ⟨668582747778744200392193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1782887327409984534379181 668582747778744200392193)
            ·
              refine ⟨501437060834058150294145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 668582747778744200392193 501437060834058150294145)
              ·
                refine ⟨376077795625543612720609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 501437060834058150294145 376077795625543612720609)
                ·
                  refine ⟨282058346719157709540457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 376077795625543612720609 282058346719157709540457)
                  ·
                    rfl

theorem cell20_617970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 3, 2, 2, 2].length) (baseStart_617970 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_617970 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_617970 prefixEnd_617970 := by exact prefixLift 617970
  have htrace : WordTrace (prefixWord ++ tailWord_617970) baseStart_617970 baseEnd_617970 := by
    simpa [prefixWord, tailWord_617970, baseEnd_617970] using wordTrace_append hprefix tailTrace_617970
  have hstable : (prefixWord ++ tailWord_617970).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_617970).length < 2 ^ (prefixWord ++ tailWord_617970).sum := by decide
  have hdescent : baseEnd_617970 < baseStart_617970 := by decide
  rcases family_descends (prefixWord ++ tailWord_617970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_617978 : List Nat := [3, 1, 1, 1, 1, 2, 4, 3, 4]
def baseStart_617978 : Nat := 118140960795 + 617978 * 2 ^ 59
def prefixEnd_617978 : Nat := 4983230072969 + 3 ^ 40 * 617978 * 2
def baseEnd_617978 : Nat := 282061998137145237273757

theorem tailTrace_617978 : CollatzResearch.WordTrace tailWord_617978 prefixEnd_617978 282061998137145237273757 := by
  unfold tailWord_617978
  simp only [CollatzResearch.WordTrace]
  refine ⟨5634877338794680771215647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15026339570119148723241725 5634877338794680771215647)
  ·
    refine ⟨8452316008192021156823471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5634877338794680771215647 8452316008192021156823471)
    ·
      refine ⟨12678474012288031735235207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8452316008192021156823471 12678474012288031735235207)
      ·
        refine ⟨19017711018432047602852811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12678474012288031735235207 19017711018432047602852811)
        ·
          refine ⟨28526566527648071404279217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19017711018432047602852811 28526566527648071404279217)
          ·
            refine ⟨21394924895736053553209413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28526566527648071404279217 21394924895736053553209413)
            ·
              refine ⟨4011548417950510041226765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21394924895736053553209413 4011548417950510041226765)
              ·
                refine ⟨1504330656731441265460037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4011548417950510041226765 1504330656731441265460037)
                ·
                  refine ⟨282061998137145237273757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1504330656731441265460037 282061998137145237273757)
                  ·
                    rfl

theorem cell20_617978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 4, 3, 4].length) (baseStart_617978 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_617978 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_617978 prefixEnd_617978 := by exact prefixLift 617978
  have htrace : WordTrace (prefixWord ++ tailWord_617978) baseStart_617978 baseEnd_617978 := by
    simpa [prefixWord, tailWord_617978, baseEnd_617978] using wordTrace_append hprefix tailTrace_617978
  have hstable : (prefixWord ++ tailWord_617978).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_617978).length < 2 ^ (prefixWord ++ tailWord_617978).sum := by decide
  have hdescent : baseEnd_617978 < baseStart_617978 := by decide
  rcases family_descends (prefixWord ++ tailWord_617978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_617995 : List Nat := [1, 1, 1, 1, 8, 1, 1, 2, 4]
def baseStart_617995 : Nat := 118140960795 + 617995 * 2 ^ 59
def prefixEnd_617995 : Nat := 4983230072969 + 3 ^ 40 * 617995 * 2
def baseEnd_617995 : Nat := 282069757400368733707021

theorem tailTrace_617995 : CollatzResearch.WordTrace tailWord_617995 prefixEnd_617995 282069757400368733707021 := by
  unfold tailWord_617995
  simp only [CollatzResearch.WordTrace]
  refine ⟨22540129396117134988231439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15026752930744756658820959 22540129396117134988231439)
  ·
    refine ⟨33810194094175702482347159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22540129396117134988231439 33810194094175702482347159)
    ·
      refine ⟨50715291141263553723520739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33810194094175702482347159 50715291141263553723520739)
      ·
        refine ⟨76072936711895330585281109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50715291141263553723520739 76072936711895330585281109)
        ·
          refine ⟨891479727092523405296263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 76072936711895330585281109 891479727092523405296263)
          ·
            refine ⟨1337219590638785107944395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 891479727092523405296263 1337219590638785107944395)
            ·
              refine ⟨2005829385958177661916593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1337219590638785107944395 2005829385958177661916593)
              ·
                refine ⟨1504372039468633246437445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2005829385958177661916593 1504372039468633246437445)
                ·
                  refine ⟨282069757400368733707021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1504372039468633246437445 282069757400368733707021)
                  ·
                    rfl

theorem cell20_617995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 1, 1, 2, 4].length) (baseStart_617995 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_617995 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_617995 prefixEnd_617995 := by exact prefixLift 617995
  have htrace : WordTrace (prefixWord ++ tailWord_617995) baseStart_617995 baseEnd_617995 := by
    simpa [prefixWord, tailWord_617995, baseEnd_617995] using wordTrace_append hprefix tailTrace_617995
  have hstable : (prefixWord ++ tailWord_617995).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_617995).length < 2 ^ (prefixWord ++ tailWord_617995).sum := by decide
  have hdescent : baseEnd_617995 < baseStart_617995 := by decide
  rcases family_descends (prefixWord ++ tailWord_617995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_618012 : List Nat := [2, 2, 3, 1, 2, 1, 4, 3, 2]
def baseStart_618012 : Nat := 118140960795 + 618012 * 2 ^ 59
def prefixEnd_618012 : Nat := 4983230072969 + 3 ^ 40 * 618012 * 2
def baseEnd_618012 : Nat := 282077516663592230140285

theorem tailTrace_618012 : CollatzResearch.WordTrace tailWord_618012 prefixEnd_618012 282077516663592230140285 := by
  unfold tailWord_618012
  simp only [CollatzResearch.WordTrace]
  refine ⟨11270374718527773445800145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15027166291370364594400193 11270374718527773445800145)
  ·
    refine ⟨8452781038895830084350109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11270374718527773445800145 8452781038895830084350109)
    ·
      refine ⟨3169792889585936281631291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8452781038895830084350109 3169792889585936281631291)
      ·
        refine ⟨4754689334378904422446937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3169792889585936281631291 4754689334378904422446937)
        ·
          refine ⟨3566017000784178316835203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4754689334378904422446937 3566017000784178316835203)
          ·
            refine ⟨5349025501176267475252805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3566017000784178316835203 5349025501176267475252805)
            ·
              refine ⟨1002942281470550151609901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5349025501176267475252805 1002942281470550151609901)
              ·
                refine ⟨376103355551456306853713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1002942281470550151609901 376103355551456306853713)
                ·
                  refine ⟨282077516663592230140285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 376103355551456306853713 282077516663592230140285)
                  ·
                    rfl

theorem cell20_618012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 4, 3, 2].length) (baseStart_618012 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_618012 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_618012 prefixEnd_618012 := by exact prefixLift 618012
  have htrace : WordTrace (prefixWord ++ tailWord_618012) baseStart_618012 baseEnd_618012 := by
    simpa [prefixWord, tailWord_618012, baseEnd_618012] using wordTrace_append hprefix tailTrace_618012
  have hstable : (prefixWord ++ tailWord_618012).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_618012).length < 2 ^ (prefixWord ++ tailWord_618012).sum := by decide
  have hdescent : baseEnd_618012 < baseStart_618012 := by decide
  rcases family_descends (prefixWord ++ tailWord_618012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_618085 : List Nat := [1, 3, 1, 3, 3, 1, 2, 1, 5]
def baseStart_618085 : Nat := 118140960795 + 618085 * 2 ^ 59
def prefixEnd_618085 : Nat := 4983230072969 + 3 ^ 40 * 618085 * 2
def baseEnd_618085 : Nat := 282110835852728420706653

theorem tailTrace_618085 : CollatzResearch.WordTrace tailWord_618085 prefixEnd_618085 282110835852728420706653 := by
  unfold tailWord_618085
  simp only [CollatzResearch.WordTrace]
  refine ⟨22543411965791080359007709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15028941310527386906005139 22543411965791080359007709)
  ·
    refine ⟨8453779487171655134627891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22543411965791080359007709 8453779487171655134627891)
    ·
      refine ⟨12680669230757482701941837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8453779487171655134627891 12680669230757482701941837)
      ·
        refine ⟨4755250961534056013228189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12680669230757482701941837 4755250961534056013228189)
        ·
          refine ⟨1783219110575271004960571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4755250961534056013228189 1783219110575271004960571)
          ·
            refine ⟨2674828665862906507440857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1783219110575271004960571 2674828665862906507440857)
            ·
              refine ⟨2006121499397179880580643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2674828665862906507440857 2006121499397179880580643)
              ·
                refine ⟨3009182249095769820870965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2006121499397179880580643 3009182249095769820870965)
                ·
                  refine ⟨282110835852728420706653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3009182249095769820870965 282110835852728420706653)
                  ·
                    rfl

theorem cell20_618085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 2, 1, 5].length) (baseStart_618085 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_618085 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_618085 prefixEnd_618085 := by exact prefixLift 618085
  have htrace : WordTrace (prefixWord ++ tailWord_618085) baseStart_618085 baseEnd_618085 := by
    simpa [prefixWord, tailWord_618085, baseEnd_618085] using wordTrace_append hprefix tailTrace_618085
  have hstable : (prefixWord ++ tailWord_618085).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_618085).length < 2 ^ (prefixWord ++ tailWord_618085).sum := by decide
  have hdescent : baseEnd_618085 < baseStart_618085 := by decide
  rcases family_descends (prefixWord ++ tailWord_618085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_618088 : List Nat := [2, 1, 4, 3, 1, 3, 1, 1, 4]
def baseStart_618088 : Nat := 118140960795 + 618088 * 2 ^ 59
def prefixEnd_618088 : Nat := 4983230072969 + 3 ^ 40 * 618088 * 2
def baseEnd_618088 : Nat := 282112205134473743606641

theorem tailTrace_618088 : CollatzResearch.WordTrace tailWord_618088 prefixEnd_618088 282112205134473743606641 := by
  unfold tailWord_618088
  simp only [CollatzResearch.WordTrace]
  refine ⟨11271760692390105935683459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15029014256520141247577945 11271760692390105935683459)
  ·
    refine ⟨16907641038585158903525189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11271760692390105935683459 16907641038585158903525189)
    ·
      refine ⟨3170182694734717294410973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16907641038585158903525189 3170182694734717294410973)
      ·
        refine ⟨1188818510525518985404115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3170182694734717294410973 1188818510525518985404115)
        ·
          refine ⟨1783227765788278478106173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1188818510525518985404115 1783227765788278478106173)
          ·
            refine ⟨668710412170604429289815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1783227765788278478106173 668710412170604429289815)
            ·
              refine ⟨1003065618255906643934723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 668710412170604429289815 1003065618255906643934723)
              ·
                refine ⟨1504598427383859965902085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1003065618255906643934723 1504598427383859965902085)
                ·
                  refine ⟨282112205134473743606641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1504598427383859965902085 282112205134473743606641)
                  ·
                    rfl

theorem cell20_618088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 3, 1, 1, 4].length) (baseStart_618088 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_618088 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_618088 prefixEnd_618088 := by exact prefixLift 618088
  have htrace : WordTrace (prefixWord ++ tailWord_618088) baseStart_618088 baseEnd_618088 := by
    simpa [prefixWord, tailWord_618088, baseEnd_618088] using wordTrace_append hprefix tailTrace_618088
  have hstable : (prefixWord ++ tailWord_618088).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_618088).length < 2 ^ (prefixWord ++ tailWord_618088).sum := by decide
  have hdescent : baseEnd_618088 < baseStart_618088 := by decide
  rcases family_descends (prefixWord ++ tailWord_618088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_618106 : List Nat := [3, 1, 1, 1, 1, 1, 1, 4, 7]
def baseStart_618106 : Nat := 118140960795 + 618106 * 2 ^ 59
def prefixEnd_618106 : Nat := 4983230072969 + 3 ^ 40 * 618106 * 2
def baseEnd_618106 : Nat := 282120420824945681006567

theorem tailTrace_618106 : CollatzResearch.WordTrace tailWord_618106 prefixEnd_618106 282120420824945681006567 := by
  unfold tailWord_618106
  simp only [CollatzResearch.WordTrace]
  refine ⟨5636044474678750236380543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15029451932476667297014781 5636044474678750236380543)
  ·
    refine ⟨8454066712018125354570815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5636044474678750236380543 8454066712018125354570815)
    ·
      refine ⟨12681100068027188031856223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8454066712018125354570815 12681100068027188031856223)
      ·
        refine ⟨19021650102040782047784335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12681100068027188031856223 19021650102040782047784335)
        ·
          refine ⟨28532475153061173071676503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19021650102040782047784335 28532475153061173071676503)
          ·
            refine ⟨42798712729591759607514755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28532475153061173071676503 42798712729591759607514755)
            ·
              refine ⟨64198069094387639411272133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42798712729591759607514755 64198069094387639411272133)
              ·
                refine ⟨12037137955197682389613525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 64198069094387639411272133 12037137955197682389613525)
                ·
                  refine ⟨282120420824945681006567, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12037137955197682389613525 282120420824945681006567)
                  ·
                    rfl

theorem cell20_618106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 4, 7].length) (baseStart_618106 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_618106 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_618106 prefixEnd_618106 := by exact prefixLift 618106
  have htrace : WordTrace (prefixWord ++ tailWord_618106) baseStart_618106 baseEnd_618106 := by
    simpa [prefixWord, tailWord_618106, baseEnd_618106] using wordTrace_append hprefix tailTrace_618106
  have hstable : (prefixWord ++ tailWord_618106).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_618106).length < 2 ^ (prefixWord ++ tailWord_618106).sum := by decide
  have hdescent : baseEnd_618106 < baseStart_618106 := by decide
  rcases family_descends (prefixWord ++ tailWord_618106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_618143 : List Nat := [1, 1, 2, 7, 1, 1, 1, 4, 2]
def baseStart_618143 : Nat := 118140960795 + 618143 * 2 ^ 59
def prefixEnd_618143 : Nat := 4983230072969 + 3 ^ 40 * 618143 * 2
def baseEnd_618143 : Nat := 282137308633137996773083

theorem tailTrace_618143 : CollatzResearch.WordTrace tailWord_618143 prefixEnd_618143 282137308633137996773083 := by
  unfold tailWord_618143
  simp only [CollatzResearch.WordTrace]
  refine ⟨22545527399580956264619083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15030351599720637509746055 22545527399580956264619083)
  ·
    refine ⟨33818291099371434396928625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22545527399580956264619083 33818291099371434396928625)
    ·
      refine ⟨25363718324528575797696469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33818291099371434396928625 25363718324528575797696469)
      ·
        refine ⟨594462148231138495258511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 25363718324528575797696469 594462148231138495258511)
        ·
          refine ⟨891693222346707742887767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 594462148231138495258511 891693222346707742887767)
          ·
            refine ⟨1337539833520061614331651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 891693222346707742887767 1337539833520061614331651)
            ·
              refine ⟨2006309750280092421497477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1337539833520061614331651 2006309750280092421497477)
              ·
                refine ⟨376183078177517329030777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2006309750280092421497477 376183078177517329030777)
                ·
                  refine ⟨282137308633137996773083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 376183078177517329030777 282137308633137996773083)
                  ·
                    rfl

theorem cell20_618143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 1, 1, 4, 2].length) (baseStart_618143 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_618143 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_618143 prefixEnd_618143 := by exact prefixLift 618143
  have htrace : WordTrace (prefixWord ++ tailWord_618143) baseStart_618143 baseEnd_618143 := by
    simpa [prefixWord, tailWord_618143, baseEnd_618143] using wordTrace_append hprefix tailTrace_618143
  have hstable : (prefixWord ++ tailWord_618143).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_618143).length < 2 ^ (prefixWord ++ tailWord_618143).sum := by decide
  have hdescent : baseEnd_618143 < baseStart_618143 := by decide
  rcases family_descends (prefixWord ++ tailWord_618143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_618147 : List Nat := [1, 1, 1, 4, 1, 1, 5, 4, 2]
def baseStart_618147 : Nat := 118140960795 + 618147 * 2 ^ 59
def prefixEnd_618147 : Nat := 4983230072969 + 3 ^ 40 * 618147 * 2
def baseEnd_618147 : Nat := 282139134342131760639733

theorem tailTrace_618147 : CollatzResearch.WordTrace tailWord_618147 prefixEnd_618147 282139134342131760639733 := by
  unfold tailWord_618147
  simp only [CollatzResearch.WordTrace]
  refine ⟨22545673291566464947764695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15030448861044309965176463 22545673291566464947764695)
  ·
    refine ⟨33818509937349697421647043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22545673291566464947764695 33818509937349697421647043)
    ·
      refine ⟨50727764906024546132470565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33818509937349697421647043 50727764906024546132470565)
      ·
        refine ⟨9511455919879602399838231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 50727764906024546132470565 9511455919879602399838231)
        ·
          refine ⟨14267183879819403599757347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9511455919879602399838231 14267183879819403599757347)
          ·
            refine ⟨21400775819729105399636021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14267183879819403599757347 21400775819729105399636021)
            ·
              refine ⟨2006322733099603631215877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 21400775819729105399636021 2006322733099603631215877)
              ·
                refine ⟨376185512456175680852977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2006322733099603631215877 376185512456175680852977)
                ·
                  refine ⟨282139134342131760639733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 376185512456175680852977 282139134342131760639733)
                  ·
                    rfl

theorem cell20_618147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 5, 4, 2].length) (baseStart_618147 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_618147 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_618147 prefixEnd_618147 := by exact prefixLift 618147
  have htrace : WordTrace (prefixWord ++ tailWord_618147) baseStart_618147 baseEnd_618147 := by
    simpa [prefixWord, tailWord_618147, baseEnd_618147] using wordTrace_append hprefix tailTrace_618147
  have hstable : (prefixWord ++ tailWord_618147).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_618147).length < 2 ^ (prefixWord ++ tailWord_618147).sum := by decide
  have hdescent : baseEnd_618147 < baseStart_618147 := by decide
  rcases family_descends (prefixWord ++ tailWord_618147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_618213 : List Nat := [1, 3, 1, 4, 1, 1, 2, 7]
def baseStart_618213 : Nat := 118140960795 + 618213 * 2 ^ 59
def prefixEnd_618213 : Nat := 4983230072969 + 3 ^ 40 * 618213 * 2
def baseEnd_618213 : Nat := 94056419513509621479821

theorem tailTrace_618213 : CollatzResearch.WordTrace tailWord_618213 prefixEnd_618213 94056419513509621479821 := by
  unfold tailWord_618213
  simp only [CollatzResearch.WordTrace]
  refine ⟨22548080509327358219667293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15032053672884905479778195 22548080509327358219667293)
  ·
    refine ⟨8455530190997759332375235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22548080509327358219667293 8455530190997759332375235)
    ·
      refine ⟨12683295286496638998562853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8455530190997759332375235 12683295286496638998562853)
      ·
        refine ⟨2378117866218119812230535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12683295286496638998562853 2378117866218119812230535)
        ·
          refine ⟨3567176799327179718345803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2378117866218119812230535 3567176799327179718345803)
          ·
            refine ⟨5350765198990769577518705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3567176799327179718345803 5350765198990769577518705)
            ·
              refine ⟨4013073899243077183139029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5350765198990769577518705 4013073899243077183139029)
              ·
                refine ⟨94056419513509621479821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4013073899243077183139029 94056419513509621479821)
                ·
                  rfl

theorem cell20_618213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 2, 7].length) (baseStart_618213 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_618213 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_618213 prefixEnd_618213 := by exact prefixLift 618213
  have htrace : WordTrace (prefixWord ++ tailWord_618213) baseStart_618213 baseEnd_618213 := by
    simpa [prefixWord, tailWord_618213, baseEnd_618213] using wordTrace_append hprefix tailTrace_618213
  have hstable : (prefixWord ++ tailWord_618213).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_618213).length < 2 ^ (prefixWord ++ tailWord_618213).sum := by decide
  have hdescent : baseEnd_618213 < baseStart_618213 := by decide
  rcases family_descends (prefixWord ++ tailWord_618213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_618230 : List Nat := [5, 1, 1, 1, 1, 4, 1, 6]
def baseStart_618230 : Nat := 118140960795 + 618230 * 2 ^ 59
def prefixEnd_618230 : Nat := 4983230072969 + 3 ^ 40 * 618230 * 2
def baseEnd_618230 : Nat := 94059005934584120290909

theorem tailTrace_618230 : CollatzResearch.WordTrace tailWord_618230 prefixEnd_618230 94059005934584120290909 := by
  unfold tailWord_618230
  simp only [CollatzResearch.WordTrace]
  refine ⟨1409293784391610632689759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 15032467033510513415357429 1409293784391610632689759)
  ·
    refine ⟨2113940676587415949034639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1409293784391610632689759 2113940676587415949034639)
    ·
      refine ⟨3170911014881123923551959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2113940676587415949034639 3170911014881123923551959)
      ·
        refine ⟨4756366522321685885327939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3170911014881123923551959 4756366522321685885327939)
        ·
          refine ⟨7134549783482528827991909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4756366522321685885327939 7134549783482528827991909)
          ·
            refine ⟨1337728084402974155248483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7134549783482528827991909 1337728084402974155248483)
            ·
              refine ⟨2006592126604461232872725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1337728084402974155248483 2006592126604461232872725)
              ·
                refine ⟨94059005934584120290909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2006592126604461232872725 94059005934584120290909)
                ·
                  rfl

theorem cell20_618230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 4, 1, 6].length) (baseStart_618230 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_618230 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_618230 prefixEnd_618230 := by exact prefixLift 618230
  have htrace : WordTrace (prefixWord ++ tailWord_618230) baseStart_618230 baseEnd_618230 := by
    simpa [prefixWord, tailWord_618230, baseEnd_618230] using wordTrace_append hprefix tailTrace_618230
  have hstable : (prefixWord ++ tailWord_618230).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_618230).length < 2 ^ (prefixWord ++ tailWord_618230).sum := by decide
  have hdescent : baseEnd_618230 < baseStart_618230 := by decide
  rcases family_descends (prefixWord ++ tailWord_618230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_618247 : List Nat := [1, 1, 4, 4, 3, 1, 6]
def baseStart_618247 : Nat := 118140960795 + 618247 * 2 ^ 59
def prefixEnd_618247 : Nat := 4983230072969 + 3 ^ 40 * 618247 * 2
def baseEnd_618247 : Nat := 31353864118552873033999

theorem tailTrace_618247 : CollatzResearch.WordTrace tailWord_618247 prefixEnd_618247 31353864118552873033999 := by
  unfold tailWord_618247
  simp only [CollatzResearch.WordTrace]
  refine ⟨22549320591204182026404995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15032880394136121350936663 22549320591204182026404995)
  ·
    refine ⟨33823980886806273039607493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22549320591204182026404995 33823980886806273039607493)
    ·
      refine ⟨6341996416276176194926405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 33823980886806273039607493 6341996416276176194926405)
      ·
        refine ⟨1189124328051783036548701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6341996416276176194926405 1189124328051783036548701)
        ·
          refine ⟨445921623019418638705763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1189124328051783036548701 445921623019418638705763)
          ·
            refine ⟨668882434529127958058645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 445921623019418638705763 668882434529127958058645)
            ·
              refine ⟨31353864118552873033999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 668882434529127958058645 31353864118552873033999)
              ·
                rfl

theorem cell20_618247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 3, 1, 6].length) (baseStart_618247 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_618247 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_618247 prefixEnd_618247 := by exact prefixLift 618247
  have htrace : WordTrace (prefixWord ++ tailWord_618247) baseStart_618247 baseEnd_618247 := by
    simpa [prefixWord, tailWord_618247, baseEnd_618247] using wordTrace_append hprefix tailTrace_618247
  have hstable : (prefixWord ++ tailWord_618247).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_618247).length < 2 ^ (prefixWord ++ tailWord_618247).sum := by decide
  have hdescent : baseEnd_618247 < baseStart_618247 := by decide
  rcases family_descends (prefixWord ++ tailWord_618247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_618253 : List Nat := [1, 7, 2, 1, 1, 2, 1, 1, 4]
def baseStart_618253 : Nat := 118140960795 + 618253 * 2 ^ 59
def prefixEnd_618253 : Nat := 4983230072969 + 3 ^ 40 * 618253 * 2
def baseEnd_618253 : Nat := 282187515630466503105967

theorem tailTrace_618253 : CollatzResearch.WordTrace tailWord_618253 prefixEnd_618253 282187515630466503105967 := by
  unfold tailWord_618253
  simp only [CollatzResearch.WordTrace]
  refine ⟨22549539429182445051123413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15033026286121630034082275 22549539429182445051123413)
  ·
    refine ⟨528504830371463555885705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 22549539429182445051123413 528504830371463555885705)
    ·
      refine ⟨396378622778597666914279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 528504830371463555885705 396378622778597666914279)
      ·
        refine ⟨594567934167896500371419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 396378622778597666914279 594567934167896500371419)
        ·
          refine ⟨891851901251844750557129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 594567934167896500371419 891851901251844750557129)
          ·
            refine ⟨668888925938883562917847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 891851901251844750557129 668888925938883562917847)
            ·
              refine ⟨1003333388908325344376771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 668888925938883562917847 1003333388908325344376771)
              ·
                refine ⟨1505000083362488016565157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1003333388908325344376771 1505000083362488016565157)
                ·
                  refine ⟨282187515630466503105967, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1505000083362488016565157 282187515630466503105967)
                  ·
                    rfl

theorem cell20_618253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 2, 1, 1, 4].length) (baseStart_618253 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_618253 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_618253 prefixEnd_618253 := by exact prefixLift 618253
  have htrace : WordTrace (prefixWord ++ tailWord_618253) baseStart_618253 baseEnd_618253 := by
    simpa [prefixWord, tailWord_618253, baseEnd_618253] using wordTrace_append hprefix tailTrace_618253
  have hstable : (prefixWord ++ tailWord_618253).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_618253).length < 2 ^ (prefixWord ++ tailWord_618253).sum := by decide
  have hdescent : baseEnd_618253 < baseStart_618253 := by decide
  rcases family_descends (prefixWord ++ tailWord_618253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_618261 : List Nat := [1, 3, 2, 1, 2, 5, 1, 1, 4]
def baseStart_618261 : Nat := 118140960795 + 618261 * 2 ^ 59
def prefixEnd_618261 : Nat := 4983230072969 + 3 ^ 40 * 618261 * 2
def baseEnd_618261 : Nat := 282191167048454030839267

theorem tailTrace_618261 : CollatzResearch.WordTrace tailWord_618261 prefixEnd_618261 282191167048454030839267 := by
  unfold tailWord_618261
  simp only [CollatzResearch.WordTrace]
  refine ⟨22549831213153462417414637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15033220808768974944943091 22549831213153462417414637)
  ·
    refine ⟨8456186704932548406530489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22549831213153462417414637 8456186704932548406530489)
    ·
      refine ⟨6342140028699411304897867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8456186704932548406530489 6342140028699411304897867)
      ·
        refine ⟨9513210043049116957346801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6342140028699411304897867 9513210043049116957346801)
        ·
          refine ⟨7134907532286837718010101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9513210043049116957346801 7134907532286837718010101)
          ·
            refine ⟨668897581151891036063447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 7134907532286837718010101 668897581151891036063447)
            ·
              refine ⟨1003346371727836554095171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 668897581151891036063447 1003346371727836554095171)
              ·
                refine ⟨1505019557591754831142757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1003346371727836554095171 1505019557591754831142757)
                ·
                  refine ⟨282191167048454030839267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1505019557591754831142757 282191167048454030839267)
                  ·
                    rfl

theorem cell20_618261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 5, 1, 1, 4].length) (baseStart_618261 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_618261 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_618261 prefixEnd_618261 := by exact prefixLift 618261
  have htrace : WordTrace (prefixWord ++ tailWord_618261) baseStart_618261 baseEnd_618261 := by
    simpa [prefixWord, tailWord_618261, baseEnd_618261] using wordTrace_append hprefix tailTrace_618261
  have hstable : (prefixWord ++ tailWord_618261).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_618261).length < 2 ^ (prefixWord ++ tailWord_618261).sum := by decide
  have hdescent : baseEnd_618261 < baseStart_618261 := by decide
  rcases family_descends (prefixWord ++ tailWord_618261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_618289 : List Nat := [1, 2, 2, 3, 2, 2, 2, 6]
def baseStart_618289 : Nat := 118140960795 + 618289 * 2 ^ 59
def prefixEnd_618289 : Nat := 4983230072969 + 3 ^ 40 * 618289 * 2
def baseEnd_618289 : Nat := 94067982337136792635273

theorem tailTrace_618289 : CollatzResearch.WordTrace tailWord_618289 prefixEnd_618289 94067982337136792635273 := by
  unfold tailWord_618289
  simp only [CollatzResearch.WordTrace]
  refine ⟨22550852457052023199433921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15033901638034682132955947 22550852457052023199433921)
  ·
    refine ⟨16913139342789017399575441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22550852457052023199433921 16913139342789017399575441)
    ·
      refine ⟨12684854507091763049681581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16913139342789017399575441 12684854507091763049681581)
      ·
        refine ⟨4756820440159411143630593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12684854507091763049681581 4756820440159411143630593)
        ·
          refine ⟨3567615330119558357722945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4756820440159411143630593 3567615330119558357722945)
          ·
            refine ⟨2675711497589668768292209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3567615330119558357722945 2675711497589668768292209)
            ·
              refine ⟨2006783623192251576219157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2675711497589668768292209 2006783623192251576219157)
              ·
                refine ⟨94067982337136792635273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2006783623192251576219157 94067982337136792635273)
                ·
                  rfl

theorem cell20_618289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 2, 6].length) (baseStart_618289 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_618289 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_618289 prefixEnd_618289 := by exact prefixLift 618289
  have htrace : WordTrace (prefixWord ++ tailWord_618289) baseStart_618289 baseEnd_618289 := by
    simpa [prefixWord, tailWord_618289, baseEnd_618289] using wordTrace_append hprefix tailTrace_618289
  have hstable : (prefixWord ++ tailWord_618289).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_618289).length < 2 ^ (prefixWord ++ tailWord_618289).sum := by decide
  have hdescent : baseEnd_618289 < baseStart_618289 := by decide
  rcases family_descends (prefixWord ++ tailWord_618289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_618313 : List Nat := [1, 2, 1, 1, 2, 4, 4, 2, 3]
def baseStart_618313 : Nat := 118140960795 + 618313 * 2 ^ 59
def prefixEnd_618313 : Nat := 4983230072969 + 3 ^ 40 * 618313 * 2
def baseEnd_618313 : Nat := 282214901265372961105721

theorem tailTrace_618313 : CollatzResearch.WordTrace tailWord_618313 prefixEnd_618313 282214901265372961105721 := by
  unfold tailWord_618313
  simp only [CollatzResearch.WordTrace]
  refine ⟨22551727808965075298307593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15034485205976716865538395 22551727808965075298307593)
  ·
    refine ⟨16913795856723806473730695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22551727808965075298307593 16913795856723806473730695)
    ·
      refine ⟨25370693785085709710596043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16913795856723806473730695 25370693785085709710596043)
      ·
        refine ⟨38056040677628564565894065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25370693785085709710596043 38056040677628564565894065)
        ·
          refine ⟨28542030508221423424420549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38056040677628564565894065 28542030508221423424420549)
          ·
            refine ⟨5351630720291516892078853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 28542030508221423424420549 5351630720291516892078853)
            ·
              refine ⟨1003430760054659417264785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5351630720291516892078853 1003430760054659417264785)
              ·
                refine ⟨752573070040994562948589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1003430760054659417264785 752573070040994562948589)
                ·
                  refine ⟨282214901265372961105721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 752573070040994562948589 282214901265372961105721)
                  ·
                    rfl

theorem cell20_618313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 4, 2, 3].length) (baseStart_618313 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_618313 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_618313 prefixEnd_618313 := by exact prefixLift 618313
  have htrace : WordTrace (prefixWord ++ tailWord_618313) baseStart_618313 baseEnd_618313 := by
    simpa [prefixWord, tailWord_618313, baseEnd_618313] using wordTrace_append hprefix tailTrace_618313
  have hstable : (prefixWord ++ tailWord_618313).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_618313).length < 2 ^ (prefixWord ++ tailWord_618313).sum := by decide
  have hdescent : baseEnd_618313 < baseStart_618313 := by decide
  rcases family_descends (prefixWord ++ tailWord_618313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_618316 : List Nat := [2, 2, 1, 3, 4, 1, 1, 4, 2]
def baseStart_618316 : Nat := 118140960795 + 618316 * 2 ^ 59
def prefixEnd_618316 : Nat := 4983230072969 + 3 ^ 40 * 618316 * 2
def baseEnd_618316 : Nat := 282216270547118284005709

theorem tailTrace_618316 : CollatzResearch.WordTrace tailWord_618316 prefixEnd_618316 282216270547118284005709 := by
  unfold tailWord_618316
  simp only [CollatzResearch.WordTrace]
  refine ⟨11275918613977103405333401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15034558151969471207111201 11275918613977103405333401)
  ·
    refine ⟨8456938960482827554000051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11275918613977103405333401 8456938960482827554000051)
    ·
      refine ⟨12685408440724241331000077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8456938960482827554000051 12685408440724241331000077)
      ·
        refine ⟨4757028165271590499125029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12685408440724241331000077 4757028165271590499125029)
        ·
          refine ⟨891942780988423218585943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4757028165271590499125029 891942780988423218585943)
          ·
            refine ⟨1337914171482634827878915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 891942780988423218585943 1337914171482634827878915)
            ·
              refine ⟨2006871257223952241818373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1337914171482634827878915 2006871257223952241818373)
              ·
                refine ⟨376288360729491045340945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2006871257223952241818373 376288360729491045340945)
                ·
                  refine ⟨282216270547118284005709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 376288360729491045340945 282216270547118284005709)
                  ·
                    rfl

theorem cell20_618316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 1, 1, 4, 2].length) (baseStart_618316 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_618316 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_618316 prefixEnd_618316 := by exact prefixLift 618316
  have htrace : WordTrace (prefixWord ++ tailWord_618316) baseStart_618316 baseEnd_618316 := by
    simpa [prefixWord, tailWord_618316, baseEnd_618316] using wordTrace_append hprefix tailTrace_618316
  have hstable : (prefixWord ++ tailWord_618316).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_618316).length < 2 ^ (prefixWord ++ tailWord_618316).sum := by decide
  have hdescent : baseEnd_618316 < baseStart_618316 := by decide
  rcases family_descends (prefixWord ++ tailWord_618316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_618344 : List Nat := [2, 1, 4, 2, 1, 1, 5, 4]
def baseStart_618344 : Nat := 118140960795 + 618344 * 2 ^ 59
def prefixEnd_618344 : Nat := 4983230072969 + 3 ^ 40 * 618344 * 2
def baseEnd_618344 : Nat := 94076350170024877024087

theorem tailTrace_618344 : CollatzResearch.WordTrace tailWord_618344 prefixEnd_618344 94076350170024877024087 := by
  unfold tailWord_618344
  simp only [CollatzResearch.WordTrace]
  refine ⟨11276429235926383796343043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15035238981235178395124057 11276429235926383796343043)
  ·
    refine ⟨16914643853889575694514565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11276429235926383796343043 16914643853889575694514565)
    ·
      refine ⟨3171495722604295442721481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16914643853889575694514565 3171495722604295442721481)
      ·
        refine ⟨2378621791953221582041111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3171495722604295442721481 2378621791953221582041111)
        ·
          refine ⟨3567932687929832373061667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2378621791953221582041111 3567932687929832373061667)
          ·
            refine ⟨5351899031894748559592501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3567932687929832373061667 5351899031894748559592501)
            ·
              refine ⟨501740534240132677461797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5351899031894748559592501 501740534240132677461797)
              ·
                refine ⟨94076350170024877024087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 501740534240132677461797 94076350170024877024087)
                ·
                  rfl

theorem cell20_618344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 5, 4].length) (baseStart_618344 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_618344 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_618344 prefixEnd_618344 := by exact prefixLift 618344
  have htrace : WordTrace (prefixWord ++ tailWord_618344) baseStart_618344 baseEnd_618344 := by
    simpa [prefixWord, tailWord_618344, baseEnd_618344] using wordTrace_append hprefix tailTrace_618344
  have hstable : (prefixWord ++ tailWord_618344).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_618344).length < 2 ^ (prefixWord ++ tailWord_618344).sum := by decide
  have hdescent : baseEnd_618344 < baseStart_618344 := by decide
  rcases family_descends (prefixWord ++ tailWord_618344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_618375 : List Nat := [1, 1, 4, 2, 4, 1, 2, 1, 4]
def baseStart_618375 : Nat := 118140960795 + 618375 * 2 ^ 59
def prefixEnd_618375 : Nat := 4983230072969 + 3 ^ 40 * 618375 * 2
def baseEnd_618375 : Nat := 282243199754776301038801

theorem tailTrace_618375 : CollatzResearch.WordTrace tailWord_618375 prefixEnd_618375 282243199754776301038801 := by
  unfold tailWord_618375
  simp only [CollatzResearch.WordTrace]
  refine ⟨22553989134740459887064579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15035992756493639924709719 22553989134740459887064579)
  ·
    refine ⟨33830983702110689830596869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22553989134740459887064579 33830983702110689830596869)
    ·
      refine ⟨6343309444145754343236913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 33830983702110689830596869 6343309444145754343236913)
      ·
        refine ⟨4757482083109315757427685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6343309444145754343236913 4757482083109315757427685)
        ·
          refine ⟨892027890582996704517691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4757482083109315757427685 892027890582996704517691)
          ·
            refine ⟨1338041835874495056776537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 892027890582996704517691 1338041835874495056776537)
            ·
              refine ⟨1003531376905871292582403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1338041835874495056776537 1003531376905871292582403)
              ·
                refine ⟨1505297065358806938873605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1003531376905871292582403 1505297065358806938873605)
                ·
                  refine ⟨282243199754776301038801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1505297065358806938873605 282243199754776301038801)
                  ·
                    rfl

theorem cell20_618375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 1, 2, 1, 4].length) (baseStart_618375 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_618375 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_618375 prefixEnd_618375 := by exact prefixLift 618375
  have htrace : WordTrace (prefixWord ++ tailWord_618375) baseStart_618375 baseEnd_618375 := by
    simpa [prefixWord, tailWord_618375, baseEnd_618375] using wordTrace_append hprefix tailTrace_618375
  have hstable : (prefixWord ++ tailWord_618375).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_618375).length < 2 ^ (prefixWord ++ tailWord_618375).sum := by decide
  have hdescent : baseEnd_618375 < baseStart_618375 := by decide
  rcases family_descends (prefixWord ++ tailWord_618375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_618399 : List Nat := [1, 1, 2, 5, 3, 2, 2, 4]
def baseStart_618399 : Nat := 118140960795 + 618399 * 2 ^ 59
def prefixEnd_618399 : Nat := 4983230072969 + 3 ^ 40 * 618399 * 2
def baseEnd_618399 : Nat := 94084718002912961412901

theorem tailTrace_618399 : CollatzResearch.WordTrace tailWord_618399 prefixEnd_618399 94084718002912961412901 := by
  unfold tailWord_618399
  simp only [CollatzResearch.WordTrace]
  refine ⟨22554864486653511985938251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15036576324435674657292167 22554864486653511985938251)
  ·
    refine ⟨33832296729980267978907377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22554864486653511985938251 33832296729980267978907377)
    ·
      refine ⟨25374222547485200984180533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33832296729980267978907377 25374222547485200984180533)
      ·
        refine ⟨2378833363826737592266925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 25374222547485200984180533 2378833363826737592266925)
        ·
          refine ⟨892062511435026597100097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2378833363826737592266925 892062511435026597100097)
          ·
            refine ⟨669046883576269947825073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 892062511435026597100097 669046883576269947825073)
            ·
              refine ⟨501785162682202460868805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 669046883576269947825073 501785162682202460868805)
              ·
                refine ⟨94084718002912961412901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 501785162682202460868805 94084718002912961412901)
                ·
                  rfl

theorem cell20_618399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 2, 2, 4].length) (baseStart_618399 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_618399 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_618399 prefixEnd_618399 := by exact prefixLift 618399
  have htrace : WordTrace (prefixWord ++ tailWord_618399) baseStart_618399 baseEnd_618399 := by
    simpa [prefixWord, tailWord_618399, baseEnd_618399] using wordTrace_append hprefix tailTrace_618399
  have hstable : (prefixWord ++ tailWord_618399).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_618399).length < 2 ^ (prefixWord ++ tailWord_618399).sum := by decide
  have hdescent : baseEnd_618399 < baseStart_618399 := by decide
  rcases family_descends (prefixWord ++ tailWord_618399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_618444 : List Nat := [2, 2, 1, 4, 1, 2, 4, 1, 3]
def baseStart_618444 : Nat := 118140960795 + 618444 * 2 ^ 59
def prefixEnd_618444 : Nat := 4983230072969 + 3 ^ 40 * 618444 * 2
def baseEnd_618444 : Nat := 282274693234918727738519

theorem tailTrace_618444 : CollatzResearch.WordTrace tailWord_618444 prefixEnd_618444 282274693234918727738519 := by
  unfold tailWord_618444
  simp only [CollatzResearch.WordTrace]
  refine ⟨11278252885745242335663193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15037670514326989780884257 11278252885745242335663193)
  ·
    refine ⟨8458689664308931751747395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11278252885745242335663193 8458689664308931751747395)
    ·
      refine ⟨12688034496463397627621093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8458689664308931751747395 12688034496463397627621093)
      ·
        refine ⟨2379006468086887055178955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12688034496463397627621093 2379006468086887055178955)
        ·
          refine ⟨3568509702130330582768433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2379006468086887055178955 3568509702130330582768433)
          ·
            refine ⟨2676382276597747937076325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3568509702130330582768433 2676382276597747937076325)
            ·
              refine ⟨501821676862077738201811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2676382276597747937076325 501821676862077738201811)
              ·
                refine ⟨752732515293116607302717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 501821676862077738201811 752732515293116607302717)
                ·
                  refine ⟨282274693234918727738519, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 752732515293116607302717 282274693234918727738519)
                  ·
                    rfl

theorem cell20_618444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 4, 1, 3].length) (baseStart_618444 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_618444 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_618444 prefixEnd_618444 := by exact prefixLift 618444
  have htrace : WordTrace (prefixWord ++ tailWord_618444) baseStart_618444 baseEnd_618444 := by
    simpa [prefixWord, tailWord_618444, baseEnd_618444] using wordTrace_append hprefix tailTrace_618444
  have hstable : (prefixWord ++ tailWord_618444).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_618444).length < 2 ^ (prefixWord ++ tailWord_618444).sum := by decide
  have hdescent : baseEnd_618444 < baseStart_618444 := by decide
  rcases family_descends (prefixWord ++ tailWord_618444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_618455 : List Nat := [1, 1, 3, 2, 1, 1, 4, 1, 6]
def baseStart_618455 : Nat := 118140960795 + 618455 * 2 ^ 59
def prefixEnd_618455 : Nat := 4983230072969 + 3 ^ 40 * 618455 * 2
def baseEnd_618455 : Nat := 282279713934651578371807

theorem tailTrace_618455 : CollatzResearch.WordTrace tailWord_618455 prefixEnd_618455 282279713934651578371807 := by
  unfold tailWord_618455
  simp only [CollatzResearch.WordTrace]
  refine ⟨22556906974450633549976819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15037937982967089033317879 22556906974450633549976819)
  ·
    refine ⟨33835360461675950324965229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22556906974450633549976819 33835360461675950324965229)
    ·
      refine ⟨12688260173128481371861961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33835360461675950324965229 12688260173128481371861961)
      ·
        refine ⟨9516195129846361028896471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12688260173128481371861961 9516195129846361028896471)
        ·
          refine ⟨14274292694769541543344707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9516195129846361028896471 14274292694769541543344707)
          ·
            refine ⟨21411439042154312315017061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14274292694769541543344707 21411439042154312315017061)
            ·
              refine ⟨4014644820403933559065699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21411439042154312315017061 4014644820403933559065699)
              ·
                refine ⟨6021967230605900338598549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4014644820403933559065699 6021967230605900338598549)
                ·
                  refine ⟨282279713934651578371807, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6021967230605900338598549 282279713934651578371807)
                  ·
                    rfl

theorem cell20_618455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 4, 1, 6].length) (baseStart_618455 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_618455 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_618455 prefixEnd_618455 := by exact prefixLift 618455
  have htrace : WordTrace (prefixWord ++ tailWord_618455) baseStart_618455 baseEnd_618455 := by
    simpa [prefixWord, tailWord_618455, baseEnd_618455] using wordTrace_append hprefix tailTrace_618455
  have hstable : (prefixWord ++ tailWord_618455).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_618455).length < 2 ^ (prefixWord ++ tailWord_618455).sum := by decide
  have hdescent : baseEnd_618455 < baseStart_618455 := by decide
  rcases family_descends (prefixWord ++ tailWord_618455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_618489 : List Nat := [1, 2, 1, 3, 1, 5, 1, 4, 2]
def baseStart_618489 : Nat := 118140960795 + 618489 * 2 ^ 59
def prefixEnd_618489 : Nat := 4983230072969 + 3 ^ 40 * 618489 * 2
def baseEnd_618489 : Nat := 282295232461098571238335

theorem tailTrace_618489 : CollatzResearch.WordTrace tailWord_618489 prefixEnd_618489 282295232461098571238335 := by
  unfold tailWord_618489
  simp only [CollatzResearch.WordTrace]
  refine ⟨22558147056327457356714521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15038764704218304904476347 22558147056327457356714521)
  ·
    refine ⟨16918610292245593017535891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22558147056327457356714521 16918610292245593017535891)
    ·
      refine ⟨25377915438368389526303837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16918610292245593017535891 25377915438368389526303837)
      ·
        refine ⟨9516718289388146072363939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25377915438368389526303837 9516718289388146072363939)
        ·
          refine ⟨14275077434082219108545909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9516718289388146072363939 14275077434082219108545909)
          ·
            refine ⟨1338288509445208041426179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 14275077434082219108545909 1338288509445208041426179)
            ·
              refine ⟨2007432764167812062139269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1338288509445208041426179 2007432764167812062139269)
              ·
                refine ⟨376393643281464761651113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2007432764167812062139269 376393643281464761651113)
                ·
                  refine ⟨282295232461098571238335, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 376393643281464761651113 282295232461098571238335)
                  ·
                    rfl

theorem cell20_618489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 5, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 5, 1, 4, 2].length) (baseStart_618489 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_618489 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_618489 prefixEnd_618489 := by exact prefixLift 618489
  have htrace : WordTrace (prefixWord ++ tailWord_618489) baseStart_618489 baseEnd_618489 := by
    simpa [prefixWord, tailWord_618489, baseEnd_618489] using wordTrace_append hprefix tailTrace_618489
  have hstable : (prefixWord ++ tailWord_618489).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_618489).length < 2 ^ (prefixWord ++ tailWord_618489).sum := by decide
  have hdescent : baseEnd_618489 < baseStart_618489 := by decide
  rcases family_descends (prefixWord ++ tailWord_618489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_618502 : List Nat := [6, 2, 1, 2, 1, 1, 1, 2, 4]
def baseStart_618502 : Nat := 118140960795 + 618502 * 2 ^ 59
def prefixEnd_618502 : Nat := 4983230072969 + 3 ^ 40 * 618502 * 2
def baseEnd_618502 : Nat := 282301166015328303804949

theorem tailTrace_618502 : CollatzResearch.WordTrace tailWord_618502 prefixEnd_618502 282301166015328303804949 := by
  unfold tailWord_618502
  simp only [CollatzResearch.WordTrace]
  refine ⟨704956912665011268029305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 15039080803520240384625173 704956912665011268029305)
  ·
    refine ⟨528717684498758451021979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 704956912665011268029305 528717684498758451021979)
    ·
      refine ⟨793076526748137676532969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 528717684498758451021979 793076526748137676532969)
      ·
        refine ⟨594807395061103257399727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 793076526748137676532969 594807395061103257399727)
        ·
          refine ⟨892211092591654886099591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 594807395061103257399727 892211092591654886099591)
          ·
            refine ⟨1338316638887482329149387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 892211092591654886099591 1338316638887482329149387)
            ·
              refine ⟨2007474958331223493724081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1338316638887482329149387 2007474958331223493724081)
              ·
                refine ⟨1505606218748417620293061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2007474958331223493724081 1505606218748417620293061)
                ·
                  refine ⟨282301166015328303804949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1505606218748417620293061 282301166015328303804949)
                  ·
                    rfl

theorem cell20_618502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 1, 1, 2, 4].length) (baseStart_618502 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_618502 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_618502 prefixEnd_618502 := by exact prefixLift 618502
  have htrace : WordTrace (prefixWord ++ tailWord_618502) baseStart_618502 baseEnd_618502 := by
    simpa [prefixWord, tailWord_618502, baseEnd_618502] using wordTrace_append hprefix tailTrace_618502
  have hstable : (prefixWord ++ tailWord_618502).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_618502).length < 2 ^ (prefixWord ++ tailWord_618502).sum := by decide
  have hdescent : baseEnd_618502 < baseStart_618502 := by decide
  rcases family_descends (prefixWord ++ tailWord_618502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_618503 : List Nat := [1, 1, 4, 3, 1, 2, 2, 3, 3]
def baseStart_618503 : Nat := 118140960795 + 618503 * 2 ^ 59
def prefixEnd_618503 : Nat := 4983230072969 + 3 ^ 40 * 618503 * 2
def baseEnd_618503 : Nat := 282301622442576744771611

theorem tailTrace_618503 : CollatzResearch.WordTrace tailWord_618503 prefixEnd_618503 282301622442576744771611 := by
  unfold tailWord_618503
  simp only [CollatzResearch.WordTrace]
  refine ⟨22558657678276737747724163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15039105118851158498482775 22558657678276737747724163)
  ·
    refine ⟨33837986517415106621586245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22558657678276737747724163 33837986517415106621586245)
    ·
      refine ⟨6344622472015332491547421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 33837986517415106621586245 6344622472015332491547421)
      ·
        refine ⟨2379233427005749684330283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6344622472015332491547421 2379233427005749684330283)
        ·
          refine ⟨3568850140508624526495425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2379233427005749684330283 3568850140508624526495425)
          ·
            refine ⟨2676637605381468394871569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3568850140508624526495425 2676637605381468394871569)
            ·
              refine ⟨2007478204036101296153677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2676637605381468394871569 2007478204036101296153677)
              ·
                refine ⟨752804326513537986057629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2007478204036101296153677 752804326513537986057629)
                ·
                  refine ⟨282301622442576744771611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 752804326513537986057629 282301622442576744771611)
                  ·
                    rfl

theorem cell20_618503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 2, 3, 3].length) (baseStart_618503 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_618503 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_618503 prefixEnd_618503 := by exact prefixLift 618503
  have htrace : WordTrace (prefixWord ++ tailWord_618503) baseStart_618503 baseEnd_618503 := by
    simpa [prefixWord, tailWord_618503, baseEnd_618503] using wordTrace_append hprefix tailTrace_618503
  have hstable : (prefixWord ++ tailWord_618503).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_618503).length < 2 ^ (prefixWord ++ tailWord_618503).sum := by decide
  have hdescent : baseEnd_618503 < baseStart_618503 := by decide
  rcases family_descends (prefixWord ++ tailWord_618503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_618509 : List Nat := [1, 7, 1, 2, 1, 1, 3, 4]
def baseStart_618509 : Nat := 118140960795 + 618509 * 2 ^ 59
def prefixEnd_618509 : Nat := 4983230072969 + 3 ^ 40 * 618509 * 2
def baseEnd_618509 : Nat := 94101453668689130190529

theorem tailTrace_618509 : CollatzResearch.WordTrace tailWord_618509 prefixEnd_618509 94101453668689130190529 := by
  unfold tailWord_618509
  simp only [CollatzResearch.WordTrace]
  refine ⟨22558876516255000772442581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15039251010836667181628387 22558876516255000772442581)
  ·
    refine ⟨528723668349726580604123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 22558876516255000772442581 528723668349726580604123)
    ·
      refine ⟨793085502524589870906185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 528723668349726580604123 793085502524589870906185)
      ·
        refine ⟨594814126893442403179639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 793085502524589870906185 594814126893442403179639)
        ·
          refine ⟨892221190340163604769459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 594814126893442403179639 892221190340163604769459)
          ·
            refine ⟨1338331785510245407154189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 892221190340163604769459 1338331785510245407154189)
            ·
              refine ⟨501874419566342027682821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1338331785510245407154189 501874419566342027682821)
              ·
                refine ⟨94101453668689130190529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 501874419566342027682821 94101453668689130190529)
                ·
                  rfl

theorem cell20_618509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 1, 3, 4].length) (baseStart_618509 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_618509 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_618509 prefixEnd_618509 := by exact prefixLift 618509
  have htrace : WordTrace (prefixWord ++ tailWord_618509) baseStart_618509 baseEnd_618509 := by
    simpa [prefixWord, tailWord_618509, baseEnd_618509] using wordTrace_append hprefix tailTrace_618509
  have hstable : (prefixWord ++ tailWord_618509).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_618509).length < 2 ^ (prefixWord ++ tailWord_618509).sum := by decide
  have hdescent : baseEnd_618509 < baseStart_618509 := by decide
  rcases family_descends (prefixWord ++ tailWord_618509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_618510 : List Nat := [4, 1, 1, 2, 2, 1, 3, 2, 4]
def baseStart_618510 : Nat := 118140960795 + 618510 * 2 ^ 59
def prefixEnd_618510 : Nat := 4983230072969 + 3 ^ 40 * 618510 * 2
def baseEnd_618510 : Nat := 282304817433315831538249

theorem tailTrace_618510 : CollatzResearch.WordTrace tailWord_618510 prefixEnd_618510 282304817433315831538249 := by
  unfold tailWord_618510
  simp only [CollatzResearch.WordTrace]
  refine ⟨2819864123656422242903623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15039275326167585295485989 2819864123656422242903623)
  ·
    refine ⟨4229796185484633364355435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2819864123656422242903623 4229796185484633364355435)
    ·
      refine ⟨6344694278226950046533153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4229796185484633364355435 6344694278226950046533153)
      ·
        refine ⟨4758520708670212534899865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6344694278226950046533153 4758520708670212534899865)
        ·
          refine ⟨3568890531502659401174899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4758520708670212534899865 3568890531502659401174899)
          ·
            refine ⟨5353335797253989101762349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3568890531502659401174899 5353335797253989101762349)
            ·
              refine ⟨2007500923970245913160881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5353335797253989101762349 2007500923970245913160881)
              ·
                refine ⟨1505625692977684434870661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2007500923970245913160881 1505625692977684434870661)
                ·
                  refine ⟨282304817433315831538249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1505625692977684434870661 282304817433315831538249)
                  ·
                    rfl

theorem cell20_618510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 3, 2, 4].length) (baseStart_618510 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_618510 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_618510 prefixEnd_618510 := by exact prefixLift 618510
  have htrace : WordTrace (prefixWord ++ tailWord_618510) baseStart_618510 baseEnd_618510 := by
    simpa [prefixWord, tailWord_618510, baseEnd_618510] using wordTrace_append hprefix tailTrace_618510
  have hstable : (prefixWord ++ tailWord_618510).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_618510).length < 2 ^ (prefixWord ++ tailWord_618510).sum := by decide
  have hdescent : baseEnd_618510 < baseStart_618510 := by decide
  rcases family_descends (prefixWord ++ tailWord_618510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_618527 : List Nat := [1, 1, 2, 4, 1, 2, 4, 3, 2]
def baseStart_618527 : Nat := 118140960795 + 618527 * 2 ^ 59
def prefixEnd_618527 : Nat := 4983230072969 + 3 ^ 40 * 618527 * 2
def baseEnd_618527 : Nat := 282312576696539327971513

theorem tailTrace_618527 : CollatzResearch.WordTrace tailWord_618527 prefixEnd_618527 282312576696539327971513 := by
  unfold tailWord_618527
  simp only [CollatzResearch.WordTrace]
  refine ⟨22559533030189789846597835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15039688686793193231065223 22559533030189789846597835)
  ·
    refine ⟨33839299545284684769896753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22559533030189789846597835 33839299545284684769896753)
    ·
      refine ⟨25379474658963513577422565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33839299545284684769896753 25379474658963513577422565)
      ·
        refine ⟨4758651498555658795766731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 25379474658963513577422565 4758651498555658795766731)
        ·
          refine ⟨7137977247833488193650097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4758651498555658795766731 7137977247833488193650097)
          ·
            refine ⟨5353482935875116145237573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7137977247833488193650097 5353482935875116145237573)
            ·
              refine ⟨1003778050476584277232045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5353482935875116145237573 1003778050476584277232045)
              ·
                refine ⟨376416768928719103962017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1003778050476584277232045 376416768928719103962017)
                ·
                  refine ⟨282312576696539327971513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 376416768928719103962017 282312576696539327971513)
                  ·
                    rfl

theorem cell20_618527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 4, 3, 2].length) (baseStart_618527 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_618527 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_618527 prefixEnd_618527 := by exact prefixLift 618527
  have htrace : WordTrace (prefixWord ++ tailWord_618527) baseStart_618527 baseEnd_618527 := by
    simpa [prefixWord, tailWord_618527, baseEnd_618527] using wordTrace_append hprefix tailTrace_618527
  have hstable : (prefixWord ++ tailWord_618527).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_618527).length < 2 ^ (prefixWord ++ tailWord_618527).sum := by decide
  have hdescent : baseEnd_618527 < baseStart_618527 := by decide
  rcases family_descends (prefixWord ++ tailWord_618527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_618531 : List Nat := [1, 1, 1, 4, 3, 1, 1, 2, 6]
def baseStart_618531 : Nat := 118140960795 + 618531 * 2 ^ 59
def prefixEnd_618531 : Nat := 4983230072969 + 3 ^ 40 * 618531 * 2
def baseEnd_618531 : Nat := 282314402405533091838163

theorem tailTrace_618531 : CollatzResearch.WordTrace tailWord_618531 prefixEnd_618531 282314402405533091838163 := by
  unfold tailWord_618531
  simp only [CollatzResearch.WordTrace]
  refine ⟨22559678922175298529743447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15039785948116865686495631 22559678922175298529743447)
  ·
    refine ⟨33839518383262947794615171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22559678922175298529743447 33839518383262947794615171)
    ·
      refine ⟨50759277574894421691922757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33839518383262947794615171 50759277574894421691922757)
      ·
        refine ⟨9517364545292704067235517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 50759277574894421691922757 9517364545292704067235517)
        ·
          refine ⟨3569011704484764025213319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9517364545292704067235517 3569011704484764025213319)
          ·
            refine ⟨5353517556727146037819979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3569011704484764025213319 5353517556727146037819979)
            ·
              refine ⟨8030276335090719056729969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5353517556727146037819979 8030276335090719056729969)
              ·
                refine ⟨6022707251318039292547477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8030276335090719056729969 6022707251318039292547477)
                ·
                  refine ⟨282314402405533091838163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6022707251318039292547477 282314402405533091838163)
                  ·
                    rfl

theorem cell20_618531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 1, 2, 6].length) (baseStart_618531 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_618531 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_618531 prefixEnd_618531 := by exact prefixLift 618531
  have htrace : WordTrace (prefixWord ++ tailWord_618531) baseStart_618531 baseEnd_618531 := by
    simpa [prefixWord, tailWord_618531, baseEnd_618531] using wordTrace_append hprefix tailTrace_618531
  have hstable : (prefixWord ++ tailWord_618531).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_618531).length < 2 ^ (prefixWord ++ tailWord_618531).sum := by decide
  have hdescent : baseEnd_618531 < baseStart_618531 := by decide
  rcases family_descends (prefixWord ++ tailWord_618531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_618569 : List Nat := [1, 2, 1, 1, 2, 2, 3, 4, 4]
def baseStart_618569 : Nat := 118140960795 + 618569 * 2 ^ 59
def prefixEnd_618569 : Nat := 4983230072969 + 3 ^ 40 * 618569 * 2
def baseEnd_618569 : Nat := 282331746640973848571341

theorem tailTrace_618569 : CollatzResearch.WordTrace tailWord_618569 prefixEnd_618569 282331746640973848571341 := by
  unfold tailWord_618569
  simp only [CollatzResearch.WordTrace]
  refine ⟨22561064896037631019626761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15040709930691754013084507 22561064896037631019626761)
  ·
    refine ⟨16920798672028223264720071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22561064896037631019626761 16920798672028223264720071)
    ·
      refine ⟨25381198008042334897080107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16920798672028223264720071 25381198008042334897080107)
      ·
        refine ⟨38071797012063502345620161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25381198008042334897080107 38071797012063502345620161)
        ·
          refine ⟨28553847759047626759215121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38071797012063502345620161 28553847759047626759215121)
          ·
            refine ⟨21415385819285720069411341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28553847759047626759215121 21415385819285720069411341)
            ·
              refine ⟨8030769682232145026029253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21415385819285720069411341 8030769682232145026029253)
              ·
                refine ⟨1505769315418527192380485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8030769682232145026029253 1505769315418527192380485)
                ·
                  refine ⟨282331746640973848571341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1505769315418527192380485 282331746640973848571341)
                  ·
                    rfl

theorem cell20_618569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 3, 4, 4].length) (baseStart_618569 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_618569 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_618569 prefixEnd_618569 := by exact prefixLift 618569
  have htrace : WordTrace (prefixWord ++ tailWord_618569) baseStart_618569 baseEnd_618569 := by
    simpa [prefixWord, tailWord_618569, baseEnd_618569] using wordTrace_append hprefix tailTrace_618569
  have hstable : (prefixWord ++ tailWord_618569).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_618569).length < 2 ^ (prefixWord ++ tailWord_618569).sum := by decide
  have hdescent : baseEnd_618569 < baseStart_618569 := by decide
  rcases family_descends (prefixWord ++ tailWord_618569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_618617 : List Nat := [1, 2, 1, 3, 4, 2, 1, 3, 3]
def baseStart_618617 : Nat := 118140960795 + 618617 * 2 ^ 59
def prefixEnd_618617 : Nat := 4983230072969 + 3 ^ 40 * 618617 * 2
def baseEnd_618617 : Nat := 282353655148899014971145

theorem tailTrace_618617 : CollatzResearch.WordTrace tailWord_618617 prefixEnd_618617 282353655148899014971145 := by
  unfold tailWord_618617
  simp only [CollatzResearch.WordTrace]
  refine ⟨22562815599863735217374105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15041877066575823478249403 22562815599863735217374105)
  ·
    refine ⟨16922111699897801413030579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22562815599863735217374105 16922111699897801413030579)
    ·
      refine ⟨25383167549846702119545869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16922111699897801413030579 25383167549846702119545869)
      ·
        refine ⟨9518687831192513294829701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25383167549846702119545869 9518687831192513294829701)
        ·
          refine ⟨1784753968348596242780569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9518687831192513294829701 1784753968348596242780569)
          ·
            refine ⟨1338565476261447182085427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1784753968348596242780569 1338565476261447182085427)
            ·
              refine ⟨2007848214392170773128141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1338565476261447182085427 2007848214392170773128141)
              ·
                refine ⟨752943080397064039923053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2007848214392170773128141 752943080397064039923053)
                ·
                  refine ⟨282353655148899014971145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 752943080397064039923053 282353655148899014971145)
                  ·
                    rfl

theorem cell20_618617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 2, 1, 3, 3].length) (baseStart_618617 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_618617 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_618617 prefixEnd_618617 := by exact prefixLift 618617
  have htrace : WordTrace (prefixWord ++ tailWord_618617) baseStart_618617 baseEnd_618617 := by
    simpa [prefixWord, tailWord_618617, baseEnd_618617] using wordTrace_append hprefix tailTrace_618617
  have hstable : (prefixWord ++ tailWord_618617).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_618617).length < 2 ^ (prefixWord ++ tailWord_618617).sum := by decide
  have hdescent : baseEnd_618617 < baseStart_618617 := by decide
  rcases family_descends (prefixWord ++ tailWord_618617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_618654 : List Nat := [4, 3, 1, 1, 3, 2, 2, 2, 2]
def baseStart_618654 : Nat := 118140960795 + 618654 * 2 ^ 59
def prefixEnd_618654 : Nat := 4983230072969 + 3 ^ 40 * 618654 * 2
def baseEnd_618654 : Nat := 282370542957091330737661

theorem tailTrace_618654 : CollatzResearch.WordTrace tailWord_618654 prefixEnd_618654 282370542957091330737661 := by
  unfold tailWord_618654
  simp only [CollatzResearch.WordTrace]
  refine ⟨2820520637591211317058877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15042776733819793690980677 2820520637591211317058877)
  ·
    refine ⟨1057695239096704243897079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2820520637591211317058877 1057695239096704243897079)
    ·
      refine ⟨1586542858645056365845619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1057695239096704243897079 1586542858645056365845619)
      ·
        refine ⟨2379814287967584548768429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1586542858645056365845619 2379814287967584548768429)
        ·
          refine ⟨892430357987844205788161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2379814287967584548768429 892430357987844205788161)
          ·
            refine ⟨669322768490883154341121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 892430357987844205788161 669322768490883154341121)
            ·
              refine ⟨501992076368162365755841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 669322768490883154341121 501992076368162365755841)
              ·
                refine ⟨376494057276121774316881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 501992076368162365755841 376494057276121774316881)
                ·
                  refine ⟨282370542957091330737661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 376494057276121774316881 282370542957091330737661)
                  ·
                    rfl

theorem cell20_618654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 2, 2, 2, 2].length) (baseStart_618654 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_618654 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_618654 prefixEnd_618654 := by exact prefixLift 618654
  have htrace : WordTrace (prefixWord ++ tailWord_618654) baseStart_618654 baseEnd_618654 := by
    simpa [prefixWord, tailWord_618654, baseEnd_618654] using wordTrace_append hprefix tailTrace_618654
  have hstable : (prefixWord ++ tailWord_618654).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_618654).length < 2 ^ (prefixWord ++ tailWord_618654).sum := by decide
  have hdescent : baseEnd_618654 < baseStart_618654 := by decide
  rcases family_descends (prefixWord ++ tailWord_618654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_618655 : List Nat := [1, 1, 2, 6, 1, 1, 1, 4, 3]
def baseStart_618655 : Nat := 118140960795 + 618655 * 2 ^ 59
def prefixEnd_618655 : Nat := 4983230072969 + 3 ^ 40 * 618655 * 2
def baseEnd_618655 : Nat := 282370999384339771704323

theorem tailTrace_618655 : CollatzResearch.WordTrace tailWord_618655 prefixEnd_618655 282370999384339771704323 := by
  unfold tailWord_618655
  simp only [CollatzResearch.WordTrace]
  refine ⟨22564201573726067707257419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15042801049150711804838279 22564201573726067707257419)
  ·
    refine ⟨33846302360589101560886129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22564201573726067707257419 33846302360589101560886129)
    ·
      refine ⟨25384726770441826170664597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33846302360589101560886129 25384726770441826170664597)
      ·
        refine ⟨1189909067364460601749903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 25384726770441826170664597 1189909067364460601749903)
        ·
          refine ⟨1784863601046690902624855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1189909067364460601749903 1784863601046690902624855)
          ·
            refine ⟨2677295401570036353937283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1784863601046690902624855 2677295401570036353937283)
            ·
              refine ⟨4015943102355054530905925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2677295401570036353937283 4015943102355054530905925)
              ·
                refine ⟨752989331691572724544861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4015943102355054530905925 752989331691572724544861)
                ·
                  refine ⟨282370999384339771704323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 752989331691572724544861 282370999384339771704323)
                  ·
                    rfl

theorem cell20_618655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 1, 4, 3].length) (baseStart_618655 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_618655 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_618655 prefixEnd_618655 := by exact prefixLift 618655
  have htrace : WordTrace (prefixWord ++ tailWord_618655) baseStart_618655 baseEnd_618655 := by
    simpa [prefixWord, tailWord_618655, baseEnd_618655] using wordTrace_append hprefix tailTrace_618655
  have hstable : (prefixWord ++ tailWord_618655).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_618655).length < 2 ^ (prefixWord ++ tailWord_618655).sum := by decide
  have hdescent : baseEnd_618655 < baseStart_618655 := by decide
  rcases family_descends (prefixWord ++ tailWord_618655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_618658 : List Nat := [3, 3, 1, 3, 1, 2, 1, 4, 2]
def baseStart_618658 : Nat := 118140960795 + 618658 * 2 ^ 59
def prefixEnd_618658 : Nat := 4983230072969 + 3 ^ 40 * 618658 * 2
def baseEnd_618658 : Nat := 282372368666085094604311

theorem tailTrace_618658 : CollatzResearch.WordTrace tailWord_618658 prefixEnd_618658 282372368666085094604311 := by
  unfold tailWord_618658
  simp only [CollatzResearch.WordTrace]
  refine ⟨5641077748178799804904157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15042873995143466146411085 5641077748178799804904157)
  ·
    refine ⟨2115404155567049926839059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5641077748178799804904157 2115404155567049926839059)
    ·
      refine ⟨3173106233350574890258589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2115404155567049926839059 3173106233350574890258589)
      ·
        refine ⟨1189914837506465583846971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3173106233350574890258589 1189914837506465583846971)
        ·
          refine ⟨1784872256259698375770457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1189914837506465583846971 1784872256259698375770457)
          ·
            refine ⟨1338654192194773781827843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1784872256259698375770457 1338654192194773781827843)
            ·
              refine ⟨2007981288292160672741765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1338654192194773781827843 2007981288292160672741765)
              ·
                refine ⟨376496491554780126139081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2007981288292160672741765 376496491554780126139081)
                ·
                  refine ⟨282372368666085094604311, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 376496491554780126139081 282372368666085094604311)
                  ·
                    rfl

theorem cell20_618658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 2, 1, 4, 2].length) (baseStart_618658 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_618658 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_618658 prefixEnd_618658 := by exact prefixLift 618658
  have htrace : WordTrace (prefixWord ++ tailWord_618658) baseStart_618658 baseEnd_618658 := by
    simpa [prefixWord, tailWord_618658, baseEnd_618658] using wordTrace_append hprefix tailTrace_618658
  have hstable : (prefixWord ++ tailWord_618658).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_618658).length < 2 ^ (prefixWord ++ tailWord_618658).sum := by decide
  have hdescent : baseEnd_618658 < baseStart_618658 := by decide
  rcases family_descends (prefixWord ++ tailWord_618658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_618683 : List Nat := [1, 1, 1, 1, 1, 2, 7, 2, 4]
def baseStart_618683 : Nat := 118140960795 + 618683 * 2 ^ 59
def prefixEnd_618683 : Nat := 4983230072969 + 3 ^ 40 * 618683 * 2
def baseEnd_618683 : Nat := 282383779347296118770875

theorem tailTrace_618683 : CollatzResearch.WordTrace tailWord_618683 prefixEnd_618683 282383779347296118770875 := by
  unfold tailWord_618683
  simp only [CollatzResearch.WordTrace]
  refine ⟨22565222817624628489276703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15043481878416418992851135 22565222817624628489276703)
  ·
    refine ⟨33847834226436942733915055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22565222817624628489276703 33847834226436942733915055)
    ·
      refine ⟨50771751339655414100872583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33847834226436942733915055 50771751339655414100872583)
      ·
        refine ⟨76157627009483121151308875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50771751339655414100872583 76157627009483121151308875)
        ·
          refine ⟨114236440514224681726963313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76157627009483121151308875 114236440514224681726963313)
          ·
            refine ⟨85677330385668511295222485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 114236440514224681726963313 85677330385668511295222485)
            ·
              refine ⟨2008062430914105733481777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 85677330385668511295222485 2008062430914105733481777)
              ·
                refine ⟨1506046823185579300111333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2008062430914105733481777 1506046823185579300111333)
                ·
                  refine ⟨282383779347296118770875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1506046823185579300111333 282383779347296118770875)
                  ·
                    rfl

theorem cell20_618683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 7, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 7, 2, 4].length) (baseStart_618683 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_618683 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_618683 prefixEnd_618683 := by exact prefixLift 618683
  have htrace : WordTrace (prefixWord ++ tailWord_618683) baseStart_618683 baseEnd_618683 := by
    simpa [prefixWord, tailWord_618683, baseEnd_618683] using wordTrace_append hprefix tailTrace_618683
  have hstable : (prefixWord ++ tailWord_618683).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_618683).length < 2 ^ (prefixWord ++ tailWord_618683).sum := by decide
  have hdescent : baseEnd_618683 < baseStart_618683 := by decide
  rcases family_descends (prefixWord ++ tailWord_618683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_618710 : List Nat := [5, 2, 1, 2, 1, 2, 1, 1, 5]
def baseStart_618710 : Nat := 118140960795 + 618710 * 2 ^ 59
def prefixEnd_618710 : Nat := 4983230072969 + 3 ^ 40 * 618710 * 2
def baseEnd_618710 : Nat := 282396102883004024870765

theorem tailTrace_618710 : CollatzResearch.WordTrace tailWord_618710 prefixEnd_618710 282396102883004024870765 := by
  unfold tailWord_618710
  simp only [CollatzResearch.WordTrace]
  refine ⟨1410387974282925756281849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 15044138392351208067006389 1410387974282925756281849)
  ·
    refine ⟨1057790980712194317211387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1410387974282925756281849 1057790980712194317211387)
    ·
      refine ⟨1586686471068291475817081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1057790980712194317211387 1586686471068291475817081)
      ·
        refine ⟨1190014853301218606862811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1586686471068291475817081 1190014853301218606862811)
        ·
          refine ⟨1785022279951827910294217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1190014853301218606862811 1785022279951827910294217)
          ·
            refine ⟨1338766709963870932720663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1785022279951827910294217 1338766709963870932720663)
            ·
              refine ⟨2008150064945806399080995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1338766709963870932720663 2008150064945806399080995)
              ·
                refine ⟨3012225097418709598621493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2008150064945806399080995 3012225097418709598621493)
                ·
                  refine ⟨282396102883004024870765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3012225097418709598621493 282396102883004024870765)
                  ·
                    rfl

theorem cell20_618710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 2, 1, 1, 5].length) (baseStart_618710 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_618710 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_618710 prefixEnd_618710 := by exact prefixLift 618710
  have htrace : WordTrace (prefixWord ++ tailWord_618710) baseStart_618710 baseEnd_618710 := by
    simpa [prefixWord, tailWord_618710, baseEnd_618710] using wordTrace_append hprefix tailTrace_618710
  have hstable : (prefixWord ++ tailWord_618710).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_618710).length < 2 ^ (prefixWord ++ tailWord_618710).sum := by decide
  have hdescent : baseEnd_618710 < baseStart_618710 := by decide
  rcases family_descends (prefixWord ++ tailWord_618710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_618717 : List Nat := [1, 4, 3, 2, 1, 2, 2, 1, 4]
def baseStart_618717 : Nat := 118140960795 + 618717 * 2 ^ 59
def prefixEnd_618717 : Nat := 4983230072969 + 3 ^ 40 * 618717 * 2
def baseEnd_618717 : Nat := 282399297873743111637403

theorem tailTrace_618717 : CollatzResearch.WordTrace tailWord_618717 prefixEnd_618717 282399297873743111637403 := by
  unfold tailWord_618717
  simp only [CollatzResearch.WordTrace]
  refine ⟨22566462899501452296014405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15044308599667634864009603 22566462899501452296014405)
  ·
    refine ⟨4231211793656522305502701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 22566462899501452296014405 4231211793656522305502701)
    ·
      refine ⟨1586704422621195864563513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4231211793656522305502701 1586704422621195864563513)
      ·
        refine ⟨1190028316965896898422635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1586704422621195864563513 1190028316965896898422635)
        ·
          refine ⟨1785042475448845347633953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1190028316965896898422635 1785042475448845347633953)
          ·
            refine ⟨1338781856586634010725465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1785042475448845347633953 1338781856586634010725465)
            ·
              refine ⟨1004086392439975508044099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1338781856586634010725465 1004086392439975508044099)
              ·
                refine ⟨1506129588659963262066149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1004086392439975508044099 1506129588659963262066149)
                ·
                  refine ⟨282399297873743111637403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1506129588659963262066149 282399297873743111637403)
                  ·
                    rfl

theorem cell20_618717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 2, 2, 1, 4].length) (baseStart_618717 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_618717 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_618717 prefixEnd_618717 := by exact prefixLift 618717
  have htrace : WordTrace (prefixWord ++ tailWord_618717) baseStart_618717 baseEnd_618717 := by
    simpa [prefixWord, tailWord_618717, baseEnd_618717] using wordTrace_append hprefix tailTrace_618717
  have hstable : (prefixWord ++ tailWord_618717).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_618717).length < 2 ^ (prefixWord ++ tailWord_618717).sum := by decide
  have hdescent : baseEnd_618717 < baseStart_618717 := by decide
  rcases family_descends (prefixWord ++ tailWord_618717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_618731 : List Nat := [1, 1, 1, 1, 2, 5, 5, 1, 3]
def baseStart_618731 : Nat := 118140960795 + 618731 * 2 ^ 59
def prefixEnd_618731 : Nat := 4983230072969 + 3 ^ 40 * 618731 * 2
def baseEnd_618731 : Nat := 282405687855221285170679

theorem tailTrace_618731 : CollatzResearch.WordTrace tailWord_618731 prefixEnd_618731 282405687855221285170679 := by
  unfold tailWord_618731
  simp only [CollatzResearch.WordTrace]
  refine ⟨22566973521450732687024047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15044649014300488458016031 22566973521450732687024047)
  ·
    refine ⟨33850460282176099030536071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22566973521450732687024047 33850460282176099030536071)
    ·
      refine ⟨50775690423264148545804107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33850460282176099030536071 50775690423264148545804107)
      ·
        refine ⟨76163535634896222818706161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50775690423264148545804107 76163535634896222818706161)
        ·
          refine ⟨57122651726172167114029621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 76163535634896222818706161 57122651726172167114029621)
          ·
            refine ⟨5355248599328640666940277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 57122651726172167114029621 5355248599328640666940277)
            ·
              refine ⟨502054556187060062525651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5355248599328640666940277 502054556187060062525651)
              ·
                refine ⟨753081834280590093788477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 502054556187060062525651 753081834280590093788477)
                ·
                  refine ⟨282405687855221285170679, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 753081834280590093788477 282405687855221285170679)
                  ·
                    rfl

theorem cell20_618731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 5, 1, 3].length) (baseStart_618731 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_618731 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_618731 prefixEnd_618731 := by exact prefixLift 618731
  have htrace : WordTrace (prefixWord ++ tailWord_618731) baseStart_618731 baseEnd_618731 := by
    simpa [prefixWord, tailWord_618731, baseEnd_618731] using wordTrace_append hprefix tailTrace_618731
  have hstable : (prefixWord ++ tailWord_618731).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_618731).length < 2 ^ (prefixWord ++ tailWord_618731).sum := by decide
  have hdescent : baseEnd_618731 < baseStart_618731 := by decide
  rcases family_descends (prefixWord ++ tailWord_618731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_618738 : List Nat := [3, 2, 1, 3, 2, 1, 2, 2, 4]
def baseStart_618738 : Nat := 118140960795 + 618738 * 2 ^ 59
def prefixEnd_618738 : Nat := 4983230072969 + 3 ^ 40 * 618738 * 2
def baseEnd_618738 : Nat := 282408882845960371937317

theorem tailTrace_618738 : CollatzResearch.WordTrace tailWord_618738 prefixEnd_618738 282408882845960371937317 := by
  unfold tailWord_618738
  simp only [CollatzResearch.WordTrace]
  refine ⟨5641807208106343220632217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15044819221616915255019245 5641807208106343220632217)
  ·
    refine ⟨4231355406079757415474163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5641807208106343220632217 4231355406079757415474163)
    ·
      refine ⟨6347033109119636123211245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4231355406079757415474163 6347033109119636123211245)
      ·
        refine ⟨2380137415919863546204217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6347033109119636123211245 2380137415919863546204217)
        ·
          refine ⟨1785103061939897659653163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2380137415919863546204217 1785103061939897659653163)
          ·
            refine ⟨2677654592909846489479745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1785103061939897659653163 2677654592909846489479745)
            ·
              refine ⟨2008240944682384867109809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2677654592909846489479745 2008240944682384867109809)
              ·
                refine ⟨1506180708511788650332357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2008240944682384867109809 1506180708511788650332357)
                ·
                  refine ⟨282408882845960371937317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1506180708511788650332357 282408882845960371937317)
                  ·
                    rfl

theorem cell20_618738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 2, 2, 4].length) (baseStart_618738 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_618738 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_618738 prefixEnd_618738 := by exact prefixLift 618738
  have htrace : WordTrace (prefixWord ++ tailWord_618738) baseStart_618738 baseEnd_618738 := by
    simpa [prefixWord, tailWord_618738, baseEnd_618738] using wordTrace_append hprefix tailTrace_618738
  have hstable : (prefixWord ++ tailWord_618738).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_618738).length < 2 ^ (prefixWord ++ tailWord_618738).sum := by decide
  have hdescent : baseEnd_618738 < baseStart_618738 := by decide
  rcases family_descends (prefixWord ++ tailWord_618738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_618782 : List Nat := [4, 3, 2, 1, 1, 3, 2, 1, 3]
def baseStart_618782 : Nat := 118140960795 + 618782 * 2 ^ 59
def prefixEnd_618782 : Nat := 4983230072969 + 3 ^ 40 * 618782 * 2
def baseEnd_618782 : Nat := 282428965644891774470471

theorem tailTrace_618782 : CollatzResearch.WordTrace tailWord_618782 prefixEnd_618782 282428965644891774470471 := by
  unfold tailWord_618782
  simp only [CollatzResearch.WordTrace]
  refine ⟨2821104205533246049641325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15045889096177312264753733 2821104205533246049641325)
  ·
    refine ⟨1057914077074967268615497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2821104205533246049641325 1057914077074967268615497)
    ·
      refine ⟨793435557806225451461623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1057914077074967268615497 793435557806225451461623)
      ·
        refine ⟨1190153336709338177192435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 793435557806225451461623 1190153336709338177192435)
        ·
          refine ⟨1785230005064007265788653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1190153336709338177192435 1785230005064007265788653)
          ·
            refine ⟨669461251899002724670745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1785230005064007265788653 669461251899002724670745)
            ·
              refine ⟨502095938924252043503059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 669461251899002724670745 502095938924252043503059)
              ·
                refine ⟨753143908386378065254589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 502095938924252043503059 753143908386378065254589)
                ·
                  refine ⟨282428965644891774470471, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 753143908386378065254589 282428965644891774470471)
                  ·
                    rfl

theorem cell20_618782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 3, 2, 1, 3].length) (baseStart_618782 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_618782 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_618782 prefixEnd_618782 := by exact prefixLift 618782
  have htrace : WordTrace (prefixWord ++ tailWord_618782) baseStart_618782 baseEnd_618782 := by
    simpa [prefixWord, tailWord_618782, baseEnd_618782] using wordTrace_append hprefix tailTrace_618782
  have hstable : (prefixWord ++ tailWord_618782).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_618782).length < 2 ^ (prefixWord ++ tailWord_618782).sum := by decide
  have hdescent : baseEnd_618782 < baseStart_618782 := by decide
  rcases family_descends (prefixWord ++ tailWord_618782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_618783 : List Nat := [1, 1, 2, 4, 3, 2, 2, 5]
def baseStart_618783 : Nat := 118140960795 + 618783 * 2 ^ 59
def prefixEnd_618783 : Nat := 4983230072969 + 3 ^ 40 * 618783 * 2
def baseEnd_618783 : Nat := 94143140690713405145711

theorem tailTrace_618783 : CollatzResearch.WordTrace tailWord_618783 prefixEnd_618783 94143140690713405145711 := by
  unfold tailWord_618783
  simp only [CollatzResearch.WordTrace]
  refine ⟨22568870117262345567917003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15045913411508230378611335 22568870117262345567917003)
  ·
    refine ⟨33853305175893518351875505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22568870117262345567917003 33853305175893518351875505)
    ·
      refine ⟨25389978881920138763906629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33853305175893518351875505 25389978881920138763906629)
      ·
        refine ⟨4760621040360026018232493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 25389978881920138763906629 4760621040360026018232493)
        ·
          refine ⟨1785232890135009756837185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4760621040360026018232493 1785232890135009756837185)
          ·
            refine ⟨1338924667601257317627889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1785232890135009756837185 1338924667601257317627889)
            ·
              refine ⟨1004193500700942988220917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1338924667601257317627889 1004193500700942988220917)
              ·
                refine ⟨94143140690713405145711, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1004193500700942988220917 94143140690713405145711)
                ·
                  rfl

theorem cell20_618783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 2, 2, 5].length) (baseStart_618783 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_618783 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_618783 prefixEnd_618783 := by exact prefixLift 618783
  have htrace : WordTrace (prefixWord ++ tailWord_618783) baseStart_618783 baseEnd_618783 := by
    simpa [prefixWord, tailWord_618783, baseEnd_618783] using wordTrace_append hprefix tailTrace_618783
  have hstable : (prefixWord ++ tailWord_618783).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_618783).length < 2 ^ (prefixWord ++ tailWord_618783).sum := by decide
  have hdescent : baseEnd_618783 < baseStart_618783 := by decide
  rcases family_descends (prefixWord ++ tailWord_618783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_618786 : List Nat := [3, 3, 1, 1, 3, 1, 4, 1, 3]
def baseStart_618786 : Nat := 118140960795 + 618786 * 2 ^ 59
def prefixEnd_618786 : Nat := 4983230072969 + 3 ^ 40 * 618786 * 2
def baseEnd_618786 : Nat := 282430791353885538337121

theorem tailTrace_618786 : CollatzResearch.WordTrace tailWord_618786 prefixEnd_618786 282430791353885538337121 := by
  unfold tailWord_618786
  simp only [CollatzResearch.WordTrace]
  refine ⟨5642244884062869270069053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15045986357500984720184141 5642244884062869270069053)
  ·
    refine ⟨2115841831523575976275895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5642244884062869270069053 2115841831523575976275895)
    ·
      refine ⟨3173762747285363964413843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2115841831523575976275895 3173762747285363964413843)
      ·
        refine ⟨4760644120928045946620765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3173762747285363964413843 4760644120928045946620765)
        ·
          refine ⟨1785241545348017229982787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4760644120928045946620765 1785241545348017229982787)
          ·
            refine ⟨2677862318022025844974181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1785241545348017229982787 2677862318022025844974181)
            ·
              refine ⟨502099184629129845932659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2677862318022025844974181 502099184629129845932659)
              ·
                refine ⟨753148776943694768898989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 502099184629129845932659 753148776943694768898989)
                ·
                  refine ⟨282430791353885538337121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 753148776943694768898989 282430791353885538337121)
                  ·
                    rfl

theorem cell20_618786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 4, 1, 3].length) (baseStart_618786 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_618786 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_618786 prefixEnd_618786 := by exact prefixLift 618786
  have htrace : WordTrace (prefixWord ++ tailWord_618786) baseStart_618786 baseEnd_618786 := by
    simpa [prefixWord, tailWord_618786, baseEnd_618786] using wordTrace_append hprefix tailTrace_618786
  have hstable : (prefixWord ++ tailWord_618786).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_618786).length < 2 ^ (prefixWord ++ tailWord_618786).sum := by decide
  have hdescent : baseEnd_618786 < baseStart_618786 := by decide
  rcases family_descends (prefixWord ++ tailWord_618786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_618849 : List Nat := [1, 2, 3, 1, 1, 1, 1, 1, 9]
def baseStart_618849 : Nat := 118140960795 + 618849 * 2 ^ 59
def prefixEnd_618849 : Nat := 4983230072969 + 3 ^ 40 * 618849 * 2
def baseEnd_618849 : Nat := 282459546270537319236863

theorem tailTrace_618849 : CollatzResearch.WordTrace tailWord_618849 prefixEnd_618849 282459546270537319236863 := by
  unfold tailWord_618849
  simp only [CollatzResearch.WordTrace]
  refine ⟨22571277335023238839819601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15047518223348825893213067 22571277335023238839819601)
  ·
    refine ⟨16928458001267429129864701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22571277335023238839819601 16928458001267429129864701)
    ·
      refine ⟨6348171750475285923699263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16928458001267429129864701 6348171750475285923699263)
      ·
        refine ⟨9522257625712928885548895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6348171750475285923699263 9522257625712928885548895)
        ·
          refine ⟨14283386438569393328323343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9522257625712928885548895 14283386438569393328323343)
          ·
            refine ⟨21425079657854089992485015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14283386438569393328323343 21425079657854089992485015)
            ·
              refine ⟨32137619486781134988727523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21425079657854089992485015 32137619486781134988727523)
              ·
                refine ⟨48206429230171702483091285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32137619486781134988727523 48206429230171702483091285)
                ·
                  refine ⟨282459546270537319236863, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 48206429230171702483091285 282459546270537319236863)
                  ·
                    rfl

theorem cell20_618849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 1, 9].length) (baseStart_618849 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_618849 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_618849 prefixEnd_618849 := by exact prefixLift 618849
  have htrace : WordTrace (prefixWord ++ tailWord_618849) baseStart_618849 baseEnd_618849 := by
    simpa [prefixWord, tailWord_618849, baseEnd_618849] using wordTrace_append hprefix tailTrace_618849
  have hstable : (prefixWord ++ tailWord_618849).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_618849).length < 2 ^ (prefixWord ++ tailWord_618849).sum := by decide
  have hdescent : baseEnd_618849 < baseStart_618849 := by decide
  rcases family_descends (prefixWord ++ tailWord_618849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_618869 : List Nat := [1, 3, 4, 1, 2, 1, 1, 5, 2]
def baseStart_618869 : Nat := 118140960795 + 618869 * 2 ^ 59
def prefixEnd_618869 : Nat := 4983230072969 + 3 ^ 40 * 618869 * 2
def baseEnd_618869 : Nat := 282468674815506138570115

theorem tailTrace_618869 : CollatzResearch.WordTrace tailWord_618869 prefixEnd_618869 282468674815506138570115 := by
  unfold tailWord_618869
  simp only [CollatzResearch.WordTrace]
  refine ⟨22572006794950782255547661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15048004529967188170365107 22572006794950782255547661)
  ·
    refine ⟨8464502548106543345830373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22572006794950782255547661 8464502548106543345830373)
    ·
      refine ⟨1587094227769976877343195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8464502548106543345830373 1587094227769976877343195)
      ·
        refine ⟨2380641341654965316014793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1587094227769976877343195 2380641341654965316014793)
        ·
          refine ⟨1785481006241223987011095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2380641341654965316014793 1785481006241223987011095)
          ·
            refine ⟨2678221509361835980516643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1785481006241223987011095 2678221509361835980516643)
            ·
              refine ⟨4017332264042753970774965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2678221509361835980516643 4017332264042753970774965)
              ·
                refine ⟨376624899754008184760153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4017332264042753970774965 376624899754008184760153)
                ·
                  refine ⟨282468674815506138570115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 376624899754008184760153 282468674815506138570115)
                  ·
                    rfl

theorem cell20_618869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 1, 5, 2].length) (baseStart_618869 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_618869 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_618869 prefixEnd_618869 := by exact prefixLift 618869
  have htrace : WordTrace (prefixWord ++ tailWord_618869) baseStart_618869 baseEnd_618869 := by
    simpa [prefixWord, tailWord_618869, baseEnd_618869] using wordTrace_append hprefix tailTrace_618869
  have hstable : (prefixWord ++ tailWord_618869).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_618869).length < 2 ^ (prefixWord ++ tailWord_618869).sum := by decide
  have hdescent : baseEnd_618869 < baseStart_618869 := by decide
  rcases family_descends (prefixWord ++ tailWord_618869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_618911 : List Nat := [1, 1, 2, 5, 1, 1, 1, 4, 4]
def baseStart_618911 : Nat := 118140960795 + 618911 * 2 ^ 59
def prefixEnd_618911 : Nat := 4983230072969 + 3 ^ 40 * 618911 * 2
def baseEnd_618911 : Nat := 282487844759940659169943

theorem tailTrace_618911 : CollatzResearch.WordTrace tailWord_618911 prefixEnd_618911 282487844759940659169943 := by
  unfold tailWord_618911
  simp only [CollatzResearch.WordTrace]
  refine ⟨22573538660798623428576587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15049025773865748952384391 22573538660798623428576587)
  ·
    refine ⟨33860307991197935142864881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22573538660798623428576587 33860307991197935142864881)
    ·
      refine ⟨25395230993398451357148661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33860307991197935142864881 25395230993398451357148661)
      ·
        refine ⟨2380802905631104814732687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 25395230993398451357148661 2380802905631104814732687)
        ·
          refine ⟨3571204358446657222099031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2380802905631104814732687 3571204358446657222099031)
          ·
            refine ⟨5356806537669985833148547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3571204358446657222099031 5356806537669985833148547)
            ·
              refine ⟨8035209806504978749722821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5356806537669985833148547 8035209806504978749722821)
              ·
                refine ⟨1506601838719683515573029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8035209806504978749722821 1506601838719683515573029)
                ·
                  refine ⟨282487844759940659169943, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1506601838719683515573029 282487844759940659169943)
                  ·
                    rfl

theorem cell20_618911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 1, 4, 4].length) (baseStart_618911 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_618911 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_618911 prefixEnd_618911 := by exact prefixLift 618911
  have htrace : WordTrace (prefixWord ++ tailWord_618911) baseStart_618911 baseEnd_618911 := by
    simpa [prefixWord, tailWord_618911, baseEnd_618911] using wordTrace_append hprefix tailTrace_618911
  have hstable : (prefixWord ++ tailWord_618911).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_618911).length < 2 ^ (prefixWord ++ tailWord_618911).sum := by decide
  have hdescent : baseEnd_618911 < baseStart_618911 := by decide
  rcases family_descends (prefixWord ++ tailWord_618911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_618942 : List Nat := [4, 2, 1, 1, 1, 1, 4, 1, 5]
def baseStart_618942 : Nat := 118140960795 + 618942 * 2 ^ 59
def prefixEnd_618942 : Nat := 4983230072969 + 3 ^ 40 * 618942 * 2
def baseEnd_618942 : Nat := 282501994004642329136483

theorem tailTrace_618942 : CollatzResearch.WordTrace tailWord_618942 prefixEnd_618942 282501994004642329136483 := by
  unfold tailWord_618942
  simp only [CollatzResearch.WordTrace]
  refine ⟨2821833665460789465369385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15049779549124210481970053 2821833665460789465369385)
  ·
    refine ⟨2116375249095592099027039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2821833665460789465369385 2116375249095592099027039)
    ·
      refine ⟨3174562873643388148540559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2116375249095592099027039 3174562873643388148540559)
      ·
        refine ⟨4761844310465082222810839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3174562873643388148540559 4761844310465082222810839)
        ·
          refine ⟨7142766465697623334216259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4761844310465082222810839 7142766465697623334216259)
          ·
            refine ⟨10714149698546435001324389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7142766465697623334216259 10714149698546435001324389)
            ·
              refine ⟨2008903068477456562748323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10714149698546435001324389 2008903068477456562748323)
              ·
                refine ⟨3013354602716184844122485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2008903068477456562748323 3013354602716184844122485)
                ·
                  refine ⟨282501994004642329136483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3013354602716184844122485 282501994004642329136483)
                  ·
                    rfl

theorem cell20_618942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 4, 1, 5].length) (baseStart_618942 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_618942 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_618942 prefixEnd_618942 := by exact prefixLift 618942
  have htrace : WordTrace (prefixWord ++ tailWord_618942) baseStart_618942 baseEnd_618942 := by
    simpa [prefixWord, tailWord_618942, baseEnd_618942] using wordTrace_append hprefix tailTrace_618942
  have hstable : (prefixWord ++ tailWord_618942).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_618942).length < 2 ^ (prefixWord ++ tailWord_618942).sum := by decide
  have hdescent : baseEnd_618942 < baseStart_618942 := by decide
  rcases family_descends (prefixWord ++ tailWord_618942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_618966 : List Nat := [5, 2, 1, 1, 1, 1, 2, 1, 6]
def baseStart_618966 : Nat := 118140960795 + 618966 * 2 ^ 59
def prefixEnd_618966 : Nat := 4983230072969 + 3 ^ 40 * 618966 * 2
def baseEnd_618966 : Nat := 282512948258604912336385

theorem tailTrace_618966 : CollatzResearch.WordTrace tailWord_618966 prefixEnd_618966 282512948258604912336385 := by
  unfold tailWord_618966
  simp only [CollatzResearch.WordTrace]
  refine ⟨1410971542224960488864297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 15050363117066245214552501 1410971542224960488864297)
  ·
    refine ⟨1058228656668720366648223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1410971542224960488864297 1058228656668720366648223)
    ·
      refine ⟨1587342985003080549972335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1058228656668720366648223 1587342985003080549972335)
      ·
        refine ⟨2381014477504620824958503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1587342985003080549972335 2381014477504620824958503)
        ·
          refine ⟨3571521716256931237437755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2381014477504620824958503 3571521716256931237437755)
          ·
            refine ⟨5357282574385396856156633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3571521716256931237437755 5357282574385396856156633)
            ·
              refine ⟨4017961930789047642117475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5357282574385396856156633 4017961930789047642117475)
              ·
                refine ⟨6026942896183571463176213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4017961930789047642117475 6026942896183571463176213)
                ·
                  refine ⟨282512948258604912336385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6026942896183571463176213 282512948258604912336385)
                  ·
                    rfl

theorem cell20_618966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 2, 1, 6].length) (baseStart_618966 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_618966 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_618966 prefixEnd_618966 := by exact prefixLift 618966
  have htrace : WordTrace (prefixWord ++ tailWord_618966) baseStart_618966 baseEnd_618966 := by
    simpa [prefixWord, tailWord_618966, baseEnd_618966] using wordTrace_append hprefix tailTrace_618966
  have hstable : (prefixWord ++ tailWord_618966).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_618966).length < 2 ^ (prefixWord ++ tailWord_618966).sum := by decide
  have hdescent : baseEnd_618966 < baseStart_618966 := by decide
  rcases family_descends (prefixWord ++ tailWord_618966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_618994 : List Nat := [3, 2, 1, 4, 10]
def baseStart_618994 : Nat := 118140960795 + 618994 * 2 ^ 59
def prefixEnd_618994 : Nat := 4983230072969 + 3 ^ 40 * 618994 * 2
def baseEnd_618994 : Nat := 3487971953352608140777

theorem tailTrace_618994 : CollatzResearch.WordTrace tailWord_618994 prefixEnd_618994 3487971953352608140777 := by
  unfold tailWord_618994
  simp only [CollatzResearch.WordTrace]
  refine ⟨5644141479874482150962009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15051043946331952402565357 5644141479874482150962009)
  ·
    refine ⟨4233106109905861613221507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5644141479874482150962009 4233106109905861613221507)
    ·
      refine ⟨6349659164858792419832261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4233106109905861613221507 6349659164858792419832261)
      ·
        refine ⟨1190561093411023578718549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6349659164858792419832261 1190561093411023578718549)
        ·
          refine ⟨3487971953352608140777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 10 1190561093411023578718549 3487971953352608140777)
          ·
            rfl

theorem cell20_618994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 10].length) (baseStart_618994 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_618994 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_618994 prefixEnd_618994 := by exact prefixLift 618994
  have htrace : WordTrace (prefixWord ++ tailWord_618994) baseStart_618994 baseEnd_618994 := by
    simpa [prefixWord, tailWord_618994, baseEnd_618994] using wordTrace_append hprefix tailTrace_618994
  have hstable : (prefixWord ++ tailWord_618994).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_618994).length < 2 ^ (prefixWord ++ tailWord_618994).sum := by decide
  have hdescent : baseEnd_618994 < baseStart_618994 := by decide
  rcases family_descends (prefixWord ++ tailWord_618994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_619001 : List Nat := [1, 2, 1, 3, 1, 2, 2, 3, 5]
def baseStart_619001 : Nat := 118140960795 + 619001 * 2 ^ 59
def prefixEnd_619001 : Nat := 4983230072969 + 3 ^ 40 * 619001 * 2
def baseEnd_619001 : Nat := 282528923212300346169575

theorem tailTrace_619001 : CollatzResearch.WordTrace tailWord_619001 prefixEnd_619001 282528923212300346169575 := by
  unfold tailWord_619001
  simp only [CollatzResearch.WordTrace]
  refine ⟨22576821230472568799352857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15051214153648379199568571 22576821230472568799352857)
  ·
    refine ⟨16932615922854426599514643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22576821230472568799352857 16932615922854426599514643)
    ·
      refine ⟨25398923884281639899271965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16932615922854426599514643 25398923884281639899271965)
      ·
        refine ⟨9524596456605614962226987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25398923884281639899271965 9524596456605614962226987)
        ·
          refine ⟨14286894684908422443340481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9524596456605614962226987 14286894684908422443340481)
          ·
            refine ⟨10715171013681316832505361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14286894684908422443340481 10715171013681316832505361)
            ·
              refine ⟨8036378260260987624379021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10715171013681316832505361 8036378260260987624379021)
              ·
                refine ⟨3013641847597870359142133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8036378260260987624379021 3013641847597870359142133)
                ·
                  refine ⟨282528923212300346169575, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3013641847597870359142133 282528923212300346169575)
                  ·
                    rfl

theorem cell20_619001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 2, 3, 5].length) (baseStart_619001 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_619001 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_619001 prefixEnd_619001 := by exact prefixLift 619001
  have htrace : WordTrace (prefixWord ++ tailWord_619001) baseStart_619001 baseEnd_619001 := by
    simpa [prefixWord, tailWord_619001, baseEnd_619001] using wordTrace_append hprefix tailTrace_619001
  have hstable : (prefixWord ++ tailWord_619001).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_619001).length < 2 ^ (prefixWord ++ tailWord_619001).sum := by decide
  have hdescent : baseEnd_619001 < baseStart_619001 := by decide
  rcases family_descends (prefixWord ++ tailWord_619001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_619008 : List Nat := [2, 1, 1, 2, 1, 1, 1, 1, 10]
def baseStart_619008 : Nat := 118140960795 + 619008 * 2 ^ 59
def prefixEnd_619008 : Nat := 4983230072969 + 3 ^ 40 * 619008 * 2
def baseEnd_619008 : Nat := 282532118203039432936213

theorem tailTrace_619008 : CollatzResearch.WordTrace tailWord_619008 prefixEnd_619008 282532118203039432936213 := by
  unfold tailWord_619008
  simp only [CollatzResearch.WordTrace]
  refine ⟨11288538270723604497428839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15051384360964805996571785 11288538270723604497428839)
  ·
    refine ⟨16932807406085406746143259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11288538270723604497428839 16932807406085406746143259)
    ·
      refine ⟨25399211109128110119214889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16932807406085406746143259 25399211109128110119214889)
      ·
        refine ⟨19049408331846082589411167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25399211109128110119214889 19049408331846082589411167)
        ·
          refine ⟨28574112497769123884116751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19049408331846082589411167 28574112497769123884116751)
          ·
            refine ⟨42861168746653685826175127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28574112497769123884116751 42861168746653685826175127)
            ·
              refine ⟨64291753119980528739262691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42861168746653685826175127 64291753119980528739262691)
              ·
                refine ⟨96437629679970793108894037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 64291753119980528739262691 96437629679970793108894037)
                ·
                  refine ⟨282532118203039432936213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 96437629679970793108894037 282532118203039432936213)
                  ·
                    rfl

theorem cell20_619008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 1, 10].length) (baseStart_619008 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_619008 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_619008 prefixEnd_619008 := by exact prefixLift 619008
  have htrace : WordTrace (prefixWord ++ tailWord_619008) baseStart_619008 baseEnd_619008 := by
    simpa [prefixWord, tailWord_619008, baseEnd_619008] using wordTrace_append hprefix tailTrace_619008
  have hstable : (prefixWord ++ tailWord_619008).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_619008).length < 2 ^ (prefixWord ++ tailWord_619008).sum := by decide
  have hdescent : baseEnd_619008 < baseStart_619008 := by decide
  rcases family_descends (prefixWord ++ tailWord_619008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_619018 : List Nat := [3, 1, 2, 2, 2, 1, 1, 5, 3]
def baseStart_619018 : Nat := 118140960795 + 619018 * 2 ^ 59
def prefixEnd_619018 : Nat := 4983230072969 + 3 ^ 40 * 619018 * 2
def baseEnd_619018 : Nat := 282536682475523842602839

theorem tailTrace_619018 : CollatzResearch.WordTrace tailWord_619018 prefixEnd_619018 282536682475523842602839 := by
  unfold tailWord_619018
  simp only [CollatzResearch.WordTrace]
  refine ⟨5644360317852745175680427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15051627514273987135147805 5644360317852745175680427)
  ·
    refine ⟨8466540476779117763520641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5644360317852745175680427 8466540476779117763520641)
    ·
      refine ⟨6349905357584338322640481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8466540476779117763520641 6349905357584338322640481)
      ·
        refine ⟨4762429018188253741980361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6349905357584338322640481 4762429018188253741980361)
        ·
          refine ⟨3571821763641190306485271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4762429018188253741980361 3571821763641190306485271)
          ·
            refine ⟨5357732645461785459727907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3571821763641190306485271 5357732645461785459727907)
            ·
              refine ⟨8036598968192678189591861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5357732645461785459727907 8036598968192678189591861)
              ·
                refine ⟨753431153268063580274237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8036598968192678189591861 753431153268063580274237)
                ·
                  refine ⟨282536682475523842602839, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 753431153268063580274237 282536682475523842602839)
                  ·
                    rfl

theorem cell20_619018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 1, 5, 3].length) (baseStart_619018 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_619018 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_619018 prefixEnd_619018 := by exact prefixLift 619018
  have htrace : WordTrace (prefixWord ++ tailWord_619018) baseStart_619018 baseEnd_619018 := by
    simpa [prefixWord, tailWord_619018, baseEnd_619018] using wordTrace_append hprefix tailTrace_619018
  have hstable : (prefixWord ++ tailWord_619018).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_619018).length < 2 ^ (prefixWord ++ tailWord_619018).sum := by decide
  have hdescent : baseEnd_619018 < baseStart_619018 := by decide
  rcases family_descends (prefixWord ++ tailWord_619018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_619021 : List Nat := [1, 7, 1, 1, 1, 1, 1, 1, 6]
def baseStart_619021 : Nat := 118140960795 + 619021 * 2 ^ 59
def prefixEnd_619021 : Nat := 4983230072969 + 3 ^ 40 * 619021 * 2
def baseEnd_619021 : Nat := 282538051757269165502827

theorem tailTrace_619021 : CollatzResearch.WordTrace tailWord_619021 prefixEnd_619021 282538051757269165502827 := by
  unfold tailWord_619021
  simp only [CollatzResearch.WordTrace]
  refine ⟨22577550690400112215080917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15051700460266741476720611 22577550690400112215080917)
  ·
    refine ⟨529161344306252630040959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 22577550690400112215080917 529161344306252630040959)
    ·
      refine ⟨793742016459378945061439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 529161344306252630040959 793742016459378945061439)
      ·
        refine ⟨1190613024689068417592159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 793742016459378945061439 1190613024689068417592159)
        ·
          refine ⟨1785919537033602626388239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1190613024689068417592159 1785919537033602626388239)
          ·
            refine ⟨2678879305550403939582359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1785919537033602626388239 2678879305550403939582359)
            ·
              refine ⟨4018318958325605909373539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2678879305550403939582359 4018318958325605909373539)
              ·
                refine ⟨6027478437488408864060309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4018318958325605909373539 6027478437488408864060309)
                ·
                  refine ⟨282538051757269165502827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6027478437488408864060309 282538051757269165502827)
                  ·
                    rfl

theorem cell20_619021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 1, 1, 6].length) (baseStart_619021 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_619021 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_619021 prefixEnd_619021 := by exact prefixLift 619021
  have htrace : WordTrace (prefixWord ++ tailWord_619021) baseStart_619021 baseEnd_619021 := by
    simpa [prefixWord, tailWord_619021, baseEnd_619021] using wordTrace_append hprefix tailTrace_619021
  have hstable : (prefixWord ++ tailWord_619021).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_619021).length < 2 ^ (prefixWord ++ tailWord_619021).sum := by decide
  have hdescent : baseEnd_619021 < baseStart_619021 := by decide
  rcases family_descends (prefixWord ++ tailWord_619021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_619039 : List Nat := [1, 1, 2, 4, 1, 1, 1, 4, 5]
def baseStart_619039 : Nat := 118140960795 + 619039 * 2 ^ 59
def prefixEnd_619039 : Nat := 4983230072969 + 3 ^ 40 * 619039 * 2
def baseEnd_619039 : Nat := 282546267447741102902753

theorem tailTrace_619039 : CollatzResearch.WordTrace tailWord_619039 prefixEnd_619039 282546267447741102902753 := by
  unfold tailWord_619039
  simp only [CollatzResearch.WordTrace]
  refine ⟨22578207204334901289236171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15052138136223267526157447 22578207204334901289236171)
  ·
    refine ⟨33867310806502351933854257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22578207204334901289236171 33867310806502351933854257)
    ·
      refine ⟨25400483104876763950390693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33867310806502351933854257 25400483104876763950390693)
      ·
        refine ⟨4762590582164393240698255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 25400483104876763950390693 4762590582164393240698255)
        ·
          refine ⟨7143885873246589861047383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4762590582164393240698255 7143885873246589861047383)
          ·
            refine ⟨10715828809869884791571075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7143885873246589861047383 10715828809869884791571075)
            ·
              refine ⟨16073743214804827187356613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10715828809869884791571075 16073743214804827187356613)
              ·
                refine ⟨3013826852775905097629365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16073743214804827187356613 3013826852775905097629365)
                ·
                  refine ⟨282546267447741102902753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3013826852775905097629365 282546267447741102902753)
                  ·
                    rfl

theorem cell20_619039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 4, 5].length) (baseStart_619039 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_619039 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_619039 prefixEnd_619039 := by exact prefixLift 619039
  have htrace : WordTrace (prefixWord ++ tailWord_619039) baseStart_619039 baseEnd_619039 := by
    simpa [prefixWord, tailWord_619039, baseEnd_619039] using wordTrace_append hprefix tailTrace_619039
  have hstable : (prefixWord ++ tailWord_619039).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_619039).length < 2 ^ (prefixWord ++ tailWord_619039).sum := by decide
  have hdescent : baseEnd_619039 < baseStart_619039 := by decide
  rcases family_descends (prefixWord ++ tailWord_619039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_619056 : List Nat := [2, 1, 1, 1, 2, 3, 5, 2, 3]
def baseStart_619056 : Nat := 118140960795 + 619056 * 2 ^ 59
def prefixEnd_619056 : Nat := 4983230072969 + 3 ^ 40 * 619056 * 2
def baseEnd_619056 : Nat := 282554026710964599336017

theorem tailTrace_619056 : CollatzResearch.WordTrace tailWord_619056 prefixEnd_619056 282554026710964599336017 := by
  unfold tailWord_619056
  simp only [CollatzResearch.WordTrace]
  refine ⟨11289413622636656596302511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15052551496848875461736681 11289413622636656596302511)
  ·
    refine ⟨16934120433954984894453767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11289413622636656596302511 16934120433954984894453767)
    ·
      refine ⟨25401180650932477341680651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16934120433954984894453767 25401180650932477341680651)
      ·
        refine ⟨38101770976398716012520977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25401180650932477341680651 38101770976398716012520977)
        ·
          refine ⟨28576328232299037009390733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38101770976398716012520977 28576328232299037009390733)
          ·
            refine ⟨10716123087112138878521525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28576328232299037009390733 10716123087112138878521525)
            ·
              refine ⟨1004636539416763019861393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 10716123087112138878521525 1004636539416763019861393)
              ·
                refine ⟨753477404562572264896045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1004636539416763019861393 753477404562572264896045)
                ·
                  refine ⟨282554026710964599336017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 753477404562572264896045 282554026710964599336017)
                  ·
                    rfl

theorem cell20_619056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 5, 2, 3].length) (baseStart_619056 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_619056 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_619056 prefixEnd_619056 := by exact prefixLift 619056
  have htrace : WordTrace (prefixWord ++ tailWord_619056) baseStart_619056 baseEnd_619056 := by
    simpa [prefixWord, tailWord_619056, baseEnd_619056] using wordTrace_append hprefix tailTrace_619056
  have hstable : (prefixWord ++ tailWord_619056).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_619056).length < 2 ^ (prefixWord ++ tailWord_619056).sum := by decide
  have hdescent : baseEnd_619056 < baseStart_619056 := by decide
  rcases family_descends (prefixWord ++ tailWord_619056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_619063 : List Nat := [1, 1, 3, 1, 2, 3, 4, 1, 4]
def baseStart_619063 : Nat := 118140960795 + 619063 * 2 ^ 59
def prefixEnd_619063 : Nat := 4983230072969 + 3 ^ 40 * 619063 * 2
def baseEnd_619063 : Nat := 282557221701703686102655

theorem tailTrace_619063 : CollatzResearch.WordTrace tailWord_619063 prefixEnd_619063 282557221701703686102655 := by
  unfold tailWord_619063
  simp only [CollatzResearch.WordTrace]
  refine ⟨22579082556247953388109843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15052721704165302258739895 22579082556247953388109843)
  ·
    refine ⟨33868623834371930082164765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22579082556247953388109843 33868623834371930082164765)
    ·
      refine ⟨12700733937889473780811787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33868623834371930082164765 12700733937889473780811787)
      ·
        refine ⟨19051100906834210671217681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12700733937889473780811787 19051100906834210671217681)
        ·
          refine ⟨14288325680125658003413261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19051100906834210671217681 14288325680125658003413261)
          ·
            refine ⟨5358122130047121751279973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14288325680125658003413261 5358122130047121751279973)
            ·
              refine ⟨1004647899383835328364995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5358122130047121751279973 1004647899383835328364995)
              ·
                refine ⟨1506971849075752992547493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1004647899383835328364995 1506971849075752992547493)
                ·
                  refine ⟨282557221701703686102655, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1506971849075752992547493 282557221701703686102655)
                  ·
                    rfl

theorem cell20_619063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 4, 1, 4].length) (baseStart_619063 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_619063 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_619063 prefixEnd_619063 := by exact prefixLift 619063
  have htrace : WordTrace (prefixWord ++ tailWord_619063) baseStart_619063 baseEnd_619063 := by
    simpa [prefixWord, tailWord_619063, baseEnd_619063] using wordTrace_append hprefix tailTrace_619063
  have hstable : (prefixWord ++ tailWord_619063).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_619063).length < 2 ^ (prefixWord ++ tailWord_619063).sum := by decide
  have hdescent : baseEnd_619063 < baseStart_619063 := by decide
  rcases family_descends (prefixWord ++ tailWord_619063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_619118 : List Nat := [4, 1, 2, 2, 2, 1, 3, 1, 4]
def baseStart_619118 : Nat := 118140960795 + 619118 * 2 ^ 59
def prefixEnd_619118 : Nat := 4983230072969 + 3 ^ 40 * 619118 * 2
def baseEnd_619118 : Nat := 282582325200367939269097

theorem tailTrace_619118 : CollatzResearch.WordTrace tailWord_619118 prefixEnd_619118 282582325200367939269097 := by
  unfold tailWord_619118
  simp only [CollatzResearch.WordTrace]
  refine ⟨2822636071381087222670251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15054059047365798520908005 2822636071381087222670251)
  ·
    refine ⟨4233954107071630834005377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2822636071381087222670251 4233954107071630834005377)
    ·
      refine ⟨3175465580303723125504033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4233954107071630834005377 3175465580303723125504033)
      ·
        refine ⟨2381599185227792344128025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3175465580303723125504033 2381599185227792344128025)
        ·
          refine ⟨1786199388920844258096019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2381599185227792344128025 1786199388920844258096019)
          ·
            refine ⟨2679299083381266387144029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1786199388920844258096019 2679299083381266387144029)
            ·
              refine ⟨1004737156267974895179011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2679299083381266387144029 1004737156267974895179011)
              ·
                refine ⟨1507105734401962342768517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1004737156267974895179011 1507105734401962342768517)
                ·
                  refine ⟨282582325200367939269097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1507105734401962342768517 282582325200367939269097)
                  ·
                    rfl

theorem cell20_619118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 3, 1, 4].length) (baseStart_619118 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_619118 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_619118 prefixEnd_619118 := by exact prefixLift 619118
  have htrace : WordTrace (prefixWord ++ tailWord_619118) baseStart_619118 baseEnd_619118 := by
    simpa [prefixWord, tailWord_619118, baseEnd_619118] using wordTrace_append hprefix tailTrace_619118
  have hstable : (prefixWord ++ tailWord_619118).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_619118).length < 2 ^ (prefixWord ++ tailWord_619118).sum := by decide
  have hdescent : baseEnd_619118 < baseStart_619118 := by decide
  rcases family_descends (prefixWord ++ tailWord_619118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_619167 : List Nat := [1, 1, 2, 16]
def baseStart_619167 : Nat := 118140960795 + 619167 * 2 ^ 59
def prefixEnd_619167 : Nat := 4983230072969 + 3 ^ 40 * 619167 * 2
def baseEnd_619167 : Nat := 1162982263932269739241

theorem tailTrace_619167 : CollatzResearch.WordTrace tailWord_619167 prefixEnd_619167 1162982263932269739241 := by
  unfold tailWord_619167
  simp only [CollatzResearch.WordTrace]
  refine ⟨22582875747871179149895755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15055250498580786099930503 22582875747871179149895755)
  ·
    refine ⟨33874313621806768724843633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22582875747871179149895755 33874313621806768724843633)
    ·
      refine ⟨25405735216355076543632725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33874313621806768724843633 25405735216355076543632725)
      ·
        refine ⟨1162982263932269739241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 16 25405735216355076543632725 1162982263932269739241)
        ·
          rfl

theorem cell20_619167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 16].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 16].length) (baseStart_619167 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_619167 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_619167 prefixEnd_619167 := by exact prefixLift 619167
  have htrace : WordTrace (prefixWord ++ tailWord_619167) baseStart_619167 baseEnd_619167 := by
    simpa [prefixWord, tailWord_619167, baseEnd_619167] using wordTrace_append hprefix tailTrace_619167
  have hstable : (prefixWord ++ tailWord_619167).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_619167).length < 2 ^ (prefixWord ++ tailWord_619167).sum := by decide
  have hdescent : baseEnd_619167 < baseStart_619167 := by decide
  rcases family_descends (prefixWord ++ tailWord_619167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_619169 : List Nat := [1, 2, 3, 3, 4, 1, 2, 2, 2]
def baseStart_619169 : Nat := 118140960795 + 619169 * 2 ^ 59
def prefixEnd_619169 : Nat := 4983230072969 + 3 ^ 40 * 619169 * 2
def baseEnd_619169 : Nat := 282605602990038428568889

theorem tailTrace_619169 : CollatzResearch.WordTrace tailWord_619169 prefixEnd_619169 282605602990038428568889 := by
  unfold tailWord_619169
  simp only [CollatzResearch.WordTrace]
  refine ⟨22582948693863933491468561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15055299129242622327645707 22582948693863933491468561)
  ·
    refine ⟨16937211520397950118601421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22582948693863933491468561 16937211520397950118601421)
    ·
      refine ⟨6351454320149231294475533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16937211520397950118601421 6351454320149231294475533)
      ·
        refine ⟨2381795370055961735428325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6351454320149231294475533 2381795370055961735428325)
        ·
          refine ⟨446586631885492825392811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2381795370055961735428325 446586631885492825392811)
          ·
            refine ⟨669879947828239238089217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 446586631885492825392811 669879947828239238089217)
            ·
              refine ⟨502409960871179428566913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 669879947828239238089217 502409960871179428566913)
              ·
                refine ⟨376807470653384571425185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 502409960871179428566913 376807470653384571425185)
                ·
                  refine ⟨282605602990038428568889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 376807470653384571425185 282605602990038428568889)
                  ·
                    rfl

theorem cell20_619169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 4, 1, 2, 2, 2].length) (baseStart_619169 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_619169 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_619169 prefixEnd_619169 := by exact prefixLift 619169
  have htrace : WordTrace (prefixWord ++ tailWord_619169) baseStart_619169 baseEnd_619169 := by
    simpa [prefixWord, tailWord_619169, baseEnd_619169] using wordTrace_append hprefix tailTrace_619169
  have hstable : (prefixWord ++ tailWord_619169).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_619169).length < 2 ^ (prefixWord ++ tailWord_619169).sum := by decide
  have hdescent : baseEnd_619169 < baseStart_619169 := by decide
  rcases family_descends (prefixWord ++ tailWord_619169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_619221 : List Nat := [1, 3, 2, 5, 2, 1, 1, 2, 3]
def baseStart_619221 : Nat := 118140960795 + 619221 * 2 ^ 59
def prefixEnd_619221 : Nat := 4983230072969 + 3 ^ 40 * 619221 * 2
def baseEnd_619221 : Nat := 282629337206957358835343

theorem tailTrace_619221 : CollatzResearch.WordTrace tailWord_619221 prefixEnd_619221 282629337206957358835343 := by
  unfold tailWord_619221
  simp only [CollatzResearch.WordTrace]
  refine ⟨22584845289675546372361517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15056563526450364248241011 22584845289675546372361517)
  ·
    refine ⟨8469316983628329889635569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22584845289675546372361517 8469316983628329889635569)
    ·
      refine ⟨6351987737721247417226677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8469316983628329889635569 6351987737721247417226677)
      ·
        refine ⟨595498850411366945365001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 6351987737721247417226677 595498850411366945365001)
        ·
          refine ⟨446624137808525209023751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 595498850411366945365001 446624137808525209023751)
          ·
            refine ⟨669936206712787813535627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 446624137808525209023751 669936206712787813535627)
            ·
              refine ⟨1004904310069181720303441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 669936206712787813535627 1004904310069181720303441)
              ·
                refine ⟨753678232551886290227581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1004904310069181720303441 753678232551886290227581)
                ·
                  refine ⟨282629337206957358835343, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 753678232551886290227581 282629337206957358835343)
                  ·
                    rfl

theorem cell20_619221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 2, 1, 1, 2, 3].length) (baseStart_619221 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_619221 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_619221 prefixEnd_619221 := by exact prefixLift 619221
  have htrace : WordTrace (prefixWord ++ tailWord_619221) baseStart_619221 baseEnd_619221 := by
    simpa [prefixWord, tailWord_619221, baseEnd_619221] using wordTrace_append hprefix tailTrace_619221
  have hstable : (prefixWord ++ tailWord_619221).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_619221).length < 2 ^ (prefixWord ++ tailWord_619221).sum := by decide
  have hdescent : baseEnd_619221 < baseStart_619221 := by decide
  rcases family_descends (prefixWord ++ tailWord_619221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_619243 : List Nat := [1, 1, 1, 1, 2, 4, 1, 9]
def baseStart_619243 : Nat := 118140960795 + 619243 * 2 ^ 59
def prefixEnd_619243 : Nat := 4983230072969 + 3 ^ 40 * 619243 * 2
def baseEnd_619243 : Nat := 94213126202141020033973

theorem tailTrace_619243 : CollatzResearch.WordTrace tailWord_619243 prefixEnd_619243 94213126202141020033973 := by
  unfold tailWord_619243
  simp only [CollatzResearch.WordTrace]
  refine ⟨22585647695595844129662383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15057098463730562753108255 22585647695595844129662383)
  ·
    refine ⟨33878471543393766194493575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22585647695595844129662383 33878471543393766194493575)
    ·
      refine ⟨50817707315090649291740363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33878471543393766194493575 50817707315090649291740363)
      ·
        refine ⟨76226560972635973937610545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50817707315090649291740363 76226560972635973937610545)
        ·
          refine ⟨57169920729476980453207909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 76226560972635973937610545 57169920729476980453207909)
          ·
            refine ⟨10719360136776933834976483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 57169920729476980453207909 10719360136776933834976483)
            ·
              refine ⟨16079040205165400752464725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10719360136776933834976483 16079040205165400752464725)
              ·
                refine ⟨94213126202141020033973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 16079040205165400752464725 94213126202141020033973)
                ·
                  rfl

theorem cell20_619243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 9].length) (baseStart_619243 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_619243 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_619243 prefixEnd_619243 := by exact prefixLift 619243
  have htrace : WordTrace (prefixWord ++ tailWord_619243) baseStart_619243 baseEnd_619243 := by
    simpa [prefixWord, tailWord_619243, baseEnd_619243] using wordTrace_append hprefix tailTrace_619243
  have hstable : (prefixWord ++ tailWord_619243).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_619243).length < 2 ^ (prefixWord ++ tailWord_619243).sum := by decide
  have hdescent : baseEnd_619243 < baseStart_619243 := by decide
  rcases family_descends (prefixWord ++ tailWord_619243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_619252 : List Nat := [2, 6, 1, 1, 2, 2, 2, 4]
def baseStart_619252 : Nat := 118140960795 + 619252 * 2 ^ 59
def prefixEnd_619252 : Nat := 4983230072969 + 3 ^ 40 * 619252 * 2
def baseEnd_619252 : Nat := 94214495483886342933961

theorem tailTrace_619252 : CollatzResearch.WordTrace tailWord_619252 prefixEnd_619252 94214495483886342933961 := by
  unfold tailWord_619252
  simp only [CollatzResearch.WordTrace]
  refine ⟨11292987976281619333370005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15057317301708825777826673 11292987976281619333370005)
  ·
    refine ⟨529358811388200906251719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 11292987976281619333370005 529358811388200906251719)
    ·
      refine ⟨794038217082301359377579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 529358811388200906251719 794038217082301359377579)
      ·
        refine ⟨1191057325623452039066369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 794038217082301359377579 1191057325623452039066369)
        ·
          refine ⟨893292994217589029299777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1191057325623452039066369 893292994217589029299777)
          ·
            refine ⟨669969745663191771974833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 893292994217589029299777 669969745663191771974833)
            ·
              refine ⟨502477309247393828981125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 669969745663191771974833 502477309247393828981125)
              ·
                refine ⟨94214495483886342933961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 502477309247393828981125 94214495483886342933961)
                ·
                  rfl

theorem cell20_619252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 2, 2, 4].length) (baseStart_619252 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_619252 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_619252 prefixEnd_619252 := by exact prefixLift 619252
  have htrace : WordTrace (prefixWord ++ tailWord_619252) baseStart_619252 baseEnd_619252 := by
    simpa [prefixWord, tailWord_619252, baseEnd_619252] using wordTrace_append hprefix tailTrace_619252
  have hstable : (prefixWord ++ tailWord_619252).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_619252).length < 2 ^ (prefixWord ++ tailWord_619252).sum := by decide
  have hdescent : baseEnd_619252 < baseStart_619252 := by decide
  rcases family_descends (prefixWord ++ tailWord_619252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_619260 : List Nat := [2, 2, 2, 1, 3, 3, 1, 6]
def baseStart_619260 : Nat := 118140960795 + 619260 * 2 ^ 59
def prefixEnd_619260 : Nat := 4983230072969 + 3 ^ 40 * 619260 * 2
def baseEnd_619260 : Nat := 94215712623215518845061

theorem tailTrace_619260 : CollatzResearch.WordTrace tailWord_619260 prefixEnd_619260 94215712623215518845061 := by
  unfold tailWord_619260
  simp only [CollatzResearch.WordTrace]
  refine ⟨11293133868267128016515617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15057511824356170688687489 11293133868267128016515617)
  ·
    refine ⟨8469850401200346012386713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11293133868267128016515617 8469850401200346012386713)
    ·
      refine ⟨6352387800900259509290035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8469850401200346012386713 6352387800900259509290035)
      ·
        refine ⟨9528581701350389263935053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6352387800900259509290035 9528581701350389263935053)
        ·
          refine ⟨3573218138006395973975645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9528581701350389263935053 3573218138006395973975645)
          ·
            refine ⟨1339956801752398490240867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3573218138006395973975645 1339956801752398490240867)
            ·
              refine ⟨2009935202628597735361301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1339956801752398490240867 2009935202628597735361301)
              ·
                refine ⟨94215712623215518845061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2009935202628597735361301 94215712623215518845061)
                ·
                  rfl

theorem cell20_619260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 3, 1, 6].length) (baseStart_619260 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_619260 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_619260 prefixEnd_619260 := by exact prefixLift 619260
  have htrace : WordTrace (prefixWord ++ tailWord_619260) baseStart_619260 baseEnd_619260 := by
    simpa [prefixWord, tailWord_619260, baseEnd_619260] using wordTrace_append hprefix tailTrace_619260
  have hstable : (prefixWord ++ tailWord_619260).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_619260).length < 2 ^ (prefixWord ++ tailWord_619260).sum := by decide
  have hdescent : baseEnd_619260 < baseStart_619260 := by decide
  rcases family_descends (prefixWord ++ tailWord_619260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_619266 : List Nat := [3, 4, 1, 1, 1, 4, 1, 3, 2]
def baseStart_619266 : Nat := 118140960795 + 619266 * 2 ^ 59
def prefixEnd_619266 : Nat := 4983230072969 + 3 ^ 40 * 619266 * 2
def baseEnd_619266 : Nat := 282649876433137202335159

theorem tailTrace_619266 : CollatzResearch.WordTrace tailWord_619266 prefixEnd_619266 282649876433137202335159 := by
  unfold tailWord_619266
  simp only [CollatzResearch.WordTrace]
  refine ⟨5646621643628129764437413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15057657716341679371833101 5646621643628129764437413)
  ·
    refine ⟨1058741558180274330832015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5646621643628129764437413 1058741558180274330832015)
    ·
      refine ⟨1588112337270411496248023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1058741558180274330832015 1588112337270411496248023)
      ·
        refine ⟨2382168505905617244372035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1588112337270411496248023 2382168505905617244372035)
        ·
          refine ⟨3573252758858425866558053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2382168505905617244372035 3573252758858425866558053)
          ·
            refine ⟨669984892285954849979635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3573252758858425866558053 669984892285954849979635)
            ·
              refine ⟨1004977338428932274969453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 669984892285954849979635 1004977338428932274969453)
              ·
                refine ⟨376866501910849603113545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1004977338428932274969453 376866501910849603113545)
                ·
                  refine ⟨282649876433137202335159, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 376866501910849603113545 282649876433137202335159)
                  ·
                    rfl

theorem cell20_619266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 4, 1, 3, 2].length) (baseStart_619266 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_619266 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_619266 prefixEnd_619266 := by exact prefixLift 619266
  have htrace : WordTrace (prefixWord ++ tailWord_619266) baseStart_619266 baseEnd_619266 := by
    simpa [prefixWord, tailWord_619266, baseEnd_619266] using wordTrace_append hprefix tailTrace_619266
  have hstable : (prefixWord ++ tailWord_619266).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_619266).length < 2 ^ (prefixWord ++ tailWord_619266).sum := by decide
  have hdescent : baseEnd_619266 < baseStart_619266 := by decide
  rcases family_descends (prefixWord ++ tailWord_619266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_619281 : List Nat := [1, 2, 2, 1, 1, 3, 10]
def baseStart_619281 : Nat := 118140960795 + 619281 * 2 ^ 59
def prefixEnd_619281 : Nat := 4983230072969 + 3 ^ 40 * 619281 * 2
def baseEnd_619281 : Nat := 31406302537984868537233

theorem tailTrace_619281 : CollatzResearch.WordTrace tailWord_619281 prefixEnd_619281 31406302537984868537233 := by
  unfold tailWord_619281
  simp only [CollatzResearch.WordTrace]
  refine ⟨22587033669458176619545697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15058022446305451079697131 22587033669458176619545697)
  ·
    refine ⟨16940275252093632464659273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22587033669458176619545697 16940275252093632464659273)
    ·
      refine ⟨12705206439070224348494455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16940275252093632464659273 12705206439070224348494455)
      ·
        refine ⟨19057809658605336522741683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12705206439070224348494455 19057809658605336522741683)
        ·
          refine ⟨28586714487908004784112525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19057809658605336522741683 28586714487908004784112525)
          ·
            refine ⟨10720017932965501794042197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28586714487908004784112525 10720017932965501794042197)
            ·
              refine ⟨31406302537984868537233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 10720017932965501794042197 31406302537984868537233)
              ·
                rfl

theorem cell20_619281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 10].length) (baseStart_619281 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_619281 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_619281 prefixEnd_619281 := by exact prefixLift 619281
  have htrace : WordTrace (prefixWord ++ tailWord_619281) baseStart_619281 baseEnd_619281 := by
    simpa [prefixWord, tailWord_619281, baseEnd_619281] using wordTrace_append hprefix tailTrace_619281
  have hstable : (prefixWord ++ tailWord_619281).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_619281).length < 2 ^ (prefixWord ++ tailWord_619281).sum := by decide
  have hdescent : baseEnd_619281 < baseStart_619281 := by decide
  rcases family_descends (prefixWord ++ tailWord_619281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_619287 : List Nat := [1, 1, 3, 4, 4, 1, 1, 1, 4]
def baseStart_619287 : Nat := 118140960795 + 619287 * 2 ^ 59
def prefixEnd_619287 : Nat := 4983230072969 + 3 ^ 40 * 619287 * 2
def baseEnd_619287 : Nat := 282659461405354462635073

theorem tailTrace_619287 : CollatzResearch.WordTrace tailWord_619287 prefixEnd_619287 282659461405354462635073 := by
  unfold tailWord_619287
  simp only [CollatzResearch.WordTrace]
  refine ⟨22587252507436439644264115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15058168338290959762842743 22587252507436439644264115)
  ·
    refine ⟨33880878761154659466396173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22587252507436439644264115 33880878761154659466396173)
    ·
      refine ⟨12705329535432997299898565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33880878761154659466396173 12705329535432997299898565)
      ·
        refine ⟨2382249287893686993730981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12705329535432997299898565 2382249287893686993730981)
        ·
          refine ⟨446671741480066311324559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2382249287893686993730981 446671741480066311324559)
          ·
            refine ⟨670007612220099466986839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 446671741480066311324559 670007612220099466986839)
            ·
              refine ⟨1005011418330149200480259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 670007612220099466986839 1005011418330149200480259)
              ·
                refine ⟨1507517127495223800720389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1005011418330149200480259 1507517127495223800720389)
                ·
                  refine ⟨282659461405354462635073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1507517127495223800720389 282659461405354462635073)
                  ·
                    rfl

theorem cell20_619287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 4, 1, 1, 1, 4].length) (baseStart_619287 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_619287 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_619287 prefixEnd_619287 := by exact prefixLift 619287
  have htrace : WordTrace (prefixWord ++ tailWord_619287) baseStart_619287 baseEnd_619287 := by
    simpa [prefixWord, tailWord_619287, baseEnd_619287] using wordTrace_append hprefix tailTrace_619287
  have hstable : (prefixWord ++ tailWord_619287).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_619287).length < 2 ^ (prefixWord ++ tailWord_619287).sum := by decide
  have hdescent : baseEnd_619287 < baseStart_619287 := by decide
  rcases family_descends (prefixWord ++ tailWord_619287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_619298 : List Nat := [3, 3, 1, 1, 2, 2, 1, 7]
def baseStart_619298 : Nat := 118140960795 + 619298 * 2 ^ 59
def prefixEnd_619298 : Nat := 4983230072969 + 3 ^ 40 * 619298 * 2
def baseEnd_619298 : Nat := 94221494035029104422787

theorem tailTrace_619298 : CollatzResearch.WordTrace tailWord_619298 prefixEnd_619298 94221494035029104422787 := by
  unfold tailWord_619298
  simp only [CollatzResearch.WordTrace]
  refine ⟨5646913427599147130728637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15058435806931059015276365 5646913427599147130728637)
  ·
    refine ⟨2117592535349680174023239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5646913427599147130728637 2117592535349680174023239)
    ·
      refine ⟨3176388803024520261034859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2117592535349680174023239 3176388803024520261034859)
      ·
        refine ⟨4764583204536780391552289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3176388803024520261034859 4764583204536780391552289)
        ·
          refine ⟨3573437403402585293664217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4764583204536780391552289 3573437403402585293664217)
          ·
            refine ⟨2680078052551938970248163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3573437403402585293664217 2680078052551938970248163)
            ·
              refine ⟨4020117078827908455372245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2680078052551938970248163 4020117078827908455372245)
              ·
                refine ⟨94221494035029104422787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4020117078827908455372245 94221494035029104422787)
                ·
                  rfl

theorem cell20_619298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 1, 7].length) (baseStart_619298 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_619298 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_619298 prefixEnd_619298 := by exact prefixLift 619298
  have htrace : WordTrace (prefixWord ++ tailWord_619298) baseStart_619298 baseEnd_619298 := by
    simpa [prefixWord, tailWord_619298, baseEnd_619298] using wordTrace_append hprefix tailTrace_619298
  have hstable : (prefixWord ++ tailWord_619298).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_619298).length < 2 ^ (prefixWord ++ tailWord_619298).sum := by decide
  have hdescent : baseEnd_619298 < baseStart_619298 := by decide
  rcases family_descends (prefixWord ++ tailWord_619298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_619305 : List Nat := [1, 2, 1, 1, 1, 1, 1, 9, 3]
def baseStart_619305 : Nat := 118140960795 + 619305 * 2 ^ 59
def prefixEnd_619305 : Nat := 4983230072969 + 3 ^ 40 * 619305 * 2
def baseEnd_619305 : Nat := 282667677095826400034999

theorem tailTrace_619305 : CollatzResearch.WordTrace tailWord_619305 prefixEnd_619305 282667677095826400034999 := by
  unfold tailWord_619305
  simp only [CollatzResearch.WordTrace]
  refine ⟨22587909021371228718419369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15058606014247485812279579 22587909021371228718419369)
  ·
    refine ⟨16940931766028421538814527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22587909021371228718419369 16940931766028421538814527)
    ·
      refine ⟨25411397649042632308221791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16940931766028421538814527 25411397649042632308221791)
      ·
        refine ⟨38117096473563948462332687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25411397649042632308221791 38117096473563948462332687)
        ·
          refine ⟨57175644710345922693499031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38117096473563948462332687 57175644710345922693499031)
          ·
            refine ⟨85763467065518884040248547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57175644710345922693499031 85763467065518884040248547)
            ·
              refine ⟨128645200598278326060372821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 85763467065518884040248547 128645200598278326060372821)
              ·
                refine ⟨753780472255537066759997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 128645200598278326060372821 753780472255537066759997)
                ·
                  refine ⟨282667677095826400034999, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 753780472255537066759997 282667677095826400034999)
                  ·
                    rfl

theorem cell20_619305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 9, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 9, 3].length) (baseStart_619305 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_619305 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_619305 prefixEnd_619305 := by exact prefixLift 619305
  have htrace : WordTrace (prefixWord ++ tailWord_619305) baseStart_619305 baseEnd_619305 := by
    simpa [prefixWord, tailWord_619305, baseEnd_619305] using wordTrace_append hprefix tailTrace_619305
  have hstable : (prefixWord ++ tailWord_619305).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_619305).length < 2 ^ (prefixWord ++ tailWord_619305).sum := by decide
  have hdescent : baseEnd_619305 < baseStart_619305 := by decide
  rcases family_descends (prefixWord ++ tailWord_619305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_619312 : List Nat := [2, 1, 1, 1, 2, 2, 1, 6, 4]
def baseStart_619312 : Nat := 118140960795 + 619312 * 2 ^ 59
def prefixEnd_619312 : Nat := 4983230072969 + 3 ^ 40 * 619312 * 2
def baseEnd_619312 : Nat := 282670872086565486801637

theorem tailTrace_619312 : CollatzResearch.WordTrace tailWord_619312 prefixEnd_619312 282670872086565486801637 := by
  unfold tailWord_619312
  simp only [CollatzResearch.WordTrace]
  refine ⟨11294082166172934456962095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15058776221563912609282793 11294082166172934456962095)
  ·
    refine ⟨16941123249259401685443143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11294082166172934456962095 16941123249259401685443143)
    ·
      refine ⟨25411684873889102528164715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16941123249259401685443143 25411684873889102528164715)
      ·
        refine ⟨38117527310833653792247073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25411684873889102528164715 38117527310833653792247073)
        ·
          refine ⟨28588145483125240344185305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38117527310833653792247073 28588145483125240344185305)
          ·
            refine ⟨21441109112343930258138979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28588145483125240344185305 21441109112343930258138979)
            ·
              refine ⟨32161663668515895387208469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21441109112343930258138979 32161663668515895387208469)
              ·
                refine ⟨1507577984461682596275397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 32161663668515895387208469 1507577984461682596275397)
                ·
                  refine ⟨282670872086565486801637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1507577984461682596275397 282670872086565486801637)
                  ·
                    rfl

theorem cell20_619312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 6, 4].length) (baseStart_619312 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_619312 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_619312 prefixEnd_619312 := by exact prefixLift 619312
  have htrace : WordTrace (prefixWord ++ tailWord_619312) baseStart_619312 baseEnd_619312 := by
    simpa [prefixWord, tailWord_619312, baseEnd_619312] using wordTrace_append hprefix tailTrace_619312
  have hstable : (prefixWord ++ tailWord_619312).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_619312).length < 2 ^ (prefixWord ++ tailWord_619312).sum := by decide
  have hdescent : baseEnd_619312 < baseStart_619312 := by decide
  rcases family_descends (prefixWord ++ tailWord_619312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_619319 : List Nat := [1, 1, 3, 1, 2, 1, 3, 8]
def baseStart_619319 : Nat := 118140960795 + 619319 * 2 ^ 59
def prefixEnd_619319 : Nat := 4983230072969 + 3 ^ 40 * 619319 * 2
def baseEnd_619319 : Nat := 94224689025768191189425

theorem tailTrace_619319 : CollatzResearch.WordTrace tailWord_619319 prefixEnd_619319 94224689025768191189425 := by
  unfold tailWord_619319
  simp only [CollatzResearch.WordTrace]
  refine ⟨22588419643320509109429011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15058946428880339406286007 22588419643320509109429011)
  ·
    refine ⟨33882629464980763664143517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22588419643320509109429011 33882629464980763664143517)
    ·
      refine ⟨12705986049367786374053819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33882629464980763664143517 12705986049367786374053819)
      ·
        refine ⟨19058979074051679561080729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12705986049367786374053819 19058979074051679561080729)
        ·
          refine ⟨14294234305538759670810547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19058979074051679561080729 14294234305538759670810547)
          ·
            refine ⟨21441351458308139506215821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14294234305538759670810547 21441351458308139506215821)
            ·
              refine ⟨8040506796865552314830933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21441351458308139506215821 8040506796865552314830933)
              ·
                refine ⟨94224689025768191189425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8040506796865552314830933 94224689025768191189425)
                ·
                  rfl

theorem cell20_619319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 3, 8].length) (baseStart_619319 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_619319 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_619319 prefixEnd_619319 := by exact prefixLift 619319
  have htrace : WordTrace (prefixWord ++ tailWord_619319) baseStart_619319 baseEnd_619319 := by
    simpa [prefixWord, tailWord_619319, baseEnd_619319] using wordTrace_append hprefix tailTrace_619319
  have hstable : (prefixWord ++ tailWord_619319).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_619319).length < 2 ^ (prefixWord ++ tailWord_619319).sum := by decide
  have hdescent : baseEnd_619319 < baseStart_619319 := by decide
  rcases family_descends (prefixWord ++ tailWord_619319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_619332 : List Nat := [2, 3, 4, 2, 2, 7]
def baseStart_619332 : Nat := 118140960795 + 619332 * 2 ^ 59
def prefixEnd_619332 : Nat := 4983230072969 + 3 ^ 40 * 619332 * 2
def baseEnd_619332 : Nat := 10469629653019789116107

theorem tailTrace_619332 : CollatzResearch.WordTrace tailWord_619332 prefixEnd_619332 10469629653019789116107 := by
  unfold tailWord_619332
  simp only [CollatzResearch.WordTrace]
  refine ⟨11294446896136706164826125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15059262528182274886434833 11294446896136706164826125)
  ·
    refine ⟨4235417586051264811809797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11294446896136706164826125 4235417586051264811809797)
    ·
      refine ⟨794140797384612152214337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4235417586051264811809797 794140797384612152214337)
      ·
        refine ⟨595605598038459114160753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 794140797384612152214337 595605598038459114160753)
        ·
          refine ⟨446704198528844335620565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 595605598038459114160753 446704198528844335620565)
          ·
            refine ⟨10469629653019789116107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 446704198528844335620565 10469629653019789116107)
            ·
              rfl

theorem cell20_619332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 2, 7].length) (baseStart_619332 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_619332 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_619332 prefixEnd_619332 := by exact prefixLift 619332
  have htrace : WordTrace (prefixWord ++ tailWord_619332) baseStart_619332 baseEnd_619332 := by
    simpa [prefixWord, tailWord_619332, baseEnd_619332] using wordTrace_append hprefix tailTrace_619332
  have hstable : (prefixWord ++ tailWord_619332).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_619332).length < 2 ^ (prefixWord ++ tailWord_619332).sum := by decide
  have hdescent : baseEnd_619332 < baseStart_619332 := by decide
  rcases family_descends (prefixWord ++ tailWord_619332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_619346 : List Nat := [3, 2, 2, 1, 1, 2, 3, 4, 2]
def baseStart_619346 : Nat := 118140960795 + 619346 * 2 ^ 59
def prefixEnd_619346 : Nat := 4983230072969 + 3 ^ 40 * 619346 * 2
def baseEnd_619346 : Nat := 282686390613012479668165

theorem tailTrace_619346 : CollatzResearch.WordTrace tailWord_619346 prefixEnd_619346 282686390613012479668165 := by
  unfold tailWord_619346
  simp only [CollatzResearch.WordTrace]
  refine ⟨5647351103555673180165473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15059602942815128480441261 5647351103555673180165473)
  ·
    refine ⟨4235513327666754885124105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5647351103555673180165473 4235513327666754885124105)
    ·
      refine ⟨3176634995750066163843079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4235513327666754885124105 3176634995750066163843079)
      ·
        refine ⟨4764952493625099245764619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3176634995750066163843079 4764952493625099245764619)
        ·
          refine ⟨7147428740437648868646929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4764952493625099245764619 7147428740437648868646929)
          ·
            refine ⟨5360571555328236651485197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7147428740437648868646929 5360571555328236651485197)
            ·
              refine ⟨2010214333248088744306949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5360571555328236651485197 2010214333248088744306949)
              ·
                refine ⟨376915187484016639557553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2010214333248088744306949 376915187484016639557553)
                ·
                  refine ⟨282686390613012479668165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 376915187484016639557553 282686390613012479668165)
                  ·
                    rfl

theorem cell20_619346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 3, 4, 2].length) (baseStart_619346 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_619346 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_619346 prefixEnd_619346 := by exact prefixLift 619346
  have htrace : WordTrace (prefixWord ++ tailWord_619346) baseStart_619346 baseEnd_619346 := by
    simpa [prefixWord, tailWord_619346, baseEnd_619346] using wordTrace_append hprefix tailTrace_619346
  have hstable : (prefixWord ++ tailWord_619346).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_619346).length < 2 ^ (prefixWord ++ tailWord_619346).sum := by decide
  have hdescent : baseEnd_619346 < baseStart_619346 := by decide
  rcases family_descends (prefixWord ++ tailWord_619346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_619367 : List Nat := [1, 1, 5, 1, 2, 3, 1, 2, 4]
def baseStart_619367 : Nat := 118140960795 + 619367 * 2 ^ 59
def prefixEnd_619367 : Nat := 4983230072969 + 3 ^ 40 * 619367 * 2
def baseEnd_619367 : Nat := 282695975585229739968079

theorem tailTrace_619367 : CollatzResearch.WordTrace tailWord_619367 prefixEnd_619367 282695975585229739968079 := by
  unfold tailWord_619367
  simp only [CollatzResearch.WordTrace]
  refine ⟨22590170347146613307176355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15060113564764408871450903 22590170347146613307176355)
  ·
    refine ⟨33885255520719919960764533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22590170347146613307176355 33885255520719919960764533)
    ·
      refine ⟨3176742705067492496321675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 33885255520719919960764533 3176742705067492496321675)
      ·
        refine ⟨4765114057601238744482513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3176742705067492496321675 4765114057601238744482513)
        ·
          refine ⟨3573835543200929058361885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4765114057601238744482513 3573835543200929058361885)
          ·
            refine ⟨1340188328700348396885707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3573835543200929058361885 1340188328700348396885707)
            ·
              refine ⟨2010282493050522595328561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1340188328700348396885707 2010282493050522595328561)
              ·
                refine ⟨1507711869787891946496421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2010282493050522595328561 1507711869787891946496421)
                ·
                  refine ⟨282695975585229739968079, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1507711869787891946496421 282695975585229739968079)
                  ·
                    rfl

theorem cell20_619367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 3, 1, 2, 4].length) (baseStart_619367 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_619367 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_619367 prefixEnd_619367 := by exact prefixLift 619367
  have htrace : WordTrace (prefixWord ++ tailWord_619367) baseStart_619367 baseEnd_619367 := by
    simpa [prefixWord, tailWord_619367, baseEnd_619367] using wordTrace_append hprefix tailTrace_619367
  have hstable : (prefixWord ++ tailWord_619367).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_619367).length < 2 ^ (prefixWord ++ tailWord_619367).sum := by decide
  have hdescent : baseEnd_619367 < baseStart_619367 := by decide
  rcases family_descends (prefixWord ++ tailWord_619367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_619394 : List Nat := [3, 4, 2, 2, 1, 1, 1, 1, 5]
def baseStart_619394 : Nat := 118140960795 + 619394 * 2 ^ 59
def prefixEnd_619394 : Nat := 4983230072969 + 3 ^ 40 * 619394 * 2
def baseEnd_619394 : Nat := 282708299120937646067969

theorem tailTrace_619394 : CollatzResearch.WordTrace tailWord_619394 prefixEnd_619394 282708299120937646067969 := by
  unfold tailWord_619394
  simp only [CollatzResearch.WordTrace]
  refine ⟨5647788779512199229602309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15060770078699197945606157 5647788779512199229602309)
  ·
    refine ⟨1058960396158537355550433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5647788779512199229602309 1058960396158537355550433)
    ·
      refine ⟨794220297118903016662825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1058960396158537355550433 794220297118903016662825)
      ·
        refine ⟨595665222839177262497119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 794220297118903016662825 595665222839177262497119)
        ·
          refine ⟨893497834258765893745679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 595665222839177262497119 893497834258765893745679)
          ·
            refine ⟨1340246751388148840618519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 893497834258765893745679 1340246751388148840618519)
            ·
              refine ⟨2010370127082223260927779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1340246751388148840618519 2010370127082223260927779)
              ·
                refine ⟨3015555190623334891391669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2010370127082223260927779 3015555190623334891391669)
                ·
                  refine ⟨282708299120937646067969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3015555190623334891391669 282708299120937646067969)
                  ·
                    rfl

theorem cell20_619394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 1, 1, 1, 5].length) (baseStart_619394 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_619394 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_619394 prefixEnd_619394 := by exact prefixLift 619394
  have htrace : WordTrace (prefixWord ++ tailWord_619394) baseStart_619394 baseEnd_619394 := by
    simpa [prefixWord, tailWord_619394, baseEnd_619394] using wordTrace_append hprefix tailTrace_619394
  have hstable : (prefixWord ++ tailWord_619394).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_619394).length < 2 ^ (prefixWord ++ tailWord_619394).sum := by decide
  have hdescent : baseEnd_619394 < baseStart_619394 := by decide
  rcases family_descends (prefixWord ++ tailWord_619394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_619395 : List Nat := [1, 1, 1, 3, 4, 1, 9]
def baseStart_619395 : Nat := 118140960795 + 619395 * 2 ^ 59
def prefixEnd_619395 : Nat := 4983230072969 + 3 ^ 40 * 619395 * 2
def baseEnd_619395 : Nat := 31412083949798454114959

theorem tailTrace_619395 : CollatzResearch.WordTrace tailWord_619395 prefixEnd_619395 31412083949798454114959 := by
  unfold tailWord_619395
  simp only [CollatzResearch.WordTrace]
  refine ⟨22591191591045174089195639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15060794394030116059463759 22591191591045174089195639)
  ·
    refine ⟨33886787386567761133793459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22591191591045174089195639 33886787386567761133793459)
    ·
      refine ⟨50830181079851641700690189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33886787386567761133793459 50830181079851641700690189)
      ·
        refine ⟨19061317904944365637758821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 50830181079851641700690189 19061317904944365637758821)
        ·
          refine ⟨3573997107177068557079779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19061317904944365637758821 3573997107177068557079779)
          ·
            refine ⟨5360995660765602835619669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3573997107177068557079779 5360995660765602835619669)
            ·
              refine ⟨31412083949798454114959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 5360995660765602835619669 31412083949798454114959)
              ·
                rfl

theorem cell20_619395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 9].length) (baseStart_619395 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_619395 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_619395 prefixEnd_619395 := by exact prefixLift 619395
  have htrace : WordTrace (prefixWord ++ tailWord_619395) baseStart_619395 baseEnd_619395 := by
    simpa [prefixWord, tailWord_619395, baseEnd_619395] using wordTrace_append hprefix tailTrace_619395
  have hstable : (prefixWord ++ tailWord_619395).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_619395).length < 2 ^ (prefixWord ++ tailWord_619395).sum := by decide
  have hdescent : baseEnd_619395 < baseStart_619395 := by decide
  rcases family_descends (prefixWord ++ tailWord_619395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_619412 : List Nat := [2, 4, 2, 1, 1, 1, 2, 7]
def baseStart_619412 : Nat := 118140960795 + 619412 * 2 ^ 59
def prefixEnd_619412 : Nat := 4983230072969 + 3 ^ 40 * 619412 * 2
def baseEnd_619412 : Nat := 94238838270469861155965

theorem tailTrace_619412 : CollatzResearch.WordTrace tailWord_619412 prefixEnd_619412 94238838270469861155965 := by
  unfold tailWord_619412
  simp only [CollatzResearch.WordTrace]
  refine ⟨11295905815991792996282245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15061207754655723995042993 11295905815991792996282245)
  ·
    refine ⟨2117982340498461186802921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11295905815991792996282245 2117982340498461186802921)
    ·
      refine ⟨1588486755373845890102191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2117982340498461186802921 1588486755373845890102191)
      ·
        refine ⟨2382730133060768835153287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1588486755373845890102191 2382730133060768835153287)
        ·
          refine ⟨3574095199591153252729931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2382730133060768835153287 3574095199591153252729931)
          ·
            refine ⟨5361142799386729879094897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3574095199591153252729931 5361142799386729879094897)
            ·
              refine ⟨4020857099540047409321173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5361142799386729879094897 4020857099540047409321173)
              ·
                refine ⟨94238838270469861155965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4020857099540047409321173 94238838270469861155965)
                ·
                  rfl

theorem cell20_619412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 2, 7].length) (baseStart_619412 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_619412 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_619412 prefixEnd_619412 := by exact prefixLift 619412
  have htrace : WordTrace (prefixWord ++ tailWord_619412) baseStart_619412 baseEnd_619412 := by
    simpa [prefixWord, tailWord_619412, baseEnd_619412] using wordTrace_append hprefix tailTrace_619412
  have hstable : (prefixWord ++ tailWord_619412).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_619412).length < 2 ^ (prefixWord ++ tailWord_619412).sum := by decide
  have hdescent : baseEnd_619412 < baseStart_619412 := by decide
  rcases family_descends (prefixWord ++ tailWord_619412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_619433 : List Nat := [1, 2, 1, 1, 1, 1, 7, 6]
def baseStart_619433 : Nat := 118140960795 + 619433 * 2 ^ 59
def prefixEnd_619433 : Nat := 4983230072969 + 3 ^ 40 * 619433 * 2
def baseEnd_619433 : Nat := 94242033261208947922603

theorem tailTrace_619433 : CollatzResearch.WordTrace tailWord_619433 prefixEnd_619433 94242033261208947922603 := by
  unfold tailWord_619433
  simp only [CollatzResearch.WordTrace]
  refine ⟨22592577564907506579078953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15061718376605004386052635 22592577564907506579078953)
  ·
    refine ⟨16944433173680629934309215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22592577564907506579078953 16944433173680629934309215)
    ·
      refine ⟨25416649760520944901463823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16944433173680629934309215 25416649760520944901463823)
      ·
        refine ⟨38124974640781417352195735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25416649760520944901463823 38124974640781417352195735)
        ·
          refine ⟨57187461961172126028293603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38124974640781417352195735 57187461961172126028293603)
          ·
            refine ⟨85781192941758189042440405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57187461961172126028293603 85781192941758189042440405)
            ·
              refine ⟨2010496709572457555682197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 85781192941758189042440405 2010496709572457555682197)
              ·
                refine ⟨94242033261208947922603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2010496709572457555682197 94242033261208947922603)
                ·
                  rfl

theorem cell20_619433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 7, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 7, 6].length) (baseStart_619433 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_619433 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_619433 prefixEnd_619433 := by exact prefixLift 619433
  have htrace : WordTrace (prefixWord ++ tailWord_619433) baseStart_619433 baseEnd_619433 := by
    simpa [prefixWord, tailWord_619433, baseEnd_619433] using wordTrace_append hprefix tailTrace_619433
  have hstable : (prefixWord ++ tailWord_619433).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_619433).length < 2 ^ (prefixWord ++ tailWord_619433).sum := by decide
  have hdescent : baseEnd_619433 < baseStart_619433 := by decide
  rcases family_descends (prefixWord ++ tailWord_619433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_619443 : List Nat := [1, 1, 1, 2, 3, 1, 2, 7, 2]
def baseStart_619443 : Nat := 118140960795 + 619443 * 2 ^ 59
def prefixEnd_619443 : Nat := 4983230072969 + 3 ^ 40 * 619443 * 2
def baseEnd_619443 : Nat := 282730664056111253434435

theorem tailTrace_619443 : CollatzResearch.WordTrace tailWord_619443 prefixEnd_619443 282730664056111253434435 := by
  unfold tailWord_619443
  simp only [CollatzResearch.WordTrace]
  refine ⟨22592942294871278286942983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15061961529914185524628655 22592942294871278286942983)
  ·
    refine ⟨33889413442306917430414475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22592942294871278286942983 33889413442306917430414475)
    ·
      refine ⟨50834120163460376145621713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33889413442306917430414475 50834120163460376145621713)
      ·
        refine ⟨38125590122595282109216285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50834120163460376145621713 38125590122595282109216285)
        ·
          refine ⟨14297096295973230790956107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38125590122595282109216285 14297096295973230790956107)
          ·
            refine ⟨21445644443959846186434161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14297096295973230790956107 21445644443959846186434161)
            ·
              refine ⟨16084233332969884639825621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21445644443959846186434161 16084233332969884639825621)
              ·
                refine ⟨376974218741481671245913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 16084233332969884639825621 376974218741481671245913)
                ·
                  refine ⟨282730664056111253434435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 376974218741481671245913 282730664056111253434435)
                  ·
                    rfl

theorem cell20_619443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 7, 2].length) (baseStart_619443 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_619443 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_619443 prefixEnd_619443 := by exact prefixLift 619443
  have htrace : WordTrace (prefixWord ++ tailWord_619443) baseStart_619443 baseEnd_619443 := by
    simpa [prefixWord, tailWord_619443, baseEnd_619443] using wordTrace_append hprefix tailTrace_619443
  have hstable : (prefixWord ++ tailWord_619443).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_619443).length < 2 ^ (prefixWord ++ tailWord_619443).sum := by decide
  have hdescent : baseEnd_619443 < baseStart_619443 := by decide
  rcases family_descends (prefixWord ++ tailWord_619443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_619462 : List Nat := [6, 1, 3, 1, 2, 1, 2, 1, 3]
def baseStart_619462 : Nat := 118140960795 + 619462 * 2 ^ 59
def prefixEnd_619462 : Nat := 4983230072969 + 3 ^ 40 * 619462 * 2
def baseEnd_619462 : Nat := 282739336173831631801025

theorem tailTrace_619462 : CollatzResearch.WordTrace tailWord_619462 prefixEnd_619462 282739336173831631801025 := by
  unfold tailWord_619462
  simp only [CollatzResearch.WordTrace]
  refine ⟨706051102556326391621395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 15062423521201629687923093 706051102556326391621395)
  ·
    refine ⟨1059076653834489587432093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 706051102556326391621395 1059076653834489587432093)
    ·
      refine ⟨397153745187933595287035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1059076653834489587432093 397153745187933595287035)
      ·
        refine ⟨595730617781900392930553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 397153745187933595287035 595730617781900392930553)
        ·
          refine ⟨446797963336425294697915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 595730617781900392930553 446797963336425294697915)
          ·
            refine ⟨670196945004637942046873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 446797963336425294697915 670196945004637942046873)
            ·
              refine ⟨502647708753478456535155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 670196945004637942046873 502647708753478456535155)
              ·
                refine ⟨753971563130217684802733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 502647708753478456535155 753971563130217684802733)
                ·
                  refine ⟨282739336173831631801025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 753971563130217684802733 282739336173831631801025)
                  ·
                    rfl

theorem cell20_619462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 2, 1, 2, 1, 3].length) (baseStart_619462 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_619462 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_619462 prefixEnd_619462 := by exact prefixLift 619462
  have htrace : WordTrace (prefixWord ++ tailWord_619462) baseStart_619462 baseEnd_619462 := by
    simpa [prefixWord, tailWord_619462, baseEnd_619462] using wordTrace_append hprefix tailTrace_619462
  have hstable : (prefixWord ++ tailWord_619462).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_619462).length < 2 ^ (prefixWord ++ tailWord_619462).sum := by decide
  have hdescent : baseEnd_619462 < baseStart_619462 := by decide
  rcases family_descends (prefixWord ++ tailWord_619462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_619471 : List Nat := [1, 1, 2, 1, 1, 6, 1, 7]
def baseStart_619471 : Nat := 118140960795 + 619471 * 2 ^ 59
def prefixEnd_619471 : Nat := 4983230072969 + 3 ^ 40 * 619471 * 2
def baseEnd_619471 : Nat := 94247814673022533500329

theorem tailTrace_619471 : CollatzResearch.WordTrace tailWord_619471 prefixEnd_619471 94247814673022533500329 := by
  unfold tailWord_619471
  simp only [CollatzResearch.WordTrace]
  refine ⟨22593963538769839068962267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15062642359179892712641511 22593963538769839068962267)
  ·
    refine ⟨33890945308154758603443401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22593963538769839068962267 33890945308154758603443401)
    ·
      refine ⟨25418208981116068952582551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33890945308154758603443401 25418208981116068952582551)
      ·
        refine ⟨38127313471674103428873827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25418208981116068952582551 38127313471674103428873827)
        ·
          refine ⟨57190970207511155143310741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38127313471674103428873827 57190970207511155143310741)
          ·
            refine ⟨2680826728477085397342691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 57190970207511155143310741 2680826728477085397342691)
            ·
              refine ⟨4021240092715628096014037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2680826728477085397342691 4021240092715628096014037)
              ·
                refine ⟨94247814673022533500329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4021240092715628096014037 94247814673022533500329)
                ·
                  rfl

theorem cell20_619471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 1, 7].length) (baseStart_619471 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_619471 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_619471 prefixEnd_619471 := by exact prefixLift 619471
  have htrace : WordTrace (prefixWord ++ tailWord_619471) baseStart_619471 baseEnd_619471 := by
    simpa [prefixWord, tailWord_619471, baseEnd_619471] using wordTrace_append hprefix tailTrace_619471
  have hstable : (prefixWord ++ tailWord_619471).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_619471).length < 2 ^ (prefixWord ++ tailWord_619471).sum := by decide
  have hdescent : baseEnd_619471 < baseStart_619471 := by decide
  rcases family_descends (prefixWord ++ tailWord_619471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_619543 : List Nat := [1, 1, 3, 5, 1, 2, 3, 4]
def baseStart_619543 : Nat := 118140960795 + 619543 * 2 ^ 59
def prefixEnd_619543 : Nat := 4983230072969 + 3 ^ 40 * 619543 * 2
def baseEnd_619543 : Nat := 94258768926985116700231

theorem tailTrace_619543 : CollatzResearch.WordTrace tailWord_619543 prefixEnd_619543 94258768926985116700231 := by
  unfold tailWord_619543
  simp only [CollatzResearch.WordTrace]
  refine ⟨22596589594508995365583283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15064393063005996910388855 22596589594508995365583283)
  ·
    refine ⟨33894884391763493048374925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22596589594508995365583283 33894884391763493048374925)
    ·
      refine ⟨12710581646911309893140597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33894884391763493048374925 12710581646911309893140597)
      ·
        refine ⟨1191617029397935302481931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 12710581646911309893140597 1191617029397935302481931)
        ·
          refine ⟨1787425544096902953722897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1191617029397935302481931 1787425544096902953722897)
          ·
            refine ⟨1340569158072677215292173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1787425544096902953722897 1340569158072677215292173)
            ·
              refine ⟨502713434277253955734565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1340569158072677215292173 502713434277253955734565)
              ·
                refine ⟨94258768926985116700231, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 502713434277253955734565 94258768926985116700231)
                ·
                  rfl

theorem cell20_619543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 2, 3, 4].length) (baseStart_619543 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_619543 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_619543 prefixEnd_619543 := by exact prefixLift 619543
  have htrace : WordTrace (prefixWord ++ tailWord_619543) baseStart_619543 baseEnd_619543 := by
    simpa [prefixWord, tailWord_619543, baseEnd_619543] using wordTrace_append hprefix tailTrace_619543
  have hstable : (prefixWord ++ tailWord_619543).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_619543).length < 2 ^ (prefixWord ++ tailWord_619543).sum := by decide
  have hdescent : baseEnd_619543 < baseStart_619543 := by decide
  rcases family_descends (prefixWord ++ tailWord_619543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_619574 : List Nat := [5, 1, 2, 1, 1, 3, 2, 1, 4]
def baseStart_619574 : Nat := 118140960795 + 619574 * 2 ^ 59
def prefixEnd_619574 : Nat := 4983230072969 + 3 ^ 40 * 619574 * 2
def baseEnd_619574 : Nat := 282790456025657020067233

theorem tailTrace_619574 : CollatzResearch.WordTrace tailWord_619574 prefixEnd_619574 282790456025657020067233 := by
  unfold tailWord_619574
  simp only [CollatzResearch.WordTrace]
  refine ⟨1412357516087292978747611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 15065146838264458439974517 1412357516087292978747611)
  ·
    refine ⟨2118536274130939468121417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1412357516087292978747611 2118536274130939468121417)
    ·
      refine ⟨1588902205598204601091063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2118536274130939468121417 1588902205598204601091063)
      ·
        refine ⟨2383353308397306901636595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1588902205598204601091063 2383353308397306901636595)
        ·
          refine ⟨3575029962595960352454893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2383353308397306901636595 3575029962595960352454893)
          ·
            refine ⟨1340636235973485132170585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3575029962595960352454893 1340636235973485132170585)
            ·
              refine ⟨1005477176980113849127939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1340636235973485132170585 1005477176980113849127939)
              ·
                refine ⟨1508215765470170773691909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1005477176980113849127939 1508215765470170773691909)
                ·
                  refine ⟨282790456025657020067233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1508215765470170773691909 282790456025657020067233)
                  ·
                    rfl

theorem cell20_619574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 3, 2, 1, 4].length) (baseStart_619574 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_619574 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_619574 prefixEnd_619574 := by exact prefixLift 619574
  have htrace : WordTrace (prefixWord ++ tailWord_619574) baseStart_619574 baseEnd_619574 := by
    simpa [prefixWord, tailWord_619574, baseEnd_619574] using wordTrace_append hprefix tailTrace_619574
  have hstable : (prefixWord ++ tailWord_619574).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_619574).length < 2 ^ (prefixWord ++ tailWord_619574).sum := by decide
  have hdescent : baseEnd_619574 < baseStart_619574 := by decide
  rcases family_descends (prefixWord ++ tailWord_619574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_619578 : List Nat := [3, 1, 1, 1, 3, 1, 3, 3, 4]
def baseStart_619578 : Nat := 118140960795 + 619578 * 2 ^ 59
def prefixEnd_619578 : Nat := 4983230072969 + 3 ^ 40 * 619578 * 2
def baseEnd_619578 : Nat := 282792281734650783933883

theorem tailTrace_619578 : CollatzResearch.WordTrace tailWord_619578 prefixEnd_619578 282792281734650783933883 := by
  unfold tailWord_619578
  simp only [CollatzResearch.WordTrace]
  refine ⟨5649466537345549085776847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15065244099588130895404925 5649466537345549085776847)
  ·
    refine ⟨8474199806018323628665271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5649466537345549085776847 8474199806018323628665271)
    ·
      refine ⟨12711299709027485442997907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8474199806018323628665271 12711299709027485442997907)
      ·
        refine ⟨19066949563541228164496861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12711299709027485442997907 19066949563541228164496861)
        ·
          refine ⟨7150106086327960561686323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19066949563541228164496861 7150106086327960561686323)
          ·
            refine ⟨10725159129491940842529485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7150106086327960561686323 10725159129491940842529485)
            ·
              refine ⟨4021934673559477815948557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10725159129491940842529485 4021934673559477815948557)
              ·
                refine ⟨1508225502584804180980709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4021934673559477815948557 1508225502584804180980709)
                ·
                  refine ⟨282792281734650783933883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1508225502584804180980709 282792281734650783933883)
                  ·
                    rfl

theorem cell20_619578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 3, 3, 4].length) (baseStart_619578 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_619578 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_619578 prefixEnd_619578 := by exact prefixLift 619578
  have htrace : WordTrace (prefixWord ++ tailWord_619578) baseStart_619578 baseEnd_619578 := by
    simpa [prefixWord, tailWord_619578, baseEnd_619578] using wordTrace_append hprefix tailTrace_619578
  have hstable : (prefixWord ++ tailWord_619578).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_619578).length < 2 ^ (prefixWord ++ tailWord_619578).sum := by decide
  have hdescent : baseEnd_619578 < baseStart_619578 := by decide
  rcases family_descends (prefixWord ++ tailWord_619578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_619602 : List Nat := [3, 2, 2, 1, 3, 2, 1, 6]
def baseStart_619602 : Nat := 118140960795 + 619602 * 2 ^ 59
def prefixEnd_619602 : Nat := 4983230072969 + 3 ^ 40 * 619602 * 2
def baseEnd_619602 : Nat := 94267745329537789044595

theorem tailTrace_619602 : CollatzResearch.WordTrace tailWord_619602 prefixEnd_619602 94267745329537789044595 := by
  unfold tailWord_619602
  simp only [CollatzResearch.WordTrace]
  refine ⟨5649685375323812110495265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15065827667530165627987373 5649685375323812110495265)
  ·
    refine ⟨4237264031492859082871449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5649685375323812110495265 4237264031492859082871449)
    ·
      refine ⟨3177948023619644312153587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4237264031492859082871449 3177948023619644312153587)
      ·
        refine ⟨4766922035429466468230381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3177948023619644312153587 4766922035429466468230381)
        ·
          refine ⟨1787595763286049925586393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4766922035429466468230381 1787595763286049925586393)
          ·
            refine ⟨1340696822464537444189795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1787595763286049925586393 1340696822464537444189795)
            ·
              refine ⟨2011045233696806166284693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1340696822464537444189795 2011045233696806166284693)
              ·
                refine ⟨94267745329537789044595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2011045233696806166284693 94267745329537789044595)
                ·
                  rfl

theorem cell20_619602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 2, 1, 6].length) (baseStart_619602 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_619602 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_619602 prefixEnd_619602 := by exact prefixLift 619602
  have htrace : WordTrace (prefixWord ++ tailWord_619602) baseStart_619602 baseEnd_619602 := by
    simpa [prefixWord, tailWord_619602, baseEnd_619602] using wordTrace_append hprefix tailTrace_619602
  have hstable : (prefixWord ++ tailWord_619602).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_619602).length < 2 ^ (prefixWord ++ tailWord_619602).sum := by decide
  have hdescent : baseEnd_619602 < baseStart_619602 := by decide
  rcases family_descends (prefixWord ++ tailWord_619602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_619623 : List Nat := [1, 1, 5, 1, 1, 3, 8]
def baseStart_619623 : Nat := 118140960795 + 619623 * 2 ^ 59
def prefixEnd_619623 : Nat := 4983230072969 + 3 ^ 40 * 619623 * 2
def baseEnd_619623 : Nat := 31423646773425625270411

theorem tailTrace_619623 : CollatzResearch.WordTrace tailWord_619623 prefixEnd_619623 31423646773425625270411 := by
  unfold tailWord_619623
  simp only [CollatzResearch.WordTrace]
  refine ⟨22599507434219169028495523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15066338289479446018997015 22599507434219169028495523)
  ·
    refine ⟨33899261151328753542743285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22599507434219169028495523 33899261151328753542743285)
    ·
      refine ⟨3178055732937070644632183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 33899261151328753542743285 3178055732937070644632183)
      ·
        refine ⟨4767083599405605966948275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3178055732937070644632183 4767083599405605966948275)
        ·
          refine ⟨7150625399108408950422413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4767083599405605966948275 7150625399108408950422413)
          ·
            refine ⟨2681484524665653356408405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7150625399108408950422413 2681484524665653356408405)
            ·
              refine ⟨31423646773425625270411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2681484524665653356408405 31423646773425625270411)
              ·
                rfl

theorem cell20_619623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 8].length) (baseStart_619623 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_619623 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_619623 prefixEnd_619623 := by exact prefixLift 619623
  have htrace : WordTrace (prefixWord ++ tailWord_619623) baseStart_619623 baseEnd_619623 := by
    simpa [prefixWord, tailWord_619623, baseEnd_619623] using wordTrace_append hprefix tailTrace_619623
  have hstable : (prefixWord ++ tailWord_619623).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_619623).length < 2 ^ (prefixWord ++ tailWord_619623).sum := by decide
  have hdescent : baseEnd_619623 < baseStart_619623 := by decide
  rcases family_descends (prefixWord ++ tailWord_619623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_619629 : List Nat := [1, 5, 1, 1, 2, 3, 3, 2, 2]
def baseStart_619629 : Nat := 118140960795 + 619629 * 2 ^ 59
def prefixEnd_619629 : Nat := 4983230072969 + 3 ^ 40 * 619629 * 2
def baseEnd_619629 : Nat := 282815559524321273233675

theorem tailTrace_619629 : CollatzResearch.WordTrace tailWord_619629 prefixEnd_619629 282815559524321273233675 := by
  unfold tailWord_619629
  simp only [CollatzResearch.WordTrace]
  refine ⟨22599726272197432053213941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15066484181464954702142627 22599726272197432053213941)
  ·
    refine ⟨2118724338018509254988807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 22599726272197432053213941 2118724338018509254988807)
    ·
      refine ⟨3178086507027763882483211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2118724338018509254988807 3178086507027763882483211)
      ·
        refine ⟨4767129760541645823724817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3178086507027763882483211 4767129760541645823724817)
        ·
          refine ⟨3575347320406234367793613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4767129760541645823724817 3575347320406234367793613)
          ·
            refine ⟨1340755245152337887922605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3575347320406234367793613 1340755245152337887922605)
            ·
              refine ⟨502783216932126707970977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1340755245152337887922605 502783216932126707970977)
              ·
                refine ⟨377087412699095030978233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 502783216932126707970977 377087412699095030978233)
                ·
                  refine ⟨282815559524321273233675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 377087412699095030978233 282815559524321273233675)
                  ·
                    rfl

theorem cell20_619629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 3, 3, 2, 2].length) (baseStart_619629 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_619629 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_619629 prefixEnd_619629 := by exact prefixLift 619629
  have htrace : WordTrace (prefixWord ++ tailWord_619629) baseStart_619629 baseEnd_619629 := by
    simpa [prefixWord, tailWord_619629, baseEnd_619629] using wordTrace_append hprefix tailTrace_619629
  have hstable : (prefixWord ++ tailWord_619629).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_619629).length < 2 ^ (prefixWord ++ tailWord_619629).sum := by decide
  have hdescent : baseEnd_619629 < baseStart_619629 := by decide
  rcases family_descends (prefixWord ++ tailWord_619629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_619678 : List Nat := [4, 3, 1, 1, 2, 9]
def baseStart_619678 : Nat := 118140960795 + 619678 * 2 ^ 59
def prefixEnd_619678 : Nat := 4983230072969 + 3 ^ 40 * 619678 * 2
def baseEnd_619678 : Nat := 10475478683684995577783

theorem tailTrace_619678 : CollatzResearch.WordTrace tailWord_619678 prefixEnd_619678 10475478683684995577783 := by
  unfold tailWord_619678
  simp only [CollatzResearch.WordTrace]
  refine ⟨2825189181127489177718461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15067675632679942281165125 2825189181127489177718461)
  ·
    refine ⟨1059445942922808441644423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2825189181127489177718461 1059445942922808441644423)
    ·
      refine ⟨1589168914384212662466635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1059445942922808441644423 1589168914384212662466635)
      ·
        refine ⟨2383753371576318993699953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1589168914384212662466635 2383753371576318993699953)
        ·
          refine ⟨1787815028682239245274965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2383753371576318993699953 1787815028682239245274965)
          ·
            refine ⟨10475478683684995577783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1787815028682239245274965 10475478683684995577783)
            ·
              rfl

theorem cell20_619678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 9].length) (baseStart_619678 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_619678 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_619678 prefixEnd_619678 := by exact prefixLift 619678
  have htrace : WordTrace (prefixWord ++ tailWord_619678) baseStart_619678 baseEnd_619678 := by
    simpa [prefixWord, tailWord_619678, baseEnd_619678] using wordTrace_append hprefix tailTrace_619678
  have hstable : (prefixWord ++ tailWord_619678).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_619678).length < 2 ^ (prefixWord ++ tailWord_619678).sum := by decide
  have hdescent : baseEnd_619678 < baseStart_619678 := by decide
  rcases family_descends (prefixWord ++ tailWord_619678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_619685 : List Nat := [1, 3, 1, 2, 1, 4, 1, 4, 3]
def baseStart_619685 : Nat := 118140960795 + 619685 * 2 ^ 59
def prefixEnd_619685 : Nat := 4983230072969 + 3 ^ 40 * 619685 * 2
def baseEnd_619685 : Nat := 282841119450233967366779

theorem tailTrace_619685 : CollatzResearch.WordTrace tailWord_619685 prefixEnd_619685 282841119450233967366779 := by
  unfold tailWord_619685
  simp only [CollatzResearch.WordTrace]
  refine ⟨22601768759994553617252509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15067845839996369078168339 22601768759994553617252509)
  ·
    refine ⟨8475663284997957606469691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22601768759994553617252509 8475663284997957606469691)
    ·
      refine ⟨12713494927496936409704537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8475663284997957606469691 12713494927496936409704537)
      ·
        refine ⟨9535121195622702307278403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12713494927496936409704537 9535121195622702307278403)
        ·
          refine ⟨14302681793434053460917605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9535121195622702307278403 14302681793434053460917605)
          ·
            refine ⟨2681752836268885023922051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14302681793434053460917605 2681752836268885023922051)
            ·
              refine ⟨4022629254403327535883077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2681752836268885023922051 4022629254403327535883077)
              ·
                refine ⟨754242985200623912978077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4022629254403327535883077 754242985200623912978077)
                ·
                  refine ⟨282841119450233967366779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 754242985200623912978077 282841119450233967366779)
                  ·
                    rfl

theorem cell20_619685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 1, 4, 3].length) (baseStart_619685 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_619685 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_619685 prefixEnd_619685 := by exact prefixLift 619685
  have htrace : WordTrace (prefixWord ++ tailWord_619685) baseStart_619685 baseEnd_619685 := by
    simpa [prefixWord, tailWord_619685, baseEnd_619685] using wordTrace_append hprefix tailTrace_619685
  have hstable : (prefixWord ++ tailWord_619685).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_619685).length < 2 ^ (prefixWord ++ tailWord_619685).sum := by decide
  have hdescent : baseEnd_619685 < baseStart_619685 := by decide
  rcases family_descends (prefixWord ++ tailWord_619685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_619699 : List Nat := [1, 1, 1, 2, 3, 2, 5, 5]
def baseStart_619699 : Nat := 118140960795 + 619699 * 2 ^ 59
def prefixEnd_619699 : Nat := 4983230072969 + 3 ^ 40 * 619699 * 2
def baseEnd_619699 : Nat := 94282503143904046966685

theorem tailTrace_619699 : CollatzResearch.WordTrace tailWord_619699 prefixEnd_619699 94282503143904046966685 := by
  unfold tailWord_619699
  simp only [CollatzResearch.WordTrace]
  refine ⟨22602279381943834008262151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15068186254629222672174767 22602279381943834008262151)
  ·
    refine ⟨33903419072915751012393227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22602279381943834008262151 33903419072915751012393227)
    ·
      refine ⟨50855128609373626518589841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33903419072915751012393227 50855128609373626518589841)
      ·
        refine ⟨38141346457030219888942381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50855128609373626518589841 38141346457030219888942381)
        ·
          refine ⟨14303004921386332458353393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38141346457030219888942381 14303004921386332458353393)
          ·
            refine ⟨10727253691039749343765045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14303004921386332458353393 10727253691039749343765045)
            ·
              refine ⟨1005680033534976500977973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 10727253691039749343765045 1005680033534976500977973)
              ·
                refine ⟨94282503143904046966685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1005680033534976500977973 94282503143904046966685)
                ·
                  rfl

theorem cell20_619699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 5, 5].length) (baseStart_619699 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_619699 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_619699 prefixEnd_619699 := by exact prefixLift 619699
  have htrace : WordTrace (prefixWord ++ tailWord_619699) baseStart_619699 baseEnd_619699 := by
    simpa [prefixWord, tailWord_619699, baseEnd_619699] using wordTrace_append hprefix tailTrace_619699
  have hstable : (prefixWord ++ tailWord_619699).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_619699).length < 2 ^ (prefixWord ++ tailWord_619699).sum := by decide
  have hdescent : baseEnd_619699 < baseStart_619699 := by decide
  rcases family_descends (prefixWord ++ tailWord_619699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_619706 : List Nat := [3, 1, 1, 1, 2, 2, 1, 2, 7]
def baseStart_619706 : Nat := 118140960795 + 619706 * 2 ^ 59
def prefixEnd_619706 : Nat := 4983230072969 + 3 ^ 40 * 619706 * 2
def baseEnd_619706 : Nat := 282850704422451227666693

theorem tailTrace_619706 : CollatzResearch.WordTrace tailWord_619706 prefixEnd_619706 282850704422451227666693 := by
  unfold tailWord_619706
  simp only [CollatzResearch.WordTrace]
  refine ⟨5650633673229618550941743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15068356461945649469177981 5650633673229618550941743)
  ·
    refine ⟨8475950509844427826412615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5650633673229618550941743 8475950509844427826412615)
    ·
      refine ⟨12713925764766641739618923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8475950509844427826412615 12713925764766641739618923)
      ·
        refine ⟨19070888647149962609428385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12713925764766641739618923 19070888647149962609428385)
        ·
          refine ⟨14303166485362471957071289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19070888647149962609428385 14303166485362471957071289)
          ·
            refine ⟨10727374864021853967803467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14303166485362471957071289 10727374864021853967803467)
            ·
              refine ⟨16091062296032780951705201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10727374864021853967803467 16091062296032780951705201)
              ·
                refine ⟨12068296722024585713778901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16091062296032780951705201 12068296722024585713778901)
                ·
                  refine ⟨282850704422451227666693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12068296722024585713778901 282850704422451227666693)
                  ·
                    rfl

theorem cell20_619706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 2, 7].length) (baseStart_619706 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_619706 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_619706 prefixEnd_619706 := by exact prefixLift 619706
  have htrace : WordTrace (prefixWord ++ tailWord_619706) baseStart_619706 baseEnd_619706 := by
    simpa [prefixWord, tailWord_619706, baseEnd_619706] using wordTrace_append hprefix tailTrace_619706
  have hstable : (prefixWord ++ tailWord_619706).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_619706).length < 2 ^ (prefixWord ++ tailWord_619706).sum := by decide
  have hdescent : baseEnd_619706 < baseStart_619706 := by decide
  rcases family_descends (prefixWord ++ tailWord_619706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_619730 : List Nat := [3, 2, 2, 2, 1, 1, 1, 2, 6]
def baseStart_619730 : Nat := 118140960795 + 619730 * 2 ^ 59
def prefixEnd_619730 : Nat := 4983230072969 + 3 ^ 40 * 619730 * 2
def baseEnd_619730 : Nat := 282861658676413810866595

theorem tailTrace_619730 : CollatzResearch.WordTrace tailWord_619730 prefixEnd_619730 282861658676413810866595 := by
  unfold tailWord_619730
  simp only [CollatzResearch.WordTrace]
  refine ⟨5650852511207881575660161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15068940029887684201760429 5650852511207881575660161)
  ·
    refine ⟨4238139383405911181745121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5650852511207881575660161 4238139383405911181745121)
    ·
      refine ⟨3178604537554433386308841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4238139383405911181745121 3178604537554433386308841)
      ·
        refine ⟨2383953403165825039731631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3178604537554433386308841 2383953403165825039731631)
        ·
          refine ⟨3575930104748737559597447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2383953403165825039731631 3575930104748737559597447)
          ·
            refine ⟨5363895157123106339396171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3575930104748737559597447 5363895157123106339396171)
            ·
              refine ⟨8045842735684659509094257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5363895157123106339396171 8045842735684659509094257)
              ·
                refine ⟨6034382051763494631820693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8045842735684659509094257 6034382051763494631820693)
                ·
                  refine ⟨282861658676413810866595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6034382051763494631820693 282861658676413810866595)
                  ·
                    rfl

theorem cell20_619730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 1, 2, 6].length) (baseStart_619730 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_619730 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_619730 prefixEnd_619730 := by exact prefixLift 619730
  have htrace : WordTrace (prefixWord ++ tailWord_619730) baseStart_619730 baseEnd_619730 := by
    simpa [prefixWord, tailWord_619730, baseEnd_619730] using wordTrace_append hprefix tailTrace_619730
  have hstable : (prefixWord ++ tailWord_619730).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_619730).length < 2 ^ (prefixWord ++ tailWord_619730).sum := by decide
  have hdescent : baseEnd_619730 < baseStart_619730 := by decide
  rcases family_descends (prefixWord ++ tailWord_619730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_619757 : List Nat := [1, 5, 1, 2, 2, 2, 3, 1, 3]
def baseStart_619757 : Nat := 118140960795 + 619757 * 2 ^ 59
def prefixEnd_619757 : Nat := 4983230072969 + 3 ^ 40 * 619757 * 2
def baseEnd_619757 : Nat := 282873982212121716966485

theorem tailTrace_619757 : CollatzResearch.WordTrace tailWord_619757 prefixEnd_619757 282873982212121716966485 := by
  unfold tailWord_619757
  simp only [CollatzResearch.WordTrace]
  refine ⟨22604394815733709913873525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15069596543822473275915683 22604394815733709913873525)
  ·
    refine ⟨2119162013975035304425643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 22604394815733709913873525 2119162013975035304425643)
    ·
      refine ⟨3178743020962552956638465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2119162013975035304425643 3178743020962552956638465)
      ·
        refine ⟨2384057265721914717478849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3178743020962552956638465 2384057265721914717478849)
        ·
          refine ⟨1788042949291436038109137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2384057265721914717478849 1788042949291436038109137)
          ·
            refine ⟨1341032211968577028581853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1788042949291436038109137 1341032211968577028581853)
            ·
              refine ⟨502887079488216385718195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1341032211968577028581853 502887079488216385718195)
              ·
                refine ⟨754330619232324578577293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 502887079488216385718195 754330619232324578577293)
                ·
                  refine ⟨282873982212121716966485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 754330619232324578577293 282873982212121716966485)
                  ·
                    rfl

theorem cell20_619757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 2, 3, 1, 3].length) (baseStart_619757 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_619757 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_619757 prefixEnd_619757 := by exact prefixLift 619757
  have htrace : WordTrace (prefixWord ++ tailWord_619757) baseStart_619757 baseEnd_619757 := by
    simpa [prefixWord, tailWord_619757, baseEnd_619757] using wordTrace_append hprefix tailTrace_619757
  have hstable : (prefixWord ++ tailWord_619757).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_619757).length < 2 ^ (prefixWord ++ tailWord_619757).sum := by decide
  have hdescent : baseEnd_619757 < baseStart_619757 := by decide
  rcases family_descends (prefixWord ++ tailWord_619757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_619775 : List Nat := [1, 1, 2, 2, 1, 6, 1, 6]
def baseStart_619775 : Nat := 118140960795 + 619775 * 2 ^ 59
def prefixEnd_619775 : Nat := 4983230072969 + 3 ^ 40 * 619775 * 2
def baseEnd_619775 : Nat := 94294065967531218122137

theorem tailTrace_619775 : CollatzResearch.WordTrace tailWord_619775 prefixEnd_619775 94294065967531218122137 := by
  unfold tailWord_619775
  simp only [CollatzResearch.WordTrace]
  refine ⟨22605051329668498988028779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15070034219778999325352519 22605051329668498988028779)
  ·
    refine ⟨33907576994502748482043169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22605051329668498988028779 33907576994502748482043169)
    ·
      refine ⟨25430682745877061361532377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33907576994502748482043169 25430682745877061361532377)
      ·
        refine ⟨19073012059407796021149283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25430682745877061361532377 19073012059407796021149283)
        ·
          refine ⟨28609518089111694031723925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19073012059407796021149283 28609518089111694031723925)
          ·
            refine ⟨1341071160427110657737059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 28609518089111694031723925 1341071160427110657737059)
            ·
              refine ⟨2011606740640665986605589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1341071160427110657737059 2011606740640665986605589)
              ·
                refine ⟨94294065967531218122137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2011606740640665986605589 94294065967531218122137)
                ·
                  rfl

theorem cell20_619775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 6, 1, 6].length) (baseStart_619775 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_619775 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_619775 prefixEnd_619775 := by exact prefixLift 619775
  have htrace : WordTrace (prefixWord ++ tailWord_619775) baseStart_619775 baseEnd_619775 := by
    simpa [prefixWord, tailWord_619775, baseEnd_619775] using wordTrace_append hprefix tailTrace_619775
  have hstable : (prefixWord ++ tailWord_619775).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_619775).length < 2 ^ (prefixWord ++ tailWord_619775).sum := by decide
  have hdescent : baseEnd_619775 < baseStart_619775 := by decide
  rcases family_descends (prefixWord ++ tailWord_619775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_619799 : List Nat := [1, 1, 3, 4, 1, 1, 2, 4, 3]
def baseStart_619799 : Nat := 118140960795 + 619799 * 2 ^ 59
def prefixEnd_619799 : Nat := 4983230072969 + 3 ^ 40 * 619799 * 2
def baseEnd_619799 : Nat := 282893152156556237566313

theorem tailTrace_619799 : CollatzResearch.WordTrace tailWord_619799 prefixEnd_619799 282893152156556237566313 := by
  unfold tailWord_619799
  simp only [CollatzResearch.WordTrace]
  refine ⟨22605926681581551086902451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15070617787721034057934967 22605926681581551086902451)
  ·
    refine ⟨33908890022372326630353677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22605926681581551086902451 33908890022372326630353677)
    ·
      refine ⟨12715833758389622486382629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33908890022372326630353677 12715833758389622486382629)
      ·
        refine ⟨2384218829698054216196743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12715833758389622486382629 2384218829698054216196743)
        ·
          refine ⟨3576328244547081324295115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2384218829698054216196743 3576328244547081324295115)
          ·
            refine ⟨5364492366820621986442673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3576328244547081324295115 5364492366820621986442673)
            ·
              refine ⟨4023369275115466489832005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5364492366820621986442673 4023369275115466489832005)
              ·
                refine ⟨754381739084149966843501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4023369275115466489832005 754381739084149966843501)
                ·
                  refine ⟨282893152156556237566313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 754381739084149966843501 282893152156556237566313)
                  ·
                    rfl

theorem cell20_619799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 2, 4, 3].length) (baseStart_619799 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_619799 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_619799 prefixEnd_619799 := by exact prefixLift 619799
  have htrace : WordTrace (prefixWord ++ tailWord_619799) baseStart_619799 baseEnd_619799 := by
    simpa [prefixWord, tailWord_619799, baseEnd_619799] using wordTrace_append hprefix tailTrace_619799
  have hstable : (prefixWord ++ tailWord_619799).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_619799).length < 2 ^ (prefixWord ++ tailWord_619799).sum := by decide
  have hdescent : baseEnd_619799 < baseStart_619799 := by decide
  rcases family_descends (prefixWord ++ tailWord_619799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_619813 : List Nat := [1, 3, 1, 2, 4, 1, 1, 7]
def baseStart_619813 : Nat := 118140960795 + 619813 * 2 ^ 59
def prefixEnd_619813 : Nat := 4983230072969 + 3 ^ 40 * 619813 * 2
def baseEnd_619813 : Nat := 94299847379344803699863

theorem tailTrace_619813 : CollatzResearch.WordTrace tailWord_619813 prefixEnd_619813 94299847379344803699863 := by
  unfold tailWord_619813
  simp only [CollatzResearch.WordTrace]
  refine ⟨22606437303530831477912093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15070958202353887651941395 22606437303530831477912093)
  ·
    refine ⟨8477413988824061804217035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22606437303530831477912093 8477413988824061804217035)
    ·
      refine ⟨12716120983236092706325553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8477413988824061804217035 12716120983236092706325553)
      ·
        refine ⟨9537090737427069529744165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12716120983236092706325553 9537090737427069529744165)
        ·
          refine ⟨1788204513267575536827031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9537090737427069529744165 1788204513267575536827031)
          ·
            refine ⟨2682306769901363305240547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1788204513267575536827031 2682306769901363305240547)
            ·
              refine ⟨4023460154852044957860821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2682306769901363305240547 4023460154852044957860821)
              ·
                refine ⟨94299847379344803699863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4023460154852044957860821 94299847379344803699863)
                ·
                  rfl

theorem cell20_619813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 1, 7].length) (baseStart_619813 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_619813 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_619813 prefixEnd_619813 := by exact prefixLift 619813
  have htrace : WordTrace (prefixWord ++ tailWord_619813) baseStart_619813 baseEnd_619813 := by
    simpa [prefixWord, tailWord_619813, baseEnd_619813] using wordTrace_append hprefix tailTrace_619813
  have hstable : (prefixWord ++ tailWord_619813).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_619813).length < 2 ^ (prefixWord ++ tailWord_619813).sum := by decide
  have hdescent : baseEnd_619813 < baseStart_619813 := by decide
  rcases family_descends (prefixWord ++ tailWord_619813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_619816 : List Nat := [2, 1, 5, 1, 2, 2, 1, 3, 3]
def baseStart_619816 : Nat := 118140960795 + 619816 * 2 ^ 59
def prefixEnd_619816 : Nat := 4983230072969 + 3 ^ 40 * 619816 * 2
def baseEnd_619816 : Nat := 282900911419779733999577

theorem tailTrace_619816 : CollatzResearch.WordTrace tailWord_619816 prefixEnd_619816 282900911419779733999577 := by
  unfold tailWord_619816
  simp only [CollatzResearch.WordTrace]
  refine ⟨11303273361259981495135651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15071031148346641993514201 11303273361259981495135651)
  ·
    refine ⟨16954910041889972242703477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11303273361259981495135651 16954910041889972242703477)
    ·
      refine ⟨1589522816427184897753451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 16954910041889972242703477 1589522816427184897753451)
      ·
        refine ⟨2384284224640777346630177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1589522816427184897753451 2384284224640777346630177)
        ·
          refine ⟨1788213168480583009972633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2384284224640777346630177 1788213168480583009972633)
          ·
            refine ⟨1341159876360437257479475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1788213168480583009972633 1341159876360437257479475)
            ·
              refine ⟨2011739814540655886219213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1341159876360437257479475 2011739814540655886219213)
              ·
                refine ⟨754402430452745957332205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2011739814540655886219213 754402430452745957332205)
                ·
                  refine ⟨282900911419779733999577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 754402430452745957332205 282900911419779733999577)
                  ·
                    rfl

theorem cell20_619816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 2, 1, 3, 3].length) (baseStart_619816 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_619816 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_619816 prefixEnd_619816 := by exact prefixLift 619816
  have htrace : WordTrace (prefixWord ++ tailWord_619816) baseStart_619816 baseEnd_619816 := by
    simpa [prefixWord, tailWord_619816, baseEnd_619816] using wordTrace_append hprefix tailTrace_619816
  have hstable : (prefixWord ++ tailWord_619816).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_619816).length < 2 ^ (prefixWord ++ tailWord_619816).sum := by decide
  have hdescent : baseEnd_619816 < baseStart_619816 := by decide
  rcases family_descends (prefixWord ++ tailWord_619816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_619853 : List Nat := [1, 6, 1, 3, 1, 2, 2, 2, 2]
def baseStart_619853 : Nat := 118140960795 + 619853 * 2 ^ 59
def prefixEnd_619853 : Nat := 4983230072969 + 3 ^ 40 * 619853 * 2
def baseEnd_619853 : Nat := 282917799227972049766093

theorem tailTrace_619853 : CollatzResearch.WordTrace tailWord_619853 prefixEnd_619853 282917799227972049766093 := by
  unfold tailWord_619853
  simp only [CollatzResearch.WordTrace]
  refine ⟨22607896223385918309368213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15071930815590612206245475 22607896223385918309368213)
  ·
    refine ⟨1059745135471214920751635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 22607896223385918309368213 1059745135471214920751635)
    ·
      refine ⟨1589617703206822381127453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1059745135471214920751635 1589617703206822381127453)
      ·
        refine ⟨596106638702558392922795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1589617703206822381127453 596106638702558392922795)
        ·
          refine ⟨894159958053837589384193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 596106638702558392922795 894159958053837589384193)
          ·
            refine ⟨670619968540378192038145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 894159958053837589384193 670619968540378192038145)
            ·
              refine ⟨502964976405283644028609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 670619968540378192038145 502964976405283644028609)
              ·
                refine ⟨377223732303962733021457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 502964976405283644028609 377223732303962733021457)
                ·
                  refine ⟨282917799227972049766093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 377223732303962733021457 282917799227972049766093)
                  ·
                    rfl

theorem cell20_619853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 2, 2, 2, 2].length) (baseStart_619853 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_619853 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_619853 prefixEnd_619853 := by exact prefixLift 619853
  have htrace : WordTrace (prefixWord ++ tailWord_619853) baseStart_619853 baseEnd_619853 := by
    simpa [prefixWord, tailWord_619853, baseEnd_619853] using wordTrace_append hprefix tailTrace_619853
  have hstable : (prefixWord ++ tailWord_619853).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_619853).length < 2 ^ (prefixWord ++ tailWord_619853).sum := by decide
  have hdescent : baseEnd_619853 < baseStart_619853 := by decide
  rcases family_descends (prefixWord ++ tailWord_619853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_619875 : List Nat := [1, 1, 1, 5, 2, 2, 2, 3, 3]
def baseStart_619875 : Nat := 118140960795 + 619875 * 2 ^ 59
def prefixEnd_619875 : Nat := 4983230072969 + 3 ^ 40 * 619875 * 2
def baseEnd_619875 : Nat := 282927840627437751032669

theorem tailTrace_619875 : CollatzResearch.WordTrace tailWord_619875 prefixEnd_619875 282927840627437751032669 := by
  unfold tailWord_619875
  simp only [CollatzResearch.WordTrace]
  refine ⟨22608698629306216066669079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15072465752870810711112719 22608698629306216066669079)
  ·
    refine ⟨33913047943959324100003619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22608698629306216066669079 33913047943959324100003619)
    ·
      refine ⟨50869571915938986150005429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33913047943959324100003619 50869571915938986150005429)
      ·
        refine ⟨4769022367119279951563009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 50869571915938986150005429 4769022367119279951563009)
        ·
          refine ⟨3576766775339459963672257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4769022367119279951563009 3576766775339459963672257)
          ·
            refine ⟨2682575081504594972754193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3576766775339459963672257 2682575081504594972754193)
            ·
              refine ⟨2011931311128446229565645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2682575081504594972754193 2011931311128446229565645)
              ·
                refine ⟨754474241673167336087117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2011931311128446229565645 754474241673167336087117)
                ·
                  refine ⟨282927840627437751032669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 754474241673167336087117 282927840627437751032669)
                  ·
                    rfl

theorem cell20_619875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 2, 3, 3].length) (baseStart_619875 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_619875 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_619875 prefixEnd_619875 := by exact prefixLift 619875
  have htrace : WordTrace (prefixWord ++ tailWord_619875) baseStart_619875 baseEnd_619875 := by
    simpa [prefixWord, tailWord_619875, baseEnd_619875] using wordTrace_append hprefix tailTrace_619875
  have hstable : (prefixWord ++ tailWord_619875).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_619875).length < 2 ^ (prefixWord ++ tailWord_619875).sum := by decide
  have hdescent : baseEnd_619875 < baseStart_619875 := by decide
  rcases family_descends (prefixWord ++ tailWord_619875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_619899 : List Nat := [1, 1, 1, 1, 1, 6, 4, 3, 2]
def baseStart_619899 : Nat := 118140960795 + 619899 * 2 ^ 59
def prefixEnd_619899 : Nat := 4983230072969 + 3 ^ 40 * 619899 * 2
def baseEnd_619899 : Nat := 282938794881400334232571

theorem tailTrace_619899 : CollatzResearch.WordTrace tailWord_619899 prefixEnd_619899 282938794881400334232571 := by
  unfold tailWord_619899
  simp only [CollatzResearch.WordTrace]
  refine ⟨22609573981219268165542751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15073049320812845443695167 22609573981219268165542751)
  ·
    refine ⟨33914360971828902248314127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22609573981219268165542751 33914360971828902248314127)
    ·
      refine ⟨50871541457743353372471191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33914360971828902248314127 50871541457743353372471191)
      ·
        refine ⟨76307312186615030058706787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50871541457743353372471191 76307312186615030058706787)
        ·
          refine ⟨114460968279922545088060181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76307312186615030058706787 114460968279922545088060181)
          ·
            refine ⟨5365357888121369301002821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 114460968279922545088060181 5365357888121369301002821)
            ·
              refine ⟨1006004604022756743938029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5365357888121369301002821 1006004604022756743938029)
              ·
                refine ⟨377251726508533778976761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1006004604022756743938029 377251726508533778976761)
                ·
                  refine ⟨282938794881400334232571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 377251726508533778976761 282938794881400334232571)
                  ·
                    rfl

theorem cell20_619899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 4, 3, 2].length) (baseStart_619899 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_619899 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_619899 prefixEnd_619899 := by exact prefixLift 619899
  have htrace : WordTrace (prefixWord ++ tailWord_619899) baseStart_619899 baseEnd_619899 := by
    simpa [prefixWord, tailWord_619899, baseEnd_619899] using wordTrace_append hprefix tailTrace_619899
  have hstable : (prefixWord ++ tailWord_619899).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_619899).length < 2 ^ (prefixWord ++ tailWord_619899).sum := by decide
  have hdescent : baseEnd_619899 < baseStart_619899 := by decide
  rcases family_descends (prefixWord ++ tailWord_619899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_619913 : List Nat := [1, 2, 1, 1, 7, 1, 1, 1, 5]
def baseStart_619913 : Nat := 118140960795 + 619913 * 2 ^ 59
def prefixEnd_619913 : Nat := 4983230072969 + 3 ^ 40 * 619913 * 2
def baseEnd_619913 : Nat := 282945184862878507765847

theorem tailTrace_619913 : CollatzResearch.WordTrace tailWord_619913 prefixEnd_619913 282945184862878507765847 := by
  unfold tailWord_619913
  simp only [CollatzResearch.WordTrace]
  refine ⟨22610084603168548556552393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15073389735445699037701595 22610084603168548556552393)
  ·
    refine ⟨16957563452376411417414295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22610084603168548556552393 16957563452376411417414295)
    ·
      refine ⟨25436345178564617126121443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16957563452376411417414295 25436345178564617126121443)
      ·
        refine ⟨38154517767846925689182165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25436345178564617126121443 38154517767846925689182165)
        ·
          refine ⟨894246510183912320840207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 38154517767846925689182165 894246510183912320840207)
          ·
            refine ⟨1341369765275868481260311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 894246510183912320840207 1341369765275868481260311)
            ·
              refine ⟨2012054647913802721890467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1341369765275868481260311 2012054647913802721890467)
              ·
                refine ⟨3018081971870704082835701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2012054647913802721890467 3018081971870704082835701)
                ·
                  refine ⟨282945184862878507765847, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3018081971870704082835701 282945184862878507765847)
                  ·
                    rfl

theorem cell20_619913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 1, 1, 1, 5].length) (baseStart_619913 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_619913 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_619913 prefixEnd_619913 := by exact prefixLift 619913
  have htrace : WordTrace (prefixWord ++ tailWord_619913) baseStart_619913 baseEnd_619913 := by
    simpa [prefixWord, tailWord_619913, baseEnd_619913] using wordTrace_append hprefix tailTrace_619913
  have hstable : (prefixWord ++ tailWord_619913).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_619913).length < 2 ^ (prefixWord ++ tailWord_619913).sum := by decide
  have hdescent : baseEnd_619913 < baseStart_619913 := by decide
  rcases family_descends (prefixWord ++ tailWord_619913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_619930 : List Nat := [3, 1, 1, 4, 1, 1, 5, 1, 3]
def baseStart_619930 : Nat := 118140960795 + 619930 * 2 ^ 59
def prefixEnd_619930 : Nat := 4983230072969 + 3 ^ 40 * 619930 * 2
def baseEnd_619930 : Nat := 282952944126102004199111

theorem tailTrace_619930 : CollatzResearch.WordTrace tailWord_619930 prefixEnd_619930 282952944126102004199111 := by
  unfold tailWord_619930
  simp only [CollatzResearch.WordTrace]
  refine ⟨5652676161026740114980311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15073803096071306973280829 5652676161026740114980311)
  ·
    refine ⟨8479014241540110172470467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5652676161026740114980311 8479014241540110172470467)
    ·
      refine ⟨12718521362310165258705701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8479014241540110172470467 12718521362310165258705701)
      ·
        refine ⟨2384722755433155986007319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12718521362310165258705701 2384722755433155986007319)
        ·
          refine ⟨3577084133149733979010979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2384722755433155986007319 3577084133149733979010979)
          ·
            refine ⟨5365626199724600968516469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3577084133149733979010979 5365626199724600968516469)
            ·
              refine ⟨503027456224181340798419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5365626199724600968516469 503027456224181340798419)
              ·
                refine ⟨754541184336272011197629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 503027456224181340798419 754541184336272011197629)
                ·
                  refine ⟨282952944126102004199111, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 754541184336272011197629 282952944126102004199111)
                  ·
                    rfl

theorem cell20_619930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 5, 1, 3].length) (baseStart_619930 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_619930 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_619930 prefixEnd_619930 := by exact prefixLift 619930
  have htrace : WordTrace (prefixWord ++ tailWord_619930) baseStart_619930 baseEnd_619930 := by
    simpa [prefixWord, tailWord_619930, baseEnd_619930] using wordTrace_append hprefix tailTrace_619930
  have hstable : (prefixWord ++ tailWord_619930).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_619930).length < 2 ^ (prefixWord ++ tailWord_619930).sum := by decide
  have hdescent : baseEnd_619930 < baseStart_619930 := by decide
  rcases family_descends (prefixWord ++ tailWord_619930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_619941 : List Nat := [1, 3, 1, 2, 1, 1, 2, 3, 6]
def baseStart_619941 : Nat := 118140960795 + 619941 * 2 ^ 59
def prefixEnd_619941 : Nat := 4983230072969 + 3 ^ 40 * 619941 * 2
def baseEnd_619941 : Nat := 282957964825834854832399

theorem tailTrace_619941 : CollatzResearch.WordTrace tailWord_619941 prefixEnd_619941 282957964825834854832399 := by
  unfold tailWord_619941
  simp only [CollatzResearch.WordTrace]
  refine ⟨22611105847067109338571677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15074070564711406225714451 22611105847067109338571677)
  ·
    refine ⟨8479164692650166001964379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22611105847067109338571677 8479164692650166001964379)
    ·
      refine ⟨12718747038975249002946569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8479164692650166001964379 12718747038975249002946569)
      ·
        refine ⟨9539060279231436752209927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12718747038975249002946569 9539060279231436752209927)
        ·
          refine ⟨14308590418847155128314891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9539060279231436752209927 14308590418847155128314891)
          ·
            refine ⟨21462885628270732692472337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14308590418847155128314891 21462885628270732692472337)
            ·
              refine ⟨16097164221203049519354253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21462885628270732692472337 16097164221203049519354253)
              ·
                refine ⟨6036436582951143569757845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16097164221203049519354253 6036436582951143569757845)
                ·
                  refine ⟨282957964825834854832399, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6036436582951143569757845 282957964825834854832399)
                  ·
                    rfl

theorem cell20_619941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 3, 6].length) (baseStart_619941 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_619941 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_619941 prefixEnd_619941 := by exact prefixLift 619941
  have htrace : WordTrace (prefixWord ++ tailWord_619941) baseStart_619941 baseEnd_619941 := by
    simpa [prefixWord, tailWord_619941, baseEnd_619941] using wordTrace_append hprefix tailTrace_619941
  have hstable : (prefixWord ++ tailWord_619941).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_619941).length < 2 ^ (prefixWord ++ tailWord_619941).sum := by decide
  have hdescent : baseEnd_619941 < baseStart_619941 := by decide
  rcases family_descends (prefixWord ++ tailWord_619941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_619989 : List Nat := [1, 3, 2, 3, 1, 1, 3, 3, 3]
def baseStart_619989 : Nat := 118140960795 + 619989 * 2 ^ 59
def prefixEnd_619989 : Nat := 4983230072969 + 3 ^ 40 * 619989 * 2
def baseEnd_619989 : Nat := 282979873333760021232203

theorem tailTrace_619989 : CollatzResearch.WordTrace tailWord_619989 prefixEnd_619989 282979873333760021232203 := by
  unfold tailWord_619989
  simp only [CollatzResearch.WordTrace]
  refine ⟨22612856550893213536319021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15075237700595475690879347 22612856550893213536319021)
  ·
    refine ⟨8479821206584955076119633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22612856550893213536319021 8479821206584955076119633)
    ·
      refine ⟨6359865904938716307089725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8479821206584955076119633 6359865904938716307089725)
      ·
        refine ⟨2384949714352018615158647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6359865904938716307089725 2384949714352018615158647)
        ·
          refine ⟨3577424571528027922737971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2384949714352018615158647 3577424571528027922737971)
          ·
            refine ⟨5366136857292041884106957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3577424571528027922737971 5366136857292041884106957)
            ·
              refine ⟨2012301321484515706540109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5366136857292041884106957 2012301321484515706540109)
              ·
                refine ⟨754612995556693389952541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2012301321484515706540109 754612995556693389952541)
                ·
                  refine ⟨282979873333760021232203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 754612995556693389952541 282979873333760021232203)
                  ·
                    rfl

theorem cell20_619989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 3, 3, 3].length) (baseStart_619989 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_619989 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_619989 prefixEnd_619989 := by exact prefixLift 619989
  have htrace : WordTrace (prefixWord ++ tailWord_619989) baseStart_619989 baseEnd_619989 := by
    simpa [prefixWord, tailWord_619989, baseEnd_619989] using wordTrace_append hprefix tailTrace_619989
  have hstable : (prefixWord ++ tailWord_619989).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_619989).length < 2 ^ (prefixWord ++ tailWord_619989).sum := by decide
  have hdescent : baseEnd_619989 < baseStart_619989 := by decide
  rcases family_descends (prefixWord ++ tailWord_619989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_620003 : List Nat := [1, 1, 1, 6, 2, 1, 2, 6]
def baseStart_620003 : Nat := 118140960795 + 620003 * 2 ^ 59
def prefixEnd_620003 : Nat := 4983230072969 + 3 ^ 40 * 620003 * 2
def baseEnd_620003 : Nat := 94328754438412731588493

theorem tailTrace_620003 : CollatzResearch.WordTrace tailWord_620003 prefixEnd_620003 94328754438412731588493 := by
  unfold tailWord_620003
  simp only [CollatzResearch.WordTrace]
  refine ⟨22613367172842493927328663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15075578115228329284885775 22613367172842493927328663)
  ·
    refine ⟨33920050759263740890992995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22613367172842493927328663 33920050759263740890992995)
    ·
      refine ⟨50880076138895611336489493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33920050759263740890992995 50880076138895611336489493)
      ·
        refine ⟨2385003569010731781397945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 50880076138895611336489493 2385003569010731781397945)
        ·
          refine ⟨1788752676758048836048459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2385003569010731781397945 1788752676758048836048459)
          ·
            refine ⟨2683129015137073254072689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1788752676758048836048459 2683129015137073254072689)
            ·
              refine ⟨2012346761352804940554517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2683129015137073254072689 2012346761352804940554517)
              ·
                refine ⟨94328754438412731588493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2012346761352804940554517 94328754438412731588493)
                ·
                  rfl

theorem cell20_620003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 2, 6].length) (baseStart_620003 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_620003 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_620003 prefixEnd_620003 := by exact prefixLift 620003
  have htrace : WordTrace (prefixWord ++ tailWord_620003) baseStart_620003 baseEnd_620003 := by
    simpa [prefixWord, tailWord_620003, baseEnd_620003] using wordTrace_append hprefix tailTrace_620003
  have hstable : (prefixWord ++ tailWord_620003).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_620003).length < 2 ^ (prefixWord ++ tailWord_620003).sum := by decide
  have hdescent : baseEnd_620003 < baseStart_620003 := by decide
  rcases family_descends (prefixWord ++ tailWord_620003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan20Incremental
