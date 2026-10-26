import V185TrunkScan22Chunk269

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_2407472 : List Nat := [2, 1, 1, 1, 2, 4, 2, 1, 3, 5]
def baseStart_2407472 : Nat := 118140960795 + 2407472 * 2 ^ 59
def prefixEnd_2407472 : Nat := 4983230072969 + 3 ^ 40 * 2407472 * 2
def baseEnd_2407472 : Nat := 824126865494073325618829

theorem tailTrace_2407472 : CollatzResearch.WordTrace tailWord_2407472 prefixEnd_2407472 824126865494073325618829 := by
  unfold tailWord_2407472
  simp only [CollatzResearch.WordTrace]
  refine ⟨43903858767073791164156335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58538478356098388218875113 43903858767073791164156335)
  ·
    refine ⟨65855788150610686746234503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43903858767073791164156335 65855788150610686746234503)
    ·
      refine ⟨98783682225916030119351755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65855788150610686746234503 98783682225916030119351755)
      ·
        refine ⟨148175523338874045179027633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98783682225916030119351755 148175523338874045179027633)
        ·
          refine ⟨111131642504155533884270725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 148175523338874045179027633 111131642504155533884270725)
          ·
            refine ⟨20837182969529162603300761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 111131642504155533884270725 20837182969529162603300761)
            ·
              refine ⟨15627887227146871952475571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20837182969529162603300761 15627887227146871952475571)
              ·
                refine ⟨23441830840720307928713357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15627887227146871952475571 23441830840720307928713357)
                ·
                  refine ⟨8790686565270115473267509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23441830840720307928713357 8790686565270115473267509)
                  ·
                    refine ⟨824126865494073325618829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8790686565270115473267509 824126865494073325618829)
                    ·
                      rfl

theorem cell22_2407472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 2, 1, 3, 5].length) (baseStart_2407472 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2407472 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2407472 prefixEnd_2407472 := by exact prefixLift 2407472
  have htrace : WordTrace (prefixWord ++ tailWord_2407472) baseStart_2407472 baseEnd_2407472 := by
    simpa [prefixWord, tailWord_2407472, baseEnd_2407472] using wordTrace_append hprefix tailTrace_2407472
  have hstable : (prefixWord ++ tailWord_2407472).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2407472).length < 2 ^ (prefixWord ++ tailWord_2407472).sum := by decide
  have hdescent : baseEnd_2407472 < baseStart_2407472 := by decide
  rcases family_descends (prefixWord ++ tailWord_2407472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2407491 : List Nat := [1, 1, 1, 3, 1, 2, 7, 2, 4]
def baseStart_2407491 : Nat := 118140960795 + 2407491 * 2 ^ 59
def prefixEnd_2407491 : Nat := 4983230072969 + 3 ^ 40 * 2407491 * 2
def baseEnd_2407491 : Nat := 274711123194121203131257

theorem tailTrace_2407491 : CollatzResearch.WordTrace tailWord_2407491 prefixEnd_2407491 274711123194121203131257 := by
  unfold tailWord_2407491
  simp only [CollatzResearch.WordTrace]
  refine ⟨87808410521078748573254327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58538940347385832382169551 87808410521078748573254327)
  ·
    refine ⟨131712615781618122859881491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87808410521078748573254327 131712615781618122859881491)
    ·
      refine ⟨197568923672427184289822237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131712615781618122859881491 197568923672427184289822237)
      ·
        refine ⟨74088346377160194108683339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 197568923672427184289822237 74088346377160194108683339)
        ·
          refine ⟨111132519565740291163025009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74088346377160194108683339 111132519565740291163025009)
          ·
            refine ⟨83349389674305218372268757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 111132519565740291163025009 83349389674305218372268757)
            ·
              refine ⟨1953501320491528555600049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 83349389674305218372268757 1953501320491528555600049)
              ·
                refine ⟨1465125990368646416700037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1953501320491528555600049 1465125990368646416700037)
                ·
                  refine ⟨274711123194121203131257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1465125990368646416700037 274711123194121203131257)
                  ·
                    rfl

theorem cell22_2407491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 7, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 7, 2, 4].length) (baseStart_2407491 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2407491 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2407491 prefixEnd_2407491 := by exact prefixLift 2407491
  have htrace : WordTrace (prefixWord ++ tailWord_2407491) baseStart_2407491 baseEnd_2407491 := by
    simpa [prefixWord, tailWord_2407491, baseEnd_2407491] using wordTrace_append hprefix tailTrace_2407491
  have hstable : (prefixWord ++ tailWord_2407491).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2407491).length < 2 ^ (prefixWord ++ tailWord_2407491).sum := by decide
  have hdescent : baseEnd_2407491 < baseStart_2407491 := by decide
  rcases family_descends (prefixWord ++ tailWord_2407491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2407547 : List Nat := [1, 1, 1, 1, 1, 4, 1, 5, 7]
def baseStart_2407547 : Nat := 118140960795 + 2407547 * 2 ^ 59
def prefixEnd_2407547 : Nat := 4983230072969 + 3 ^ 40 * 2407547 * 2
def baseEnd_2407547 : Nat := 274717513175599376664533

theorem tailTrace_2407547 : CollatzResearch.WordTrace tailWord_2407547 prefixEnd_2407547 274717513175599376664533 := by
  unfold tailWord_2407547
  simp only [CollatzResearch.WordTrace]
  refine ⟨87810453008875870137292895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58540302005917246758195263 87810453008875870137292895)
  ·
    refine ⟨131715679513313805205939343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87810453008875870137292895 131715679513313805205939343)
    ·
      refine ⟨197573519269970707808909015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131715679513313805205939343 197573519269970707808909015)
      ·
        refine ⟨296360278904956061713363523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 197573519269970707808909015 296360278904956061713363523)
        ·
          refine ⟨444540418357434092570045285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 296360278904956061713363523 444540418357434092570045285)
          ·
            refine ⟨83351328442018892356883491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 444540418357434092570045285 83351328442018892356883491)
            ·
              refine ⟨125026992663028338535325237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 83351328442018892356883491 125026992663028338535325237)
              ·
                refine ⟨11721280562158906737686741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 125026992663028338535325237 11721280562158906737686741)
                ·
                  refine ⟨274717513175599376664533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11721280562158906737686741 274717513175599376664533)
                  ·
                    rfl

theorem cell22_2407547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 5, 7].length) (baseStart_2407547 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2407547 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2407547 prefixEnd_2407547 := by exact prefixLift 2407547
  have htrace : WordTrace (prefixWord ++ tailWord_2407547) baseStart_2407547 baseEnd_2407547 := by
    simpa [prefixWord, tailWord_2407547, baseEnd_2407547] using wordTrace_append hprefix tailTrace_2407547
  have hstable : (prefixWord ++ tailWord_2407547).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2407547).length < 2 ^ (prefixWord ++ tailWord_2407547).sum := by decide
  have hdescent : baseEnd_2407547 < baseStart_2407547 := by decide
  rcases family_descends (prefixWord ++ tailWord_2407547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2407609 : List Nat := [1, 2, 1, 4, 1, 3, 1, 3, 6]
def baseStart_2407609 : Nat := 118140960795 + 2407609 * 2 ^ 59
def prefixEnd_2407609 : Nat := 4983230072969 + 3 ^ 40 * 2407609 * 2
def baseEnd_2407609 : Nat := 274724587797950211647803

theorem tailTrace_2407609 : CollatzResearch.WordTrace tailWord_2407609 prefixEnd_2407609 274724587797950211647803 := by
  unfold tailWord_2407609
  simp only [CollatzResearch.WordTrace]
  refine ⟨87812714334651254726049881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58541809556434169817366587 87812714334651254726049881)
  ·
    refine ⟨65859535750988441044537411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87812714334651254726049881 65859535750988441044537411)
    ·
      refine ⟨98789303626482661566806117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65859535750988441044537411 98789303626482661566806117)
      ·
        refine ⟨18522994429965499043776147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 98789303626482661566806117 18522994429965499043776147)
        ·
          refine ⟨27784491644948248565664221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18522994429965499043776147 27784491644948248565664221)
          ·
            refine ⟨10419184366855593212124083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27784491644948248565664221 10419184366855593212124083)
            ·
              refine ⟨15628776550283389818186125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10419184366855593212124083 15628776550283389818186125)
              ·
                refine ⟨5860791206356271181819797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15628776550283389818186125 5860791206356271181819797)
                ·
                  refine ⟨274724587797950211647803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5860791206356271181819797 274724587797950211647803)
                  ·
                    rfl

theorem cell22_2407609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 1, 3, 6].length) (baseStart_2407609 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2407609 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2407609 prefixEnd_2407609 := by exact prefixLift 2407609
  have htrace : WordTrace (prefixWord ++ tailWord_2407609) baseStart_2407609 baseEnd_2407609 := by
    simpa [prefixWord, tailWord_2407609, baseEnd_2407609] using wordTrace_append hprefix tailTrace_2407609
  have hstable : (prefixWord ++ tailWord_2407609).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2407609).length < 2 ^ (prefixWord ++ tailWord_2407609).sum := by decide
  have hdescent : baseEnd_2407609 < baseStart_2407609 := by decide
  rcases family_descends (prefixWord ++ tailWord_2407609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2407639 : List Nat := [1, 1, 3, 2, 1, 2, 4, 1, 1, 6]
def baseStart_2407639 : Nat := 118140960795 + 2407639 * 2 ^ 59
def prefixEnd_2407639 : Nat := 4983230072969 + 3 ^ 40 * 2407639 * 2
def baseEnd_2407639 : Nat := 824184033006940556693317

theorem tailTrace_2407639 : CollatzResearch.WordTrace tailWord_2407639 prefixEnd_2407639 824184033006940556693317 := by
  unfold tailWord_2407639
  simp only [CollatzResearch.WordTrace]
  refine ⟨87813808524542569849641971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58542539016361713233094647 87813808524542569849641971)
  ·
    refine ⟨131720712786813854774462957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87813808524542569849641971 131720712786813854774462957)
    ·
      refine ⟨49395267295055195540423609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 131720712786813854774462957 49395267295055195540423609)
      ·
        refine ⟨37046450471291396655317707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49395267295055195540423609 37046450471291396655317707)
        ·
          refine ⟨55569675706937094982976561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37046450471291396655317707 55569675706937094982976561)
          ·
            refine ⟨41677256780202821237232421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55569675706937094982976561 41677256780202821237232421)
            ·
              refine ⟨7814485646288028981981079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 41677256780202821237232421 7814485646288028981981079)
              ·
                refine ⟨11721728469432043472971619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7814485646288028981981079 11721728469432043472971619)
                ·
                  refine ⟨17582592704148065209457429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11721728469432043472971619 17582592704148065209457429)
                  ·
                    refine ⟨824184033006940556693317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17582592704148065209457429 824184033006940556693317)
                    ·
                      rfl

theorem cell22_2407639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 4, 1, 1, 6].length) (baseStart_2407639 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2407639 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2407639 prefixEnd_2407639 := by exact prefixLift 2407639
  have htrace : WordTrace (prefixWord ++ tailWord_2407639) baseStart_2407639 baseEnd_2407639 := by
    simpa [prefixWord, tailWord_2407639, baseEnd_2407639] using wordTrace_append hprefix tailTrace_2407639
  have hstable : (prefixWord ++ tailWord_2407639).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2407639).length < 2 ^ (prefixWord ++ tailWord_2407639).sum := by decide
  have hdescent : baseEnd_2407639 < baseStart_2407639 := by decide
  rcases family_descends (prefixWord ++ tailWord_2407639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2407656 : List Nat := [2, 1, 4, 1, 2, 1, 3, 2, 2, 4]
def baseStart_2407656 : Nat := 118140960795 + 2407656 * 2 ^ 59
def prefixEnd_2407656 : Nat := 4983230072969 + 3 ^ 40 * 2407656 * 2
def baseEnd_2407656 : Nat := 824189852454358179018265

theorem tailTrace_2407656 : CollatzResearch.WordTrace tailWord_2407656 prefixEnd_2407656 824189852454358179018265 := by
  unfold tailWord_2407656
  simp only [CollatzResearch.WordTrace]
  refine ⟨43907214282740490876505411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58542952376987321168673881 43907214282740490876505411)
  ·
    refine ⟨65860821424110736314758117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43907214282740490876505411 65860821424110736314758117)
    ·
      refine ⟨12348904017020763059017147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 65860821424110736314758117 12348904017020763059017147)
      ·
        refine ⟨18523356025531144588525721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12348904017020763059017147 18523356025531144588525721)
        ·
          refine ⟨13892517019148358441394291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18523356025531144588525721 13892517019148358441394291)
          ·
            refine ⟨20838775528722537662091437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13892517019148358441394291 20838775528722537662091437)
            ·
              refine ⟨7814540823270951623284289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20838775528722537662091437 7814540823270951623284289)
              ·
                refine ⟨5860905617453213717463217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7814540823270951623284289 5860905617453213717463217)
                ·
                  refine ⟨4395679213089910288097413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5860905617453213717463217 4395679213089910288097413)
                  ·
                    refine ⟨824189852454358179018265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4395679213089910288097413 824189852454358179018265)
                    ·
                      rfl

theorem cell22_2407656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 3, 2, 2, 4].length) (baseStart_2407656 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2407656 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2407656 prefixEnd_2407656 := by exact prefixLift 2407656
  have htrace : WordTrace (prefixWord ++ tailWord_2407656) baseStart_2407656 baseEnd_2407656 := by
    simpa [prefixWord, tailWord_2407656, baseEnd_2407656] using wordTrace_append hprefix tailTrace_2407656
  have hstable : (prefixWord ++ tailWord_2407656).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2407656).length < 2 ^ (prefixWord ++ tailWord_2407656).sum := by decide
  have hdescent : baseEnd_2407656 < baseStart_2407656 := by decide
  rcases family_descends (prefixWord ++ tailWord_2407656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2407731 : List Nat := [1, 1, 1, 2, 5, 3, 1, 1, 2, 5]
def baseStart_2407731 : Nat := 118140960795 + 2407731 * 2 ^ 59
def prefixEnd_2407731 : Nat := 4983230072969 + 3 ^ 40 * 2407731 * 2
def baseEnd_2407731 : Nat := 824215526487082983393035

theorem tailTrace_2407731 : CollatzResearch.WordTrace tailWord_2407731 prefixEnd_2407731 824215526487082983393035 := by
  unfold tailWord_2407731
  simp only [CollatzResearch.WordTrace]
  refine ⟨87817164040209269561991047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58544776026806179707994031 87817164040209269561991047)
  ·
    refine ⟨131725746060313904342986571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87817164040209269561991047 131725746060313904342986571)
    ·
      refine ⟨197588619090470856514479857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131725746060313904342986571 197588619090470856514479857)
      ·
        refine ⟨148191464317853142385859893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 197588619090470856514479857 148191464317853142385859893)
        ·
          refine ⟨13892949779798732098674365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 148191464317853142385859893 13892949779798732098674365)
          ·
            refine ⟨5209856167424524537002887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13892949779798732098674365 5209856167424524537002887)
            ·
              refine ⟨7814784251136786805504331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5209856167424524537002887 7814784251136786805504331)
              ·
                refine ⟨11722176376705180208256497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7814784251136786805504331 11722176376705180208256497)
                ·
                  refine ⟨8791632282528885156192373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11722176376705180208256497 8791632282528885156192373)
                  ·
                    refine ⟨824215526487082983393035, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8791632282528885156192373 824215526487082983393035)
                    ·
                      rfl

theorem cell22_2407731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 3, 1, 1, 2, 5].length) (baseStart_2407731 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2407731 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2407731 prefixEnd_2407731 := by exact prefixLift 2407731
  have htrace : WordTrace (prefixWord ++ tailWord_2407731) baseStart_2407731 baseEnd_2407731 := by
    simpa [prefixWord, tailWord_2407731, baseEnd_2407731] using wordTrace_append hprefix tailTrace_2407731
  have hstable : (prefixWord ++ tailWord_2407731).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2407731).length < 2 ^ (prefixWord ++ tailWord_2407731).sum := by decide
  have hdescent : baseEnd_2407731 < baseStart_2407731 := by decide
  rcases family_descends (prefixWord ++ tailWord_2407731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2407759 : List Nat := [1, 1, 2, 1, 1, 2, 1, 2, 2, 9]
def baseStart_2407759 : Nat := 118140960795 + 2407759 * 2 ^ 59
def prefixEnd_2407759 : Nat := 4983230072969 + 3 ^ 40 * 2407759 * 2
def baseEnd_2407759 : Nat := 824225111459300243692949

theorem tailTrace_2407759 : CollatzResearch.WordTrace tailWord_2407759 prefixEnd_2407759 824225111459300243692949 := by
  unfold tailWord_2407759
  simp only [CollatzResearch.WordTrace]
  refine ⟨87818185284107830344010331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58545456856071886896006887 87818185284107830344010331)
  ·
    refine ⟨131727277926161745516015497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87818185284107830344010331 131727277926161745516015497)
    ·
      refine ⟨98795458444621309137011623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 131727277926161745516015497 98795458444621309137011623)
      ·
        refine ⟨148193187666931963705517435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98795458444621309137011623 148193187666931963705517435)
        ·
          refine ⟨222289781500397945558276153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 148193187666931963705517435 222289781500397945558276153)
          ·
            refine ⟨166717336125298459168707115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 222289781500397945558276153 166717336125298459168707115)
            ·
              refine ⟨250076004187947688753060673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 166717336125298459168707115 250076004187947688753060673)
              ·
                refine ⟨187557003140960766564795505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 250076004187947688753060673 187557003140960766564795505)
                ·
                  refine ⟨140667752355720574923596629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 187557003140960766564795505 140667752355720574923596629)
                  ·
                    refine ⟨824225111459300243692949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 140667752355720574923596629 824225111459300243692949)
                    ·
                      rfl

theorem cell22_2407759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 2, 2, 9].length) (baseStart_2407759 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2407759 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2407759 prefixEnd_2407759 := by exact prefixLift 2407759
  have htrace : WordTrace (prefixWord ++ tailWord_2407759) baseStart_2407759 baseEnd_2407759 := by
    simpa [prefixWord, tailWord_2407759, baseEnd_2407759] using wordTrace_append hprefix tailTrace_2407759
  have hstable : (prefixWord ++ tailWord_2407759).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2407759).length < 2 ^ (prefixWord ++ tailWord_2407759).sum := by decide
  have hdescent : baseEnd_2407759 < baseStart_2407759 := by decide
  rcases family_descends (prefixWord ++ tailWord_2407759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2407778 : List Nat := [3, 3, 2, 1, 1, 1, 4, 1, 6]
def baseStart_2407778 : Nat := 118140960795 + 2407778 * 2 ^ 59
def prefixEnd_2407778 : Nat := 4983230072969 + 3 ^ 40 * 2407778 * 2
def baseEnd_2407778 : Nat := 274743871849196842489297

theorem tailTrace_2407778 : CollatzResearch.WordTrace tailWord_2407778 prefixEnd_2407778 274743871849196842489297 := by
  unfold tailWord_2407778
  simp only [CollatzResearch.WordTrace]
  refine ⟨21954719567759749147237997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58545918847359331059301325 21954719567759749147237997)
  ·
    refine ⟨8233019837909905930214249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21954719567759749147237997 8233019837909905930214249)
    ·
      refine ⟨6174764878432429447660687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8233019837909905930214249 6174764878432429447660687)
      ·
        refine ⟨9262147317648644171491031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6174764878432429447660687 9262147317648644171491031)
        ·
          refine ⟨13893220976472966257236547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9262147317648644171491031 13893220976472966257236547)
          ·
            refine ⟨20839831464709449385854821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13893220976472966257236547 20839831464709449385854821)
            ·
              refine ⟨3907468399633021759847779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20839831464709449385854821 3907468399633021759847779)
              ·
                refine ⟨5861202599449532639771669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3907468399633021759847779 5861202599449532639771669)
                ·
                  refine ⟨274743871849196842489297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5861202599449532639771669 274743871849196842489297)
                  ·
                    rfl

theorem cell22_2407778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 4, 1, 6].length) (baseStart_2407778 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2407778 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2407778 prefixEnd_2407778 := by exact prefixLift 2407778
  have htrace : WordTrace (prefixWord ++ tailWord_2407778) baseStart_2407778 baseEnd_2407778 := by
    simpa [prefixWord, tailWord_2407778, baseEnd_2407778] using wordTrace_append hprefix tailTrace_2407778
  have hstable : (prefixWord ++ tailWord_2407778).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2407778).length < 2 ^ (prefixWord ++ tailWord_2407778).sum := by decide
  have hdescent : baseEnd_2407778 < baseStart_2407778 := by decide
  rcases family_descends (prefixWord ++ tailWord_2407778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2407793 : List Nat := [1, 2, 2, 2, 1, 2, 2, 5, 2, 3]
def baseStart_2407793 : Nat := 118140960795 + 2407793 * 2 ^ 59
def prefixEnd_2407793 : Nat := 4983230072969 + 3 ^ 40 * 2407793 * 2
def baseEnd_2407793 : Nat := 824236750354135488342845

theorem tailTrace_2407793 : CollatzResearch.WordTrace tailWord_2407793 prefixEnd_2407793 824236750354135488342845 := by
  unfold tailWord_2407793
  simp only [CollatzResearch.WordTrace]
  refine ⟨87819425365984654150748033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58546283577323102767165355 87819425365984654150748033)
  ·
    refine ⟨65864569024488490613061025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87819425365984654150748033 65864569024488490613061025)
    ·
      refine ⟨49398426768366367959795769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65864569024488490613061025 49398426768366367959795769)
      ·
        refine ⟨37048820076274775969846827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49398426768366367959795769 37048820076274775969846827)
        ·
          refine ⟨55573230114412163954770241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37048820076274775969846827 55573230114412163954770241)
          ·
            refine ⟨41679922585809122966077681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55573230114412163954770241 41679922585809122966077681)
            ·
              refine ⟨31259941939356842224558261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41679922585809122966077681 31259941939356842224558261)
              ·
                refine ⟨2930619556814703958552337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 31259941939356842224558261 2930619556814703958552337)
                ·
                  refine ⟨2197964667611027968914253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2930619556814703958552337 2197964667611027968914253)
                  ·
                    refine ⟨824236750354135488342845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2197964667611027968914253 824236750354135488342845)
                    ·
                      rfl

theorem cell22_2407793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 2, 5, 2, 3].length) (baseStart_2407793 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2407793 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2407793 prefixEnd_2407793 := by exact prefixLift 2407793
  have htrace : WordTrace (prefixWord ++ tailWord_2407793) baseStart_2407793 baseEnd_2407793 := by
    simpa [prefixWord, tailWord_2407793, baseEnd_2407793] using wordTrace_append hprefix tailTrace_2407793
  have hstable : (prefixWord ++ tailWord_2407793).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2407793).length < 2 ^ (prefixWord ++ tailWord_2407793).sum := by decide
  have hdescent : baseEnd_2407793 < baseStart_2407793 := by decide
  rcases family_descends (prefixWord ++ tailWord_2407793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2407866 : List Nat := [3, 1, 1, 1, 2, 1, 1, 1, 6, 5]
def baseStart_2407866 : Nat := 118140960795 + 2407866 * 2 ^ 59
def prefixEnd_2407866 : Nat := 4983230072969 + 3 ^ 40 * 2407866 * 2
def baseEnd_2407866 : Nat := 824261739745987631267621

theorem tailTrace_2407866 : CollatzResearch.WordTrace tailWord_2407866 prefixEnd_2407866 824261739745987631267621 := by
  unfold tailWord_2407866
  simp only [CollatzResearch.WordTrace]
  refine ⟨21955521973680046904538863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58548058596480125078770301 21955521973680046904538863)
  ·
    refine ⟨32933282960520070356808295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21955521973680046904538863 32933282960520070356808295)
    ·
      refine ⟨49399924440780105535212443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32933282960520070356808295 49399924440780105535212443)
      ·
        refine ⟨74099886661170158302818665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49399924440780105535212443 74099886661170158302818665)
        ·
          refine ⟨55574914995877618727113999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 74099886661170158302818665 55574914995877618727113999)
          ·
            refine ⟨83362372493816428090670999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55574914995877618727113999 83362372493816428090670999)
            ·
              refine ⟨125043558740724642136006499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 83362372493816428090670999 125043558740724642136006499)
              ·
                refine ⟨187565338111086963204009749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 125043558740724642136006499 187565338111086963204009749)
                ·
                  refine ⟨8792125223957201400187957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 187565338111086963204009749 8792125223957201400187957)
                  ·
                    refine ⟨824261739745987631267621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8792125223957201400187957 824261739745987631267621)
                    ·
                      rfl

theorem cell22_2407866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 1, 6, 5].length) (baseStart_2407866 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2407866 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2407866 prefixEnd_2407866 := by exact prefixLift 2407866
  have htrace : WordTrace (prefixWord ++ tailWord_2407866) baseStart_2407866 baseEnd_2407866 := by
    simpa [prefixWord, tailWord_2407866, baseEnd_2407866] using wordTrace_append hprefix tailTrace_2407866
  have hstable : (prefixWord ++ tailWord_2407866).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2407866).length < 2 ^ (prefixWord ++ tailWord_2407866).sum := by decide
  have hdescent : baseEnd_2407866 < baseStart_2407866 := by decide
  rcases family_descends (prefixWord ++ tailWord_2407866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2407874 : List Nat := [3, 5, 2, 1, 2, 9]
def baseStart_2407874 : Nat := 118140960795 + 2407874 * 2 ^ 59
def prefixEnd_2407874 : Nat := 4983230072969 + 3 ^ 40 * 2407874 * 2
def baseEnd_2407874 : Nat := 10176104670487386136637

theorem tailTrace_2407874 : CollatzResearch.WordTrace tailWord_2407874 prefixEnd_2407874 10176104670487386136637 := by
  unfold tailWord_2407874
  simp only [CollatzResearch.WordTrace]
  refine ⟨21955594919672801246111669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58548253119127469989631117 21955594919672801246111669)
  ·
    refine ⟨2058337023719325116822969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 21955594919672801246111669 2058337023719325116822969)
    ·
      refine ⟨1543752767789493837617227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2058337023719325116822969 1543752767789493837617227)
      ·
        refine ⟨2315629151684240756425841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1543752767789493837617227 2315629151684240756425841)
        ·
          refine ⟨1736721863763180567319381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2315629151684240756425841 1736721863763180567319381)
          ·
            refine ⟨10176104670487386136637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1736721863763180567319381 10176104670487386136637)
            ·
              rfl

theorem cell22_2407874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 2, 9].length) (baseStart_2407874 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2407874 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2407874 prefixEnd_2407874 := by exact prefixLift 2407874
  have htrace : WordTrace (prefixWord ++ tailWord_2407874) baseStart_2407874 baseEnd_2407874 := by
    simpa [prefixWord, tailWord_2407874, baseEnd_2407874] using wordTrace_append hprefix tailTrace_2407874
  have hstable : (prefixWord ++ tailWord_2407874).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2407874).length < 2 ^ (prefixWord ++ tailWord_2407874).sum := by decide
  have hdescent : baseEnd_2407874 < baseStart_2407874 := by decide
  rcases family_descends (prefixWord ++ tailWord_2407874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2407898 : List Nat := [3, 1, 1, 2, 3, 2, 1, 2, 3, 4]
def baseStart_2407898 : Nat := 118140960795 + 2407898 * 2 ^ 59
def prefixEnd_2407898 : Nat := 4983230072969 + 3 ^ 40 * 2407898 * 2
def baseEnd_2407898 : Nat := 824272693999950214467523

theorem tailTrace_2407898 : CollatzResearch.WordTrace tailWord_2407898 prefixEnd_2407898 824272693999950214467523 := by
  unfold tailWord_2407898
  simp only [CollatzResearch.WordTrace]
  refine ⟨21955813757651064270830087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58548836687069504722213565 21955813757651064270830087)
  ·
    refine ⟨32933720636476596406245131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21955813757651064270830087 32933720636476596406245131)
    ·
      refine ⟨49400580954714894609367697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32933720636476596406245131 49400580954714894609367697)
      ·
        refine ⟨37050435716036170957025773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49400580954714894609367697 37050435716036170957025773)
        ·
          refine ⟨13893913393513564108884665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37050435716036170957025773 13893913393513564108884665)
          ·
            refine ⟨10420435045135173081663499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13893913393513564108884665 10420435045135173081663499)
            ·
              refine ⟨15630652567702759622495249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10420435045135173081663499 15630652567702759622495249)
              ·
                refine ⟨11722989425777069716871437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15630652567702759622495249 11722989425777069716871437)
                ·
                  refine ⟨4396121034666401143826789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11722989425777069716871437 4396121034666401143826789)
                  ·
                    refine ⟨824272693999950214467523, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4396121034666401143826789 824272693999950214467523)
                    ·
                      rfl

theorem cell22_2407898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 1, 2, 3, 4].length) (baseStart_2407898 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2407898 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2407898 prefixEnd_2407898 := by exact prefixLift 2407898
  have htrace : WordTrace (prefixWord ++ tailWord_2407898) baseStart_2407898 baseEnd_2407898 := by
    simpa [prefixWord, tailWord_2407898, baseEnd_2407898] using wordTrace_append hprefix tailTrace_2407898
  have hstable : (prefixWord ++ tailWord_2407898).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2407898).length < 2 ^ (prefixWord ++ tailWord_2407898).sum := by decide
  have hdescent : baseEnd_2407898 < baseStart_2407898 := by decide
  rcases family_descends (prefixWord ++ tailWord_2407898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2407928 : List Nat := [2, 1, 2, 1, 1, 5, 2, 2, 1, 5]
def baseStart_2407928 : Nat := 118140960795 + 2407928 * 2 ^ 59
def prefixEnd_2407928 : Nat := 4983230072969 + 3 ^ 40 * 2407928 * 2
def baseEnd_2407928 : Nat := 824282963613040136217431

theorem tailTrace_2407928 : CollatzResearch.WordTrace tailWord_2407928 prefixEnd_2407928 824282963613040136217431 := by
  unfold tailWord_2407928
  simp only [CollatzResearch.WordTrace]
  refine ⟨43912174610247786103456219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58549566146997048137941625 43912174610247786103456219)
  ·
    refine ⟨65868261915371679155184329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43912174610247786103456219 65868261915371679155184329)
    ·
      refine ⟨49401196436528759366388247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65868261915371679155184329 49401196436528759366388247)
      ·
        refine ⟨74101794654793139049582371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49401196436528759366388247 74101794654793139049582371)
        ·
          refine ⟨111152691982189708574373557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74101794654793139049582371 111152691982189708574373557)
          ·
            refine ⟨10420564873330285178847521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 111152691982189708574373557 10420564873330285178847521)
            ·
              refine ⟨7815423654997713884135641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10420564873330285178847521 7815423654997713884135641)
              ·
                refine ⟨5861567741248285413101731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7815423654997713884135641 5861567741248285413101731)
                ·
                  refine ⟨8792351611872428119652597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5861567741248285413101731 8792351611872428119652597)
                  ·
                    refine ⟨824282963613040136217431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8792351611872428119652597 824282963613040136217431)
                    ·
                      rfl

theorem cell22_2407928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 2, 2, 1, 5].length) (baseStart_2407928 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2407928 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2407928 prefixEnd_2407928 := by exact prefixLift 2407928
  have htrace : WordTrace (prefixWord ++ tailWord_2407928) baseStart_2407928 baseEnd_2407928 := by
    simpa [prefixWord, tailWord_2407928, baseEnd_2407928] using wordTrace_append hprefix tailTrace_2407928
  have hstable : (prefixWord ++ tailWord_2407928).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2407928).length < 2 ^ (prefixWord ++ tailWord_2407928).sum := by decide
  have hdescent : baseEnd_2407928 < baseStart_2407928 := by decide
  rcases family_descends (prefixWord ++ tailWord_2407928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2407930 : List Nat := [3, 1, 1, 1, 1, 2, 6, 3, 4]
def baseStart_2407930 : Nat := 118140960795 + 2407930 * 2 ^ 59
def prefixEnd_2407930 : Nat := 4983230072969 + 3 ^ 40 * 2407930 * 2
def baseEnd_2407930 : Nat := 274761216084637599222475

theorem tailTrace_2407930 : CollatzResearch.WordTrace tailWord_2407930 prefixEnd_2407930 274761216084637599222475 := by
  unfold tailWord_2407930
  simp only [CollatzResearch.WordTrace]
  refine ⟨21956105541622081637121311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58549614777658884365656829 21956105541622081637121311)
  ·
    refine ⟨32934158312433122455681967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21956105541622081637121311 32934158312433122455681967)
    ·
      refine ⟨49401237468649683683522951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32934158312433122455681967 49401237468649683683522951)
      ·
        refine ⟨74101856202974525525284427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49401237468649683683522951 74101856202974525525284427)
        ·
          refine ⟨111152784304461788287926641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74101856202974525525284427 111152784304461788287926641)
          ·
            refine ⟨83364588228346341215944981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 111152784304461788287926641 83364588228346341215944981)
            ·
              refine ⟨3907715073203734744497421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 83364588228346341215944981 3907715073203734744497421)
              ·
                refine ⟨1465393152451400529186533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3907715073203734744497421 1465393152451400529186533)
                ·
                  refine ⟨274761216084637599222475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1465393152451400529186533 274761216084637599222475)
                  ·
                    rfl

theorem cell22_2407930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 6, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 6, 3, 4].length) (baseStart_2407930 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2407930 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2407930 prefixEnd_2407930 := by exact prefixLift 2407930
  have htrace : WordTrace (prefixWord ++ tailWord_2407930) baseStart_2407930 baseEnd_2407930 := by
    simpa [prefixWord, tailWord_2407930, baseEnd_2407930] using wordTrace_append hprefix tailTrace_2407930
  have hstable : (prefixWord ++ tailWord_2407930).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2407930).length < 2 ^ (prefixWord ++ tailWord_2407930).sum := by decide
  have hdescent : baseEnd_2407930 < baseStart_2407930 := by decide
  rcases family_descends (prefixWord ++ tailWord_2407930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2408013 : List Nat := [1, 6, 1, 1, 4, 1, 2, 1, 2, 3]
def baseStart_2408013 : Nat := 118140960795 + 2408013 * 2 ^ 59
def prefixEnd_2408013 : Nat := 4983230072969 + 3 ^ 40 * 2408013 * 2
def baseEnd_2408013 : Nat := 824312060850128247842171

theorem tailTrace_2408013 : CollatzResearch.WordTrace tailWord_2408013 prefixEnd_2408013 824312060850128247842171 := by
  unfold tailWord_2408013
  simp only [CollatzResearch.WordTrace]
  refine ⟨87827449425187631723756693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58551632950125087815837795 87827449425187631723756693)
  ·
    refine ⟨4116911691805670237051095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 87827449425187631723756693 4116911691805670237051095)
    ·
      refine ⟨6175367537708505355576643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4116911691805670237051095 6175367537708505355576643)
      ·
        refine ⟨9263051306562758033364965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6175367537708505355576643 9263051306562758033364965)
        ·
          refine ⟨1736822119980517131255931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9263051306562758033364965 1736822119980517131255931)
          ·
            refine ⟨2605233179970775696883897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1736822119980517131255931 2605233179970775696883897)
            ·
              refine ⟨1953924884978081772662923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2605233179970775696883897 1953924884978081772662923)
              ·
                refine ⟨2930887327467122658994385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1953924884978081772662923 2930887327467122658994385)
                ·
                  refine ⟨2198165495600341994245789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2930887327467122658994385 2198165495600341994245789)
                  ·
                    refine ⟨824312060850128247842171, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2198165495600341994245789 824312060850128247842171)
                    ·
                      rfl

theorem cell22_2408013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 4, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 4, 1, 2, 1, 2, 3].length) (baseStart_2408013 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2408013 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2408013 prefixEnd_2408013 := by exact prefixLift 2408013
  have htrace : WordTrace (prefixWord ++ tailWord_2408013) baseStart_2408013 baseEnd_2408013 := by
    simpa [prefixWord, tailWord_2408013, baseEnd_2408013] using wordTrace_append hprefix tailTrace_2408013
  have hstable : (prefixWord ++ tailWord_2408013).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2408013).length < 2 ^ (prefixWord ++ tailWord_2408013).sum := by decide
  have hdescent : baseEnd_2408013 < baseStart_2408013 := by decide
  rcases family_descends (prefixWord ++ tailWord_2408013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2408020 : List Nat := [2, 4, 1, 1, 1, 2, 3, 3, 5]
def baseStart_2408020 : Nat := 118140960795 + 2408020 * 2 ^ 59
def prefixEnd_2408020 : Nat := 4983230072969 + 3 ^ 40 * 2408020 * 2
def baseEnd_2408020 : Nat := 274771485697727520972383

theorem tailTrace_2408020 : CollatzResearch.WordTrace tailWord_2408020 prefixEnd_2408020 274771485697727520972383 := by
  unfold tailWord_2408020
  simp only [CollatzResearch.WordTrace]
  refine ⟨43913852368081135959630757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58551803157441514612841009 43913852368081135959630757)
  ·
    refine ⟨8233847319015212992430767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 43913852368081135959630757 8233847319015212992430767)
    ·
      refine ⟨12350770978522819488646151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8233847319015212992430767 12350770978522819488646151)
      ·
        refine ⟨18526156467784229232969227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12350770978522819488646151 18526156467784229232969227)
        ·
          refine ⟨27789234701676343849453841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18526156467784229232969227 27789234701676343849453841)
          ·
            refine ⟨20841926026257257887090381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27789234701676343849453841 20841926026257257887090381)
            ·
              refine ⟨7815722259846471707658893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20841926026257257887090381 7815722259846471707658893)
              ·
                refine ⟨2930895847442426890372085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7815722259846471707658893 2930895847442426890372085)
                ·
                  refine ⟨274771485697727520972383, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2930895847442426890372085 274771485697727520972383)
                  ·
                    rfl

theorem cell22_2408020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 3, 3, 5].length) (baseStart_2408020 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2408020 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2408020 prefixEnd_2408020 := by exact prefixLift 2408020
  have htrace : WordTrace (prefixWord ++ tailWord_2408020) baseStart_2408020 baseEnd_2408020 := by
    simpa [prefixWord, tailWord_2408020, baseEnd_2408020] using wordTrace_append hprefix tailTrace_2408020
  have hstable : (prefixWord ++ tailWord_2408020).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2408020).length < 2 ^ (prefixWord ++ tailWord_2408020).sum := by decide
  have hdescent : baseEnd_2408020 < baseStart_2408020 := by decide
  rcases family_descends (prefixWord ++ tailWord_2408020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2408082 : List Nat := [3, 2, 3, 1, 3, 1, 1, 2, 6]
def baseStart_2408082 : Nat := 118140960795 + 2408082 * 2 ^ 59
def prefixEnd_2408082 : Nat := 4983230072969 + 3 ^ 40 * 2408082 * 2
def baseEnd_2408082 : Nat := 274778560320078355955653

theorem tailTrace_2408082 : CollatzResearch.WordTrace tailWord_2408082 prefixEnd_2408082 274778560320078355955653 := by
  unfold tailWord_2408082
  simp only [CollatzResearch.WordTrace]
  refine ⟨21957491515484414127004625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58553310707958437672012333 21957491515484414127004625)
  ·
    refine ⟨16468118636613310595253469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21957491515484414127004625 16468118636613310595253469)
    ·
      refine ⟨6175544488729991473220051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16468118636613310595253469 6175544488729991473220051)
      ·
        refine ⟨9263316733094987209830077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6175544488729991473220051 9263316733094987209830077)
        ·
          refine ⟨3473743774910620203686279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9263316733094987209830077 3473743774910620203686279)
          ·
            refine ⟨5210615662365930305529419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3473743774910620203686279 5210615662365930305529419)
            ·
              refine ⟨7815923493548895458294129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5210615662365930305529419 7815923493548895458294129)
              ·
                refine ⟨5861942620161671593720597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7815923493548895458294129 5861942620161671593720597)
                ·
                  refine ⟨274778560320078355955653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5861942620161671593720597 274778560320078355955653)
                  ·
                    rfl

theorem cell22_2408082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 1, 1, 2, 6].length) (baseStart_2408082 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2408082 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2408082 prefixEnd_2408082 := by exact prefixLift 2408082
  have htrace : WordTrace (prefixWord ++ tailWord_2408082) baseStart_2408082 baseEnd_2408082 := by
    simpa [prefixWord, tailWord_2408082, baseEnd_2408082] using wordTrace_append hprefix tailTrace_2408082
  have hstable : (prefixWord ++ tailWord_2408082).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2408082).length < 2 ^ (prefixWord ++ tailWord_2408082).sum := by decide
  have hdescent : baseEnd_2408082 < baseStart_2408082 := by decide
  rcases family_descends (prefixWord ++ tailWord_2408082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2408108 : List Nat := [2, 2, 1, 1, 1, 1, 1, 1, 3, 9]
def baseStart_2408108 : Nat := 118140960795 + 2408108 * 2 ^ 59
def prefixEnd_2408108 : Nat := 4983230072969 + 3 ^ 40 * 2408108 * 2
def baseEnd_2408108 : Nat := 824344581291579666716879

theorem tailTrace_2408108 : CollatzResearch.WordTrace tailWord_2408108 prefixEnd_2408108 824344581291579666716879 := by
  unfold tailWord_2408108
  simp only [CollatzResearch.WordTrace]
  refine ⟨43915457179921731474232489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58553942906562308632309985 43915457179921731474232489)
  ·
    refine ⟨32936592884941298605674367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43915457179921731474232489 32936592884941298605674367)
    ·
      refine ⟨49404889327411947908511551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32936592884941298605674367 49404889327411947908511551)
      ·
        refine ⟨74107333991117921862767327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49404889327411947908511551 74107333991117921862767327)
        ·
          refine ⟨111161000986676882794150991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74107333991117921862767327 111161000986676882794150991)
          ·
            refine ⟨166741501480015324191226487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 111161000986676882794150991 166741501480015324191226487)
            ·
              refine ⟨250112252220022986286839731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 166741501480015324191226487 250112252220022986286839731)
              ·
                refine ⟨375168378330034479430259597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 250112252220022986286839731 375168378330034479430259597)
                ·
                  refine ⟨140688141873762929786347349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 375168378330034479430259597 140688141873762929786347349)
                  ·
                    refine ⟨824344581291579666716879, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 140688141873762929786347349 824344581291579666716879)
                    ·
                      rfl

theorem cell22_2408108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 9].length) (baseStart_2408108 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2408108 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2408108 prefixEnd_2408108 := by exact prefixLift 2408108
  have htrace : WordTrace (prefixWord ++ tailWord_2408108) baseStart_2408108 baseEnd_2408108 := by
    simpa [prefixWord, tailWord_2408108, baseEnd_2408108] using wordTrace_append hprefix tailTrace_2408108
  have hstable : (prefixWord ++ tailWord_2408108).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2408108).length < 2 ^ (prefixWord ++ tailWord_2408108).sum := by decide
  have hdescent : baseEnd_2408108 < baseStart_2408108 := by decide
  rcases family_descends (prefixWord ++ tailWord_2408108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2408123 : List Nat := [1, 1, 1, 1, 1, 2, 3, 3, 1, 8]
def baseStart_2408123 : Nat := 118140960795 + 2408123 * 2 ^ 59
def prefixEnd_2408123 : Nat := 4983230072969 + 3 ^ 40 * 2408123 * 2
def baseEnd_2408123 : Nat := 824349716098124627591833

theorem tailTrace_2408123 : CollatzResearch.WordTrace tailWord_2408123 prefixEnd_2408123 824349716098124627591833 := by
  unfold tailWord_2408123
  simp only [CollatzResearch.WordTrace]
  refine ⟨87831461454789120510261023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58554307636526080340174015 87831461454789120510261023)
  ·
    refine ⟨131747192182183680765391535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87831461454789120510261023 131747192182183680765391535)
    ·
      refine ⟨197620788273275521148087303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131747192182183680765391535 197620788273275521148087303)
      ·
        refine ⟨296431182409913281722130955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 197620788273275521148087303 296431182409913281722130955)
        ·
          refine ⟨444646773614869922583196433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 296431182409913281722130955 444646773614869922583196433)
          ·
            refine ⟨333485080211152441937397325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 444646773614869922583196433 333485080211152441937397325)
            ·
              refine ⟨125056905079182165726523997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 333485080211152441937397325 125056905079182165726523997)
              ·
                refine ⟨46896339404693312147446499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 125056905079182165726523997 46896339404693312147446499)
                ·
                  refine ⟨70344509107039968221169749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 46896339404693312147446499 70344509107039968221169749)
                  ·
                    refine ⟨824349716098124627591833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 70344509107039968221169749 824349716098124627591833)
                    ·
                      rfl

theorem cell22_2408123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 3, 1, 8].length) (baseStart_2408123 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2408123 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2408123 prefixEnd_2408123 := by exact prefixLift 2408123
  have htrace : WordTrace (prefixWord ++ tailWord_2408123) baseStart_2408123 baseEnd_2408123 := by
    simpa [prefixWord, tailWord_2408123, baseEnd_2408123] using wordTrace_append hprefix tailTrace_2408123
  have hstable : (prefixWord ++ tailWord_2408123).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2408123).length < 2 ^ (prefixWord ++ tailWord_2408123).sum := by decide
  have hdescent : baseEnd_2408123 < baseStart_2408123 := by decide
  rcases family_descends (prefixWord ++ tailWord_2408123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2408142 : List Nat := [4, 1, 1, 1, 3, 1, 1, 4, 3, 3]
def baseStart_2408142 : Nat := 118140960795 + 2408142 * 2 ^ 59
def prefixEnd_2408142 : Nat := 4983230072969 + 3 ^ 40 * 2408142 * 2
def baseEnd_2408142 : Nat := 824356220186414911366775

theorem tailTrace_2408142 : CollatzResearch.WordTrace tailWord_2408142 prefixEnd_2408142 824356220186414911366775 := by
  unfold tailWord_2408142
  simp only [CollatzResearch.WordTrace]
  refine ⟨10979019305215035844400335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 58554769627813524503468453 10979019305215035844400335)
  ·
    refine ⟨16468528957822553766600503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10979019305215035844400335 16468528957822553766600503)
    ·
      refine ⟨24702793436733830649900755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16468528957822553766600503 24702793436733830649900755)
      ·
        refine ⟨37054190155100745974851133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24702793436733830649900755 37054190155100745974851133)
        ·
          refine ⟨13895321308162779740569175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37054190155100745974851133 13895321308162779740569175)
          ·
            refine ⟨20842981962244169610853763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13895321308162779740569175 20842981962244169610853763)
            ·
              refine ⟨31264472943366254416280645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20842981962244169610853763 31264472943366254416280645)
              ·
                refine ⟨5862088676881172703052621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 31264472943366254416280645 5862088676881172703052621)
                ·
                  refine ⟨2198283253830439763644733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5862088676881172703052621 2198283253830439763644733)
                  ·
                    refine ⟨824356220186414911366775, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2198283253830439763644733 824356220186414911366775)
                    ·
                      rfl

theorem cell22_2408142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 1, 4, 3, 3].length) (baseStart_2408142 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2408142 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2408142 prefixEnd_2408142 := by exact prefixLift 2408142
  have htrace : WordTrace (prefixWord ++ tailWord_2408142) baseStart_2408142 baseEnd_2408142 := by
    simpa [prefixWord, tailWord_2408142, baseEnd_2408142] using wordTrace_append hprefix tailTrace_2408142
  have hstable : (prefixWord ++ tailWord_2408142).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2408142).length < 2 ^ (prefixWord ++ tailWord_2408142).sum := by decide
  have hdescent : baseEnd_2408142 < baseStart_2408142 := by decide
  rcases family_descends (prefixWord ++ tailWord_2408142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2408150 : List Nat := [5, 2, 1, 3, 2, 1, 1, 3, 4]
def baseStart_2408150 : Nat := 118140960795 + 2408150 * 2 ^ 59
def prefixEnd_2408150 : Nat := 4983230072969 + 3 ^ 40 * 2408150 * 2
def baseEnd_2408150 : Nat := 274786319583301852388917

theorem tailTrace_2408150 : CollatzResearch.WordTrace tailWord_2408150 prefixEnd_2408150 274786319583301852388917 := by
  unfold tailWord_2408150
  simp only [CollatzResearch.WordTrace]
  refine ⟨5489527889105706507593369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 58554964150460869414329269 5489527889105706507593369)
  ·
    refine ⟨4117145916829279880695027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5489527889105706507593369 4117145916829279880695027)
    ·
      refine ⟨6175718875243919821042541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4117145916829279880695027 6175718875243919821042541)
      ·
        refine ⟨2315894578216469932890953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6175718875243919821042541 2315894578216469932890953)
        ·
          refine ⟨1736920933662352449668215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2315894578216469932890953 1736920933662352449668215)
          ·
            refine ⟨2605381400493528674502323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1736920933662352449668215 2605381400493528674502323)
            ·
              refine ⟨3908072100740293011753485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2605381400493528674502323 3908072100740293011753485)
              ·
                refine ⟨1465527037777609879407557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3908072100740293011753485 1465527037777609879407557)
                ·
                  refine ⟨274786319583301852388917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1465527037777609879407557 274786319583301852388917)
                  ·
                    rfl

theorem cell22_2408150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 2, 1, 1, 3, 4].length) (baseStart_2408150 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2408150 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2408150 prefixEnd_2408150 := by exact prefixLift 2408150
  have htrace : WordTrace (prefixWord ++ tailWord_2408150) baseStart_2408150 baseEnd_2408150 := by
    simpa [prefixWord, tailWord_2408150, baseEnd_2408150] using wordTrace_append hprefix tailTrace_2408150
  have hstable : (prefixWord ++ tailWord_2408150).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2408150).length < 2 ^ (prefixWord ++ tailWord_2408150).sum := by decide
  have hdescent : baseEnd_2408150 < baseStart_2408150 := by decide
  rcases family_descends (prefixWord ++ tailWord_2408150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2408170 : List Nat := [3, 1, 3, 1, 1, 1, 2, 1, 4, 5]
def baseStart_2408170 : Nat := 118140960795 + 2408170 * 2 ^ 59
def prefixEnd_2408170 : Nat := 4983230072969 + 3 ^ 40 * 2408170 * 2
def baseEnd_2408170 : Nat := 824365805158632171666689

theorem tailTrace_2408170 : CollatzResearch.WordTrace tailWord_2408170 prefixEnd_2408170 824365805158632171666689 := by
  unfold tailWord_2408170
  simp only [CollatzResearch.WordTrace]
  refine ⟨21958293921404711884305491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58555450457079231691481309 21958293921404711884305491)
  ·
    refine ⟨32937440882107067826458237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21958293921404711884305491 32937440882107067826458237)
    ·
      refine ⟨12351540330790150434921839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32937440882107067826458237 12351540330790150434921839)
      ·
        refine ⟨18527310496185225652382759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12351540330790150434921839 18527310496185225652382759)
        ·
          refine ⟨27790965744277838478574139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18527310496185225652382759 27790965744277838478574139)
          ·
            refine ⟨41686448616416757717861209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27790965744277838478574139 41686448616416757717861209)
            ·
              refine ⟨31264836462312568288395907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41686448616416757717861209 31264836462312568288395907)
              ·
                refine ⟨46897254693468852432593861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31264836462312568288395907 46897254693468852432593861)
                ·
                  refine ⟨8793235255025409831111349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 46897254693468852432593861 8793235255025409831111349)
                  ·
                    refine ⟨824365805158632171666689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8793235255025409831111349 824365805158632171666689)
                    ·
                      rfl

theorem cell22_2408170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 2, 1, 4, 5].length) (baseStart_2408170 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2408170 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2408170 prefixEnd_2408170 := by exact prefixLift 2408170
  have htrace : WordTrace (prefixWord ++ tailWord_2408170) baseStart_2408170 baseEnd_2408170 := by
    simpa [prefixWord, tailWord_2408170, baseEnd_2408170] using wordTrace_append hprefix tailTrace_2408170
  have hstable : (prefixWord ++ tailWord_2408170).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2408170).length < 2 ^ (prefixWord ++ tailWord_2408170).sum := by decide
  have hdescent : baseEnd_2408170 < baseStart_2408170 := by decide
  rcases family_descends (prefixWord ++ tailWord_2408170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2408200 : List Nat := [2, 1, 3, 2, 2, 1, 2, 1, 8]
def baseStart_2408200 : Nat := 118140960795 + 2408200 * 2 ^ 59
def prefixEnd_2408200 : Nat := 4983230072969 + 3 ^ 40 * 2408200 * 2
def baseEnd_2408200 : Nat := 274792024923907364472199

theorem tailTrace_2408200 : CollatzResearch.WordTrace tailWord_2408200 prefixEnd_2408200 274792024923907364472199 := by
  unfold tailWord_2408200
  simp only [CollatzResearch.WordTrace]
  refine ⟨43917134937755081330407027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58556179917006775107209369 43917134937755081330407027)
  ·
    refine ⟨65875702406632621995610541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43917134937755081330407027 65875702406632621995610541)
    ·
      refine ⟨24703388402487233248353953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 65875702406632621995610541 24703388402487233248353953)
      ·
        refine ⟨18527541301865424936265465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24703388402487233248353953 18527541301865424936265465)
        ·
          refine ⟨13895655976399068702199099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18527541301865424936265465 13895655976399068702199099)
          ·
            refine ⟨20843483964598603053298649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13895655976399068702199099 20843483964598603053298649)
            ·
              refine ⟨15632612973448952289973987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20843483964598603053298649 15632612973448952289973987)
              ·
                refine ⟨23448919460173428434960981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15632612973448952289973987 23448919460173428434960981)
                ·
                  refine ⟨274792024923907364472199, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 23448919460173428434960981 274792024923907364472199)
                  ·
                    rfl

theorem cell22_2408200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 2, 1, 8].length) (baseStart_2408200 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2408200 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2408200 prefixEnd_2408200 := by exact prefixLift 2408200
  have htrace : WordTrace (prefixWord ++ tailWord_2408200) baseStart_2408200 baseEnd_2408200 := by
    simpa [prefixWord, tailWord_2408200, baseEnd_2408200] using wordTrace_append hprefix tailTrace_2408200
  have hstable : (prefixWord ++ tailWord_2408200).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2408200).length < 2 ^ (prefixWord ++ tailWord_2408200).sum := by decide
  have hdescent : baseEnd_2408200 < baseStart_2408200 := by decide
  rcases family_descends (prefixWord ++ tailWord_2408200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2408202 : List Nat := [3, 1, 2, 2, 1, 4, 1, 1, 3, 4]
def baseStart_2408202 : Nat := 118140960795 + 2408202 * 2 ^ 59
def prefixEnd_2408202 : Nat := 4983230072969 + 3 ^ 40 * 2408202 * 2
def baseEnd_2408202 : Nat := 824376759412594754866591

theorem tailTrace_2408202 : CollatzResearch.WordTrace tailWord_2408202 prefixEnd_2408202 824376759412594754866591 := by
  unfold tailWord_2408202
  simp only [CollatzResearch.WordTrace]
  refine ⟨21958585705375729250596715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58556228547668611334924573 21958585705375729250596715)
  ·
    refine ⟨32937878558063593875895073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21958585705375729250596715 32937878558063593875895073)
    ·
      refine ⟨24703408918547695406921305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32937878558063593875895073 24703408918547695406921305)
      ·
        refine ⟨18527556688910771555190979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24703408918547695406921305 18527556688910771555190979)
        ·
          refine ⟨27791335033366157332786469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18527556688910771555190979 27791335033366157332786469)
          ·
            refine ⟨5210875318756154499897463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27791335033366157332786469 5210875318756154499897463)
            ·
              refine ⟨7816312978134231749846195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5210875318756154499897463 7816312978134231749846195)
              ·
                refine ⟨11724469467201347624769293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7816312978134231749846195 11724469467201347624769293)
                ·
                  refine ⟨4396676050200505359288485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11724469467201347624769293 4396676050200505359288485)
                  ·
                    refine ⟨824376759412594754866591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4396676050200505359288485 824376759412594754866591)
                    ·
                      rfl

theorem cell22_2408202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 4, 1, 1, 3, 4].length) (baseStart_2408202 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2408202 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2408202 prefixEnd_2408202 := by exact prefixLift 2408202
  have htrace : WordTrace (prefixWord ++ tailWord_2408202) baseStart_2408202 baseEnd_2408202 := by
    simpa [prefixWord, tailWord_2408202, baseEnd_2408202] using wordTrace_append hprefix tailTrace_2408202
  have hstable : (prefixWord ++ tailWord_2408202).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2408202).length < 2 ^ (prefixWord ++ tailWord_2408202).sum := by decide
  have hdescent : baseEnd_2408202 < baseStart_2408202 := by decide
  rcases family_descends (prefixWord ++ tailWord_2408202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2408264 : List Nat := [2, 1, 3, 1, 1, 6, 1, 1, 2, 4]
def baseStart_2408264 : Nat := 118140960795 + 2408264 * 2 ^ 59
def prefixEnd_2408264 : Nat := 4983230072969 + 3 ^ 40 * 2408264 * 2
def baseEnd_2408264 : Nat := 824397983279647259816401

theorem tailTrace_2408264 : CollatzResearch.WordTrace tailWord_2408264 prefixEnd_2408264 824397983279647259816401 := by
  unfold tailWord_2408264
  simp only [CollatzResearch.WordTrace]
  refine ⟨43918302073639150795571923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58557736098185534394095897 43918302073639150795571923)
  ·
    refine ⟨65877453110458726193357885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43918302073639150795571923 65877453110458726193357885)
    ·
      refine ⟨24704044916422022322509207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 65877453110458726193357885 24704044916422022322509207)
      ·
        refine ⟨37056067374633033483763811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24704044916422022322509207 37056067374633033483763811)
        ·
          refine ⟨55584101061949550225645717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37056067374633033483763811 55584101061949550225645717)
          ·
            refine ⟨2605504737278885166827143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 55584101061949550225645717 2605504737278885166827143)
            ·
              refine ⟨3908257105918327750240715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2605504737278885166827143 3908257105918327750240715)
              ·
                refine ⟨5862385658877491625361073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3908257105918327750240715 5862385658877491625361073)
                ·
                  refine ⟨4396789244158118719020805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5862385658877491625361073 4396789244158118719020805)
                  ·
                    refine ⟨824397983279647259816401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4396789244158118719020805 824397983279647259816401)
                    ·
                      rfl

theorem cell22_2408264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 6, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 6, 1, 1, 2, 4].length) (baseStart_2408264 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2408264 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2408264 prefixEnd_2408264 := by exact prefixLift 2408264
  have htrace : WordTrace (prefixWord ++ tailWord_2408264) baseStart_2408264 baseEnd_2408264 := by
    simpa [prefixWord, tailWord_2408264, baseEnd_2408264] using wordTrace_append hprefix tailTrace_2408264
  have hstable : (prefixWord ++ tailWord_2408264).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2408264).length < 2 ^ (prefixWord ++ tailWord_2408264).sum := by decide
  have hdescent : baseEnd_2408264 < baseStart_2408264 := by decide
  rcases family_descends (prefixWord ++ tailWord_2408264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2408367 : List Nat := [1, 1, 2, 1, 2, 2, 4, 3, 1, 5]
def baseStart_2408367 : Nat := 118140960795 + 2408367 * 2 ^ 59
def prefixEnd_2408367 : Nat := 4983230072969 + 3 ^ 40 * 2408367 * 2
def baseEnd_2408367 : Nat := 824433242284589324491085

theorem tailTrace_2408367 : CollatzResearch.WordTrace tailWord_2408367 prefixEnd_2408367 824433242284589324491085 := by
  unfold tailWord_2408367
  simp only [CollatzResearch.WordTrace]
  refine ⟨87840360865905150182143355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58560240577270100121428903 87840360865905150182143355)
  ·
    refine ⟨131760541298857725273215033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87840360865905150182143355 131760541298857725273215033)
    ·
      refine ⟨98820405974143293954911275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 131760541298857725273215033 98820405974143293954911275)
      ·
        refine ⟨148230608961214940932366913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98820405974143293954911275 148230608961214940932366913)
        ·
          refine ⟨111172956720911205699275185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 148230608961214940932366913 111172956720911205699275185)
          ·
            refine ⟨83379717540683404274456389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 111172956720911205699275185 83379717540683404274456389)
            ·
              refine ⟨15633697038878138301460573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 83379717540683404274456389 15633697038878138301460573)
              ·
                refine ⟨5862636389579301863047715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15633697038878138301460573 5862636389579301863047715)
                ·
                  refine ⟨8793954584368952794571573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5862636389579301863047715 8793954584368952794571573)
                  ·
                    refine ⟨824433242284589324491085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8793954584368952794571573 824433242284589324491085)
                    ·
                      rfl

theorem cell22_2408367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 4, 3, 1, 5].length) (baseStart_2408367 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2408367 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2408367 prefixEnd_2408367 := by exact prefixLift 2408367
  have htrace : WordTrace (prefixWord ++ tailWord_2408367) baseStart_2408367 baseEnd_2408367 := by
    simpa [prefixWord, tailWord_2408367, baseEnd_2408367] using wordTrace_append hprefix tailTrace_2408367
  have hstable : (prefixWord ++ tailWord_2408367).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2408367).length < 2 ^ (prefixWord ++ tailWord_2408367).sum := by decide
  have hdescent : baseEnd_2408367 < baseStart_2408367 := by decide
  rcases family_descends (prefixWord ++ tailWord_2408367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2408418 : List Nat := [3, 3, 3, 1, 2, 1, 2, 1, 1, 5]
def baseStart_2408418 : Nat := 118140960795 + 2408418 * 2 ^ 59
def prefixEnd_2408418 : Nat := 4983230072969 + 3 ^ 40 * 2408418 * 2
def baseEnd_2408418 : Nat := 824450700626842191465929

theorem tailTrace_2408418 : CollatzResearch.WordTrace tailWord_2408418 prefixEnd_2408418 824450700626842191465929 := by
  unfold tailWord_2408418
  simp only [CollatzResearch.WordTrace]
  refine ⟨21960555247180096473062477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58561480659146923928166605 21960555247180096473062477)
  ·
    refine ⟨8235208217692536177398429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21960555247180096473062477 8235208217692536177398429)
    ·
      refine ⟨3088203081634701066524411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8235208217692536177398429 3088203081634701066524411)
      ·
        refine ⟨4632304622452051599786617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3088203081634701066524411 4632304622452051599786617)
        ·
          refine ⟨3474228466839038699839963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4632304622452051599786617 3474228466839038699839963)
          ·
            refine ⟨5211342700258558049759945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3474228466839038699839963 5211342700258558049759945)
            ·
              refine ⟨3908507025193918537319959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5211342700258558049759945 3908507025193918537319959)
              ·
                refine ⟨5862760537790877805979939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3908507025193918537319959 5862760537790877805979939)
                ·
                  refine ⟨8794140806686316708969909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5862760537790877805979939 8794140806686316708969909)
                  ·
                    refine ⟨824450700626842191465929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8794140806686316708969909 824450700626842191465929)
                    ·
                      rfl

theorem cell22_2408418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 1, 2, 1, 1, 5].length) (baseStart_2408418 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2408418 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2408418 prefixEnd_2408418 := by exact prefixLift 2408418
  have htrace : WordTrace (prefixWord ++ tailWord_2408418) baseStart_2408418 baseEnd_2408418 := by
    simpa [prefixWord, tailWord_2408418, baseEnd_2408418] using wordTrace_append hprefix tailTrace_2408418
  have hstable : (prefixWord ++ tailWord_2408418).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2408418).length < 2 ^ (prefixWord ++ tailWord_2408418).sum := by decide
  have hdescent : baseEnd_2408418 < baseStart_2408418 := by decide
  rcases family_descends (prefixWord ++ tailWord_2408418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2408433 : List Nat := [1, 2, 2, 2, 6, 1, 1, 1, 2, 4]
def baseStart_2408433 : Nat := 118140960795 + 2408433 * 2 ^ 59
def prefixEnd_2408433 : Nat := 4983230072969 + 3 ^ 40 * 2408433 * 2
def baseEnd_2408433 : Nat := 824455835433387152340883

theorem tailTrace_2408433 : CollatzResearch.WordTrace tailWord_2408433 prefixEnd_2408433 824455835433387152340883 := by
  unfold tailWord_2408433
  simp only [CollatzResearch.WordTrace]
  refine ⟨87842768083666043454045953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58561845389110695636030635 87842768083666043454045953)
  ·
    refine ⟨65882076062749532590534465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87842768083666043454045953 65882076062749532590534465)
    ·
      refine ⟨49411557047062149442900849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65882076062749532590534465 49411557047062149442900849)
      ·
        refine ⟨37058667785296612082175637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49411557047062149442900849 37058667785296612082175637)
        ·
          refine ⟨1737125052435778691351983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 37058667785296612082175637 1737125052435778691351983)
          ·
            refine ⟨2605687578653668037027975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1737125052435778691351983 2605687578653668037027975)
            ·
              refine ⟨3908531367980502055541963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2605687578653668037027975 3908531367980502055541963)
              ·
                refine ⟨5862797051970753083312945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3908531367980502055541963 5862797051970753083312945)
                ·
                  refine ⟨4397097788978064812484709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5862797051970753083312945 4397097788978064812484709)
                  ·
                    refine ⟨824455835433387152340883, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4397097788978064812484709 824455835433387152340883)
                    ·
                      rfl

theorem cell22_2408433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 6, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 6, 1, 1, 1, 2, 4].length) (baseStart_2408433 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2408433 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2408433 prefixEnd_2408433 := by exact prefixLift 2408433
  have htrace : WordTrace (prefixWord ++ tailWord_2408433) baseStart_2408433 baseEnd_2408433 := by
    simpa [prefixWord, tailWord_2408433, baseEnd_2408433] using wordTrace_append hprefix tailTrace_2408433
  have hstable : (prefixWord ++ tailWord_2408433).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2408433).length < 2 ^ (prefixWord ++ tailWord_2408433).sum := by decide
  have hdescent : baseEnd_2408433 < baseStart_2408433 := by decide
  rcases family_descends (prefixWord ++ tailWord_2408433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2408452 : List Nat := [2, 3, 2, 4, 2, 1, 1, 2, 2, 3]
def baseStart_2408452 : Nat := 118140960795 + 2408452 * 2 ^ 59
def prefixEnd_2408452 : Nat := 4983230072969 + 3 ^ 40 * 2408452 * 2
def baseEnd_2408452 : Nat := 824462339521677436115825

theorem tailTrace_2408452 : CollatzResearch.WordTrace tailWord_2408452 prefixEnd_2408452 824462339521677436115825 := by
  unfold tailWord_2408452
  simp only [CollatzResearch.WordTrace]
  refine ⟨43921730535298604849493805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58562307380398139799325073 43921730535298604849493805)
  ·
    refine ⟨16470648950736976818560177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43921730535298604849493805 16470648950736976818560177)
    ·
      refine ⟨12352986713052732613920133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16470648950736976818560177 12352986713052732613920133)
      ·
        refine ⟨2316185008697387365110025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12352986713052732613920133 2316185008697387365110025)
        ·
          refine ⟨1737138756523040523832519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2316185008697387365110025 1737138756523040523832519)
          ·
            refine ⟨2605708134784560785748779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1737138756523040523832519 2605708134784560785748779)
            ·
              refine ⟨3908562202176841178623169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2605708134784560785748779 3908562202176841178623169)
              ·
                refine ⟨2931421651632630883967377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3908562202176841178623169 2931421651632630883967377)
                ·
                  refine ⟨2198566238724473162975533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2931421651632630883967377 2198566238724473162975533)
                  ·
                    refine ⟨824462339521677436115825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2198566238724473162975533 824462339521677436115825)
                    ·
                      rfl

theorem cell22_2408452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 2, 1, 1, 2, 2, 3].length) (baseStart_2408452 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2408452 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2408452 prefixEnd_2408452 := by exact prefixLift 2408452
  have htrace : WordTrace (prefixWord ++ tailWord_2408452) baseStart_2408452 baseEnd_2408452 := by
    simpa [prefixWord, tailWord_2408452, baseEnd_2408452] using wordTrace_append hprefix tailTrace_2408452
  have hstable : (prefixWord ++ tailWord_2408452).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2408452).length < 2 ^ (prefixWord ++ tailWord_2408452).sum := by decide
  have hdescent : baseEnd_2408452 < baseStart_2408452 := by decide
  rcases family_descends (prefixWord ++ tailWord_2408452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2408474 : List Nat := [3, 1, 1, 3, 1, 3, 2, 1, 2, 5]
def baseStart_2408474 : Nat := 118140960795 + 2408474 * 2 ^ 59
def prefixEnd_2408474 : Nat := 4983230072969 + 3 ^ 40 * 2408474 * 2
def baseEnd_2408474 : Nat := 824469870571276712065757

theorem tailTrace_2408474 : CollatzResearch.WordTrace tailWord_2408474 prefixEnd_2408474 824469870571276712065757 := by
  unfold tailWord_2408474
  simp only [CollatzResearch.WordTrace]
  refine ⟨21961065869129376864072119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58562842317678338304192317 21961065869129376864072119)
  ·
    refine ⟨32941598803694065296108179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21961065869129376864072119 32941598803694065296108179)
    ·
      refine ⟨49412398205541097944162269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32941598803694065296108179 49412398205541097944162269)
      ·
        refine ⟨18529649327077911729060851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 49412398205541097944162269 18529649327077911729060851)
        ·
          refine ⟨27794473990616867593591277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18529649327077911729060851 27794473990616867593591277)
          ·
            refine ⟨10422927746481325347596729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27794473990616867593591277 10422927746481325347596729)
            ·
              refine ⟨7817195809860994010697547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10422927746481325347596729 7817195809860994010697547)
              ·
                refine ⟨11725793714791491016046321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7817195809860994010697547 11725793714791491016046321)
                ·
                  refine ⟨8794345286093618262034741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11725793714791491016046321 8794345286093618262034741)
                  ·
                    refine ⟨824469870571276712065757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8794345286093618262034741 824469870571276712065757)
                    ·
                      rfl

theorem cell22_2408474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 2, 1, 2, 5].length) (baseStart_2408474 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2408474 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2408474 prefixEnd_2408474 := by exact prefixLift 2408474
  have htrace : WordTrace (prefixWord ++ tailWord_2408474) baseStart_2408474 baseEnd_2408474 := by
    simpa [prefixWord, tailWord_2408474, baseEnd_2408474] using wordTrace_append hprefix tailTrace_2408474
  have hstable : (prefixWord ++ tailWord_2408474).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2408474).length < 2 ^ (prefixWord ++ tailWord_2408474).sum := by decide
  have hdescent : baseEnd_2408474 < baseStart_2408474 := by decide
  rcases family_descends (prefixWord ++ tailWord_2408474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2408549 : List Nat := [1, 3, 1, 3, 2, 2, 2, 8]
def baseStart_2408549 : Nat := 118140960795 + 2408549 * 2 ^ 59
def prefixEnd_2408549 : Nat := 4983230072969 + 3 ^ 40 * 2408549 * 2
def baseEnd_2408549 : Nat := 91610616067111279604503

theorem tailTrace_2408549 : CollatzResearch.WordTrace tailWord_2408549 prefixEnd_2408549 91610616067111279604503 := by
  unfold tailWord_2408549
  simp only [CollatzResearch.WordTrace]
  refine ⟨87846998951245795265268701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58564665967497196843512467 87846998951245795265268701)
  ·
    refine ⟨32942624606717173224475763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 87846998951245795265268701 32942624606717173224475763)
    ·
      refine ⟨49413936910075759836713645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32942624606717173224475763 49413936910075759836713645)
      ·
        refine ⟨18530226341278409938767617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 49413936910075759836713645 18530226341278409938767617)
        ·
          refine ⟨13897669755958807454075713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18530226341278409938767617 13897669755958807454075713)
          ·
            refine ⟨10423252316969105590556785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13897669755958807454075713 10423252316969105590556785)
            ·
              refine ⟨7817439237726829192917589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10423252316969105590556785 7817439237726829192917589)
              ·
                refine ⟨91610616067111279604503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7817439237726829192917589 91610616067111279604503)
                ·
                  rfl

theorem cell22_2408549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 2, 8].length) (baseStart_2408549 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2408549 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2408549 prefixEnd_2408549 := by exact prefixLift 2408549
  have htrace : WordTrace (prefixWord ++ tailWord_2408549) baseStart_2408549 baseEnd_2408549 := by
    simpa [prefixWord, tailWord_2408549, baseEnd_2408549] using wordTrace_append hprefix tailTrace_2408549
  have hstable : (prefixWord ++ tailWord_2408549).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2408549).length < 2 ^ (prefixWord ++ tailWord_2408549).sum := by decide
  have hdescent : baseEnd_2408549 < baseStart_2408549 := by decide
  rcases family_descends (prefixWord ++ tailWord_2408549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2408551 : List Nat := [1, 1, 5, 1, 1, 2, 4, 1, 2, 4]
def baseStart_2408551 : Nat := 118140960795 + 2408551 * 2 ^ 59
def prefixEnd_2408551 : Nat := 4983230072969 + 3 ^ 40 * 2408551 * 2
def baseEnd_2408551 : Nat := 824496229244874177890521

theorem tailTrace_2408551 : CollatzResearch.WordTrace tailWord_2408551 prefixEnd_2408551 824496229244874177890521 := by
  unfold tailWord_2408551
  simp only [CollatzResearch.WordTrace]
  refine ⟨87847071897238549606841507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58564714598159033071227671 87847071897238549606841507)
  ·
    refine ⟨131770607845857824410262261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87847071897238549606841507 131770607845857824410262261)
    ·
      refine ⟨12353494485549171038462087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 131770607845857824410262261 12353494485549171038462087)
      ·
        refine ⟨18530241728323756557693131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12353494485549171038462087 18530241728323756557693131)
        ·
          refine ⟨27795362592485634836539697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18530241728323756557693131 27795362592485634836539697)
          ·
            refine ⟨20846521944364226127404773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27795362592485634836539697 20846521944364226127404773)
            ·
              refine ⟨3908722864568292398888395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20846521944364226127404773 3908722864568292398888395)
              ·
                refine ⟨5863084296852438598332593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3908722864568292398888395 5863084296852438598332593)
                ·
                  refine ⟨4397313222639328948749445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5863084296852438598332593 4397313222639328948749445)
                  ·
                    refine ⟨824496229244874177890521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4397313222639328948749445 824496229244874177890521)
                    ·
                      rfl

theorem cell22_2408551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 4, 1, 2, 4].length) (baseStart_2408551 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2408551 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2408551 prefixEnd_2408551 := by exact prefixLift 2408551
  have htrace : WordTrace (prefixWord ++ tailWord_2408551) baseStart_2408551 baseEnd_2408551 := by
    simpa [prefixWord, tailWord_2408551, baseEnd_2408551] using wordTrace_append hprefix tailTrace_2408551
  have hstable : (prefixWord ++ tailWord_2408551).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2408551).length < 2 ^ (prefixWord ++ tailWord_2408551).sum := by decide
  have hdescent : baseEnd_2408551 < baseStart_2408551 := by decide
  rcases family_descends (prefixWord ++ tailWord_2408551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2408579 : List Nat := [1, 1, 1, 3, 3, 3, 1, 1, 2, 6]
def baseStart_2408579 : Nat := 118140960795 + 2408579 * 2 ^ 59
def prefixEnd_2408579 : Nat := 4983230072969 + 3 ^ 40 * 2408579 * 2
def baseEnd_2408579 : Nat := 824505814217091438190435

theorem tailTrace_2408579 : CollatzResearch.WordTrace tailWord_2408579 prefixEnd_2408579 824505814217091438190435 := by
  unfold tailWord_2408579
  simp only [CollatzResearch.WordTrace]
  refine ⟨87848093141137110388860791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58565395427424740259240527 87848093141137110388860791)
  ·
    refine ⟨131772139711705665583291187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87848093141137110388860791 131772139711705665583291187)
    ·
      refine ⟨197658209567558498374936781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131772139711705665583291187 197658209567558498374936781)
      ·
        refine ⟨74121828587834436890601293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 197658209567558498374936781 74121828587834436890601293)
        ·
          refine ⟨27795685720437913833975485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 74121828587834436890601293 27795685720437913833975485)
          ·
            refine ⟨10423382145164217687740807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27795685720437913833975485 10423382145164217687740807)
            ·
              refine ⟨15635073217746326531611211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10423382145164217687740807 15635073217746326531611211)
              ·
                refine ⟨23452609826619489797416817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15635073217746326531611211 23452609826619489797416817)
                ·
                  refine ⟨17589457369964617348062613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23452609826619489797416817 17589457369964617348062613)
                  ·
                    refine ⟨824505814217091438190435, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17589457369964617348062613 824505814217091438190435)
                    ·
                      rfl

theorem cell22_2408579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 1, 1, 2, 6].length) (baseStart_2408579 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2408579 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2408579 prefixEnd_2408579 := by exact prefixLift 2408579
  have htrace : WordTrace (prefixWord ++ tailWord_2408579) baseStart_2408579 baseEnd_2408579 := by
    simpa [prefixWord, tailWord_2408579, baseEnd_2408579] using wordTrace_append hprefix tailTrace_2408579
  have hstable : (prefixWord ++ tailWord_2408579).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2408579).length < 2 ^ (prefixWord ++ tailWord_2408579).sum := by decide
  have hdescent : baseEnd_2408579 < baseStart_2408579 := by decide
  rcases family_descends (prefixWord ++ tailWord_2408579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2408658 : List Nat := [3, 2, 2, 2, 1, 2, 1, 4, 1, 4]
def baseStart_2408658 : Nat := 118140960795 + 2408658 * 2 ^ 59
def prefixEnd_2408658 : Nat := 4983230072969 + 3 ^ 40 * 2408658 * 2
def baseEnd_2408658 : Nat := 824532857531561565465193

theorem tailTrace_2408658 : CollatzResearch.WordTrace tailWord_2408658 prefixEnd_2408658 824532857531561565465193 := by
  unfold tailWord_2408658
  simp only [CollatzResearch.WordTrace]
  refine ⟨21962743626962726720246657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58567316338567271253991085 21962743626962726720246657)
  ·
    refine ⟨16472057720222045040184993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21962743626962726720246657 16472057720222045040184993)
    ·
      refine ⟨12354043290166533780138745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16472057720222045040184993 12354043290166533780138745)
      ·
        refine ⟨9265532467624900335104059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12354043290166533780138745 9265532467624900335104059)
        ·
          refine ⟨13898298701437350502656089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9265532467624900335104059 13898298701437350502656089)
          ·
            refine ⟨10423724026078012876992067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13898298701437350502656089 10423724026078012876992067)
            ·
              refine ⟨15635586039117019315488101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10423724026078012876992067 15635586039117019315488101)
              ·
                refine ⟨2931672382334441121654019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15635586039117019315488101 2931672382334441121654019)
                ·
                  refine ⟨4397508573501661682481029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2931672382334441121654019 4397508573501661682481029)
                  ·
                    refine ⟨824532857531561565465193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4397508573501661682481029 824532857531561565465193)
                    ·
                      rfl

theorem cell22_2408658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 1, 4, 1, 4].length) (baseStart_2408658 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2408658 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2408658 prefixEnd_2408658 := by exact prefixLift 2408658
  have htrace : WordTrace (prefixWord ++ tailWord_2408658) baseStart_2408658 baseEnd_2408658 := by
    simpa [prefixWord, tailWord_2408658, baseEnd_2408658] using wordTrace_append hprefix tailTrace_2408658
  have hstable : (prefixWord ++ tailWord_2408658).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2408658).length < 2 ^ (prefixWord ++ tailWord_2408658).sum := by decide
  have hdescent : baseEnd_2408658 < baseStart_2408658 := by decide
  rcases family_descends (prefixWord ++ tailWord_2408658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2408791 : List Nat := [1, 1, 3, 2, 3, 1, 1, 2, 8]
def baseStart_2408791 : Nat := 118140960795 + 2408791 * 2 ^ 59
def prefixEnd_2408791 : Nat := 4983230072969 + 3 ^ 40 * 2408791 * 2
def baseEnd_2408791 : Nat := 274859462049864517296595

theorem tailTrace_2408791 : CollatzResearch.WordTrace tailWord_2408791 prefixEnd_2408791 274859462049864517296595 := by
  unfold tailWord_2408791
  simp only [CollatzResearch.WordTrace]
  refine ⟨87855825416369070595578227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58570550277579380397052151 87855825416369070595578227)
  ·
    refine ⟨131783738124553605893367341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87855825416369070595578227 131783738124553605893367341)
    ·
      refine ⟨49418901796707602210012753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 131783738124553605893367341 49418901796707602210012753)
      ·
        refine ⟨37064176347530701657509565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49418901796707602210012753 37064176347530701657509565)
        ·
          refine ⟨13899066130324013121566087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37064176347530701657509565 13899066130324013121566087)
          ·
            refine ⟨20848599195486019682349131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13899066130324013121566087 20848599195486019682349131)
            ·
              refine ⟨31272898793229029523523697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20848599195486019682349131 31272898793229029523523697)
              ·
                refine ⟨23454674094921772142642773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31272898793229029523523697 23454674094921772142642773)
                ·
                  refine ⟨274859462049864517296595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 23454674094921772142642773 274859462049864517296595)
                  ·
                    rfl

theorem cell22_2408791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 1, 2, 8].length) (baseStart_2408791 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2408791 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2408791 prefixEnd_2408791 := by exact prefixLift 2408791
  have htrace : WordTrace (prefixWord ++ tailWord_2408791) baseStart_2408791 baseEnd_2408791 := by
    simpa [prefixWord, tailWord_2408791, baseEnd_2408791] using wordTrace_append hprefix tailTrace_2408791
  have hstable : (prefixWord ++ tailWord_2408791).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2408791).length < 2 ^ (prefixWord ++ tailWord_2408791).sum := by decide
  have hdescent : baseEnd_2408791 < baseStart_2408791 := by decide
  rcases family_descends (prefixWord ++ tailWord_2408791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2408808 : List Nat := [2, 1, 4, 2, 2, 1, 1, 3, 6]
def baseStart_2408808 : Nat := 118140960795 + 2408808 * 2 ^ 59
def prefixEnd_2408808 : Nat := 4983230072969 + 3 ^ 40 * 2408808 * 2
def baseEnd_2408808 : Nat := 274861401865670391404911

theorem tailTrace_2408808 : CollatzResearch.WordTrace tailWord_2408808 prefixEnd_2408808 274861401865670391404911 := by
  unfold tailWord_2408808
  simp only [CollatzResearch.WordTrace]
  refine ⟨43928222728653741249473539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58570963638204988332631385 43928222728653741249473539)
  ·
    refine ⟨65892334092980611874210309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43928222728653741249473539 65892334092980611874210309)
    ·
      refine ⟨12354812642433864726414433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 65892334092980611874210309 12354812642433864726414433)
      ·
        refine ⟨9266109481825398544810825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12354812642433864726414433 9266109481825398544810825)
        ·
          refine ⟨6949582111369048908608119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9266109481825398544810825 6949582111369048908608119)
          ·
            refine ⟨10424373167053573362912179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6949582111369048908608119 10424373167053573362912179)
            ·
              refine ⟨15636559750580360044368269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10424373167053573362912179 15636559750580360044368269)
              ·
                refine ⟨5863709906467635016638101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15636559750580360044368269 5863709906467635016638101)
                ·
                  refine ⟨274861401865670391404911, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5863709906467635016638101 274861401865670391404911)
                  ·
                    rfl

theorem cell22_2408808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 1, 3, 6].length) (baseStart_2408808 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2408808 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2408808 prefixEnd_2408808 := by exact prefixLift 2408808
  have htrace : WordTrace (prefixWord ++ tailWord_2408808) baseStart_2408808 baseEnd_2408808 := by
    simpa [prefixWord, tailWord_2408808, baseEnd_2408808] using wordTrace_append hprefix tailTrace_2408808
  have hstable : (prefixWord ++ tailWord_2408808).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2408808).length < 2 ^ (prefixWord ++ tailWord_2408808).sum := by decide
  have hdescent : baseEnd_2408808 < baseStart_2408808 := by decide
  rcases family_descends (prefixWord ++ tailWord_2408808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2408928 : List Nat := [2, 1, 1, 3, 1, 1, 3, 1, 5, 4]
def baseStart_2408928 : Nat := 118140960795 + 2408928 * 2 ^ 59
def prefixEnd_2408928 : Nat := 4983230072969 + 3 ^ 40 * 2408928 * 2
def baseEnd_2408928 : Nat := 824625284049370861214365

theorem tailTrace_2408928 : CollatzResearch.WordTrace tailWord_2408928 prefixEnd_2408928 824625284049370861214365 := by
  unfold tailWord_2408928
  simp only [CollatzResearch.WordTrace]
  refine ⟨43930411108436371496657719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58573881477915161995543625 43930411108436371496657719)
  ·
    refine ⟨65895616662654557244986579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43930411108436371496657719 65895616662654557244986579)
    ·
      refine ⟨98843424993981835867479869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65895616662654557244986579 98843424993981835867479869)
      ·
        refine ⟨37066284372743188450304951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 98843424993981835867479869 37066284372743188450304951)
        ·
          refine ⟨55599426559114782675457427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37066284372743188450304951 55599426559114782675457427)
          ·
            refine ⟨83399139838672174013186141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55599426559114782675457427 83399139838672174013186141)
            ·
              refine ⟨31274677439502065254944803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 83399139838672174013186141 31274677439502065254944803)
              ·
                refine ⟨46912016159253097882417205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31274677439502065254944803 46912016159253097882417205)
                ·
                  refine ⟨4398001514929977926476613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 46912016159253097882417205 4398001514929977926476613)
                  ·
                    refine ⟨824625284049370861214365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4398001514929977926476613 824625284049370861214365)
                    ·
                      rfl

theorem cell22_2408928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 3, 1, 5, 4].length) (baseStart_2408928 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2408928 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2408928 prefixEnd_2408928 := by exact prefixLift 2408928
  have htrace : WordTrace (prefixWord ++ tailWord_2408928) baseStart_2408928 baseEnd_2408928 := by
    simpa [prefixWord, tailWord_2408928, baseEnd_2408928] using wordTrace_append hprefix tailTrace_2408928
  have hstable : (prefixWord ++ tailWord_2408928).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2408928).length < 2 ^ (prefixWord ++ tailWord_2408928).sum := by decide
  have hdescent : baseEnd_2408928 < baseStart_2408928 := by decide
  rcases family_descends (prefixWord ++ tailWord_2408928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2408945 : List Nat := [1, 2, 2, 2, 3, 1, 2, 4, 1, 4]
def baseStart_2408945 : Nat := 118140960795 + 2408945 * 2 ^ 59
def prefixEnd_2408945 : Nat := 4983230072969 + 3 ^ 40 * 2408945 * 2
def baseEnd_2408945 : Nat := 824631103496788483539313

theorem tailTrace_2408945 : CollatzResearch.WordTrace tailWord_2408945 prefixEnd_2408945 824631103496788483539313 := by
  unfold tailWord_2408945
  simp only [CollatzResearch.WordTrace]
  refine ⟨87861442257811154896684289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58574294838540769931122859 87861442257811154896684289)
  ·
    refine ⟨65896081693358366172513217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87861442257811154896684289 65896081693358366172513217)
    ·
      refine ⟨49422061270018774629384913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65896081693358366172513217 49422061270018774629384913)
      ·
        refine ⟨37066545952514080972038685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49422061270018774629384913 37066545952514080972038685)
        ·
          refine ⟨13899954732192780364514507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37066545952514080972038685 13899954732192780364514507)
          ·
            refine ⟨20849932098289170546771761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13899954732192780364514507 20849932098289170546771761)
            ·
              refine ⟨15637449073716877910078821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20849932098289170546771761 15637449073716877910078821)
              ·
                refine ⟨2932021701321914608139779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15637449073716877910078821 2932021701321914608139779)
                ·
                  refine ⟨4398032551982871912209669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2932021701321914608139779 4398032551982871912209669)
                  ·
                    refine ⟨824631103496788483539313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4398032551982871912209669 824631103496788483539313)
                    ·
                      rfl

theorem cell22_2408945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 2, 4, 1, 4].length) (baseStart_2408945 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2408945 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2408945 prefixEnd_2408945 := by exact prefixLift 2408945
  have htrace : WordTrace (prefixWord ++ tailWord_2408945) baseStart_2408945 baseEnd_2408945 := by
    simpa [prefixWord, tailWord_2408945, baseEnd_2408945] using wordTrace_append hprefix tailTrace_2408945
  have hstable : (prefixWord ++ tailWord_2408945).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2408945).length < 2 ^ (prefixWord ++ tailWord_2408945).sum := by decide
  have hdescent : baseEnd_2408945 < baseStart_2408945 := by decide
  rcases family_descends (prefixWord ++ tailWord_2408945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2408966 : List Nat := [6, 2, 1, 1, 1, 1, 3, 2, 5]
def baseStart_2408966 : Nat := 118140960795 + 2408966 * 2 ^ 59
def prefixEnd_2408966 : Nat := 4983230072969 + 3 ^ 40 * 2408966 * 2
def baseEnd_2408966 : Nat := 274879430741983809588083

theorem tailTrace_2408966 : CollatzResearch.WordTrace tailWord_2408966 prefixEnd_2408966 274879430741983809588083 := by
  unfold tailWord_2408966
  simp only [CollatzResearch.WordTrace]
  refine ⟨2745694005960471108849961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 58574805460490050322132501 2745694005960471108849961)
  ·
    refine ⟨2059270504470353331637471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2745694005960471108849961 2059270504470353331637471)
    ·
      refine ⟨3088905756705529997456207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2059270504470353331637471 3088905756705529997456207)
      ·
        refine ⟨4633358635058294996184311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3088905756705529997456207 4633358635058294996184311)
        ·
          refine ⟨6950037952587442494276467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4633358635058294996184311 6950037952587442494276467)
          ·
            refine ⟨10425056928881163741414701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6950037952587442494276467 10425056928881163741414701)
            ·
              refine ⟨3909396348330436403030513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10425056928881163741414701 3909396348330436403030513)
              ·
                refine ⟨2932047261247827302272885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3909396348330436403030513 2932047261247827302272885)
                ·
                  refine ⟨274879430741983809588083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2932047261247827302272885 274879430741983809588083)
                  ·
                    rfl

theorem cell22_2408966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 3, 2, 5].length) (baseStart_2408966 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2408966 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2408966 prefixEnd_2408966 := by exact prefixLift 2408966
  have htrace : WordTrace (prefixWord ++ tailWord_2408966) baseStart_2408966 baseEnd_2408966 := by
    simpa [prefixWord, tailWord_2408966, baseEnd_2408966] using wordTrace_append hprefix tailTrace_2408966
  have hstable : (prefixWord ++ tailWord_2408966).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2408966).length < 2 ^ (prefixWord ++ tailWord_2408966).sum := by decide
  have hdescent : baseEnd_2408966 < baseStart_2408966 := by decide
  rcases family_descends (prefixWord ++ tailWord_2408966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2409028 : List Nat := [2, 3, 5, 1, 2, 1, 1, 1, 6]
def baseStart_2409028 : Nat := 118140960795 + 2409028 * 2 ^ 59
def prefixEnd_2409028 : Nat := 4983230072969 + 3 ^ 40 * 2409028 * 2
def baseEnd_2409028 : Nat := 274886505364334644571353

theorem tailTrace_2409028 : CollatzResearch.WordTrace tailWord_2409028 prefixEnd_2409028 274886505364334644571353 := by
  unfold tailWord_2409028
  simp only [CollatzResearch.WordTrace]
  refine ⟨43932234758255230035977869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58576313011006973381303825 43932234758255230035977869)
  ·
    refine ⟨16474588034345711263491701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43932234758255230035977869 16474588034345711263491701)
    ·
      refine ⟨1544492628219910430952347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 16474588034345711263491701 1544492628219910430952347)
      ·
        refine ⟨2316738942329865646428521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1544492628219910430952347 2316738942329865646428521)
        ·
          refine ⟨1737554206747399234821391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2316738942329865646428521 1737554206747399234821391)
          ·
            refine ⟨2606331310121098852232087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1737554206747399234821391 2606331310121098852232087)
            ·
              refine ⟨3909496965181648278348131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2606331310121098852232087 3909496965181648278348131)
              ·
                refine ⟨5864245447772472417522197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3909496965181648278348131 5864245447772472417522197)
                ·
                  refine ⟨274886505364334644571353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5864245447772472417522197 274886505364334644571353)
                  ·
                    rfl

theorem cell22_2409028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 2, 1, 1, 1, 6].length) (baseStart_2409028 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2409028 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2409028 prefixEnd_2409028 := by exact prefixLift 2409028
  have htrace : WordTrace (prefixWord ++ tailWord_2409028) baseStart_2409028 baseEnd_2409028 := by
    simpa [prefixWord, tailWord_2409028, baseEnd_2409028] using wordTrace_append hprefix tailTrace_2409028
  have hstable : (prefixWord ++ tailWord_2409028).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2409028).length < 2 ^ (prefixWord ++ tailWord_2409028).sum := by decide
  have hdescent : baseEnd_2409028 < baseStart_2409028 := by decide
  rcases family_descends (prefixWord ++ tailWord_2409028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2409095 : List Nat := [1, 1, 4, 2, 1, 2, 2, 3, 6]
def baseStart_2409095 : Nat := 118140960795 + 2409095 * 2 ^ 59
def prefixEnd_2409095 : Nat := 4983230072969 + 3 ^ 40 * 2409095 * 2
def baseEnd_2409095 : Nat := 274894150520746030762951

theorem tailTrace_2409095 : CollatzResearch.WordTrace tailWord_2409095 prefixEnd_2409095 274894150520746030762951 := by
  unfold tailWord_2409095
  simp only [CollatzResearch.WordTrace]
  refine ⟨87866913207267730514644739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58577942138178487009763159 87866913207267730514644739)
  ·
    refine ⟨131800369810901595771967109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87866913207267730514644739 131800369810901595771967109)
    ·
      refine ⟨24712569339544049207243833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 131800369810901595771967109 24712569339544049207243833)
      ·
        refine ⟨18534427004658036905432875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24712569339544049207243833 18534427004658036905432875)
        ·
          refine ⟨27801640506987055358149313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18534427004658036905432875 27801640506987055358149313)
          ·
            refine ⟨20851230380240291518611985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27801640506987055358149313 20851230380240291518611985)
            ·
              refine ⟨15638422785180218638958989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20851230380240291518611985 15638422785180218638958989)
              ·
                refine ⟨5864408544442581989609621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15638422785180218638958989 5864408544442581989609621)
                ·
                  refine ⟨274894150520746030762951, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5864408544442581989609621 274894150520746030762951)
                  ·
                    rfl

theorem cell22_2409095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 2, 3, 6].length) (baseStart_2409095 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2409095 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2409095 prefixEnd_2409095 := by exact prefixLift 2409095
  have htrace : WordTrace (prefixWord ++ tailWord_2409095) baseStart_2409095 baseEnd_2409095 := by
    simpa [prefixWord, tailWord_2409095, baseEnd_2409095] using wordTrace_append hprefix tailTrace_2409095
  have hstable : (prefixWord ++ tailWord_2409095).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2409095).length < 2 ^ (prefixWord ++ tailWord_2409095).sum := by decide
  have hdescent : baseEnd_2409095 < baseStart_2409095 := by decide
  rcases family_descends (prefixWord ++ tailWord_2409095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2409202 : List Nat := [3, 2, 1, 3, 1, 2, 2, 1, 7]
def baseStart_2409202 : Nat := 118140960795 + 2409202 * 2 ^ 59
def prefixEnd_2409202 : Nat := 4983230072969 + 3 ^ 40 * 2409202 * 2
def baseEnd_2409202 : Nat := 274906359949641826621175

theorem tailTrace_2409202 : CollatzResearch.WordTrace tailWord_2409202 prefixEnd_2409202 274906359949641826621175 := by
  unfold tailWord_2409202
  simp only [CollatzResearch.WordTrace]
  refine ⟨21967703954470021947197465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58580543878586725192526573 21967703954470021947197465)
  ·
    refine ⟨16475777965852516460398099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21967703954470021947197465 16475777965852516460398099)
    ·
      refine ⟨24713666948778774690597149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16475777965852516460398099 24713666948778774690597149)
      ·
        refine ⟨9267625105792040508973931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24713666948778774690597149 9267625105792040508973931)
        ·
          refine ⟨13901437658688060763460897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9267625105792040508973931 13901437658688060763460897)
          ·
            refine ⟨10426078244016045572595673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13901437658688060763460897 10426078244016045572595673)
            ·
              refine ⟨7819558683012034179446755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10426078244016045572595673 7819558683012034179446755)
              ·
                refine ⟨11729338024518051269170133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7819558683012034179446755 11729338024518051269170133)
                ·
                  refine ⟨274906359949641826621175, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11729338024518051269170133 274906359949641826621175)
                  ·
                    rfl

theorem cell22_2409202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 2, 1, 7].length) (baseStart_2409202 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2409202 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2409202 prefixEnd_2409202 := by exact prefixLift 2409202
  have htrace : WordTrace (prefixWord ++ tailWord_2409202) baseStart_2409202 baseEnd_2409202 := by
    simpa [prefixWord, tailWord_2409202, baseEnd_2409202] using wordTrace_append hprefix tailTrace_2409202
  have hstable : (prefixWord ++ tailWord_2409202).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2409202).length < 2 ^ (prefixWord ++ tailWord_2409202).sum := by decide
  have hdescent : baseEnd_2409202 < baseStart_2409202 := by decide
  rcases family_descends (prefixWord ++ tailWord_2409202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2409215 : List Nat := [1, 1, 2, 2, 1, 3, 1, 1, 2, 8]
def baseStart_2409215 : Nat := 118140960795 + 2409215 * 2 ^ 59
def prefixEnd_2409215 : Nat := 4983230072969 + 3 ^ 40 * 2409215 * 2
def baseEnd_2409215 : Nat := 824723530014597779288485

theorem tailTrace_2409215 : CollatzResearch.WordTrace tailWord_2409215 prefixEnd_2409215 824723530014597779288485 := by
  unfold tailWord_2409215
  simp only [CollatzResearch.WordTrace]
  refine ⟨87871289966832991009013099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58580859977888660672675399 87871289966832991009013099)
  ·
    refine ⟨131806934950249486513519649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87871289966832991009013099 131806934950249486513519649)
    ·
      refine ⟨98855201212687114885139737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 131806934950249486513519649 98855201212687114885139737)
      ·
        refine ⟨74141400909515336163854803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 98855201212687114885139737 74141400909515336163854803)
        ·
          refine ⟨111212101364273004245782205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74141400909515336163854803 111212101364273004245782205)
          ·
            refine ⟨41704538011602376592168327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 111212101364273004245782205 41704538011602376592168327)
            ·
              refine ⟨62556807017403564888252491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41704538011602376592168327 62556807017403564888252491)
              ·
                refine ⟨93835210526105347332378737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 62556807017403564888252491 93835210526105347332378737)
                ·
                  refine ⟨70376407894579010499284053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 93835210526105347332378737 70376407894579010499284053)
                  ·
                    refine ⟨824723530014597779288485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 70376407894579010499284053 824723530014597779288485)
                    ·
                      rfl

theorem cell22_2409215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 1, 2, 8].length) (baseStart_2409215 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2409215 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2409215 prefixEnd_2409215 := by exact prefixLift 2409215
  have htrace : WordTrace (prefixWord ++ tailWord_2409215) baseStart_2409215 baseEnd_2409215 := by
    simpa [prefixWord, tailWord_2409215, baseEnd_2409215] using wordTrace_append hprefix tailTrace_2409215
  have hstable : (prefixWord ++ tailWord_2409215).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2409215).length < 2 ^ (prefixWord ++ tailWord_2409215).sum := by decide
  have hdescent : baseEnd_2409215 < baseStart_2409215 := by decide
  rcases family_descends (prefixWord ++ tailWord_2409215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2409279 : List Nat := [1, 1, 2, 2, 5, 2, 2, 1, 1, 5]
def baseStart_2409279 : Nat := 118140960795 + 2409279 * 2 ^ 59
def prefixEnd_2409279 : Nat := 4983230072969 + 3 ^ 40 * 2409279 * 2
def baseEnd_2409279 : Nat := 824745438522522945688289

theorem tailTrace_2409279 : CollatzResearch.WordTrace tailWord_2409279 prefixEnd_2409279 824745438522522945688289 := by
  unfold tailWord_2409279
  simp only [CollatzResearch.WordTrace]
  refine ⟨87873624238601129939342891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58582416159067419959561927 87873624238601129939342891)
  ·
    refine ⟨131810436357901694909014337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87873624238601129939342891 131810436357901694909014337)
    ·
      refine ⟨98857827268426271181760753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 131810436357901694909014337 98857827268426271181760753)
      ·
        refine ⟨74143370451319703386320565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 98857827268426271181760753 74143370451319703386320565)
        ·
          refine ⟨6950940979811222192467553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 74143370451319703386320565 6950940979811222192467553)
          ·
            refine ⟨5213205734858416644350665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6950940979811222192467553 5213205734858416644350665)
            ·
              refine ⟨3909904301143812483262999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5213205734858416644350665 3909904301143812483262999)
              ·
                refine ⟨5864856451715718724894499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3909904301143812483262999 5864856451715718724894499)
                ·
                  refine ⟨8797284677573578087341749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5864856451715718724894499 8797284677573578087341749)
                  ·
                    refine ⟨824745438522522945688289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8797284677573578087341749 824745438522522945688289)
                    ·
                      rfl

theorem cell22_2409279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 2, 2, 1, 1, 5].length) (baseStart_2409279 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2409279 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2409279 prefixEnd_2409279 := by exact prefixLift 2409279
  have htrace : WordTrace (prefixWord ++ tailWord_2409279) baseStart_2409279 baseEnd_2409279 := by
    simpa [prefixWord, tailWord_2409279, baseEnd_2409279] using wordTrace_append hprefix tailTrace_2409279
  have hstable : (prefixWord ++ tailWord_2409279).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2409279).length < 2 ^ (prefixWord ++ tailWord_2409279).sum := by decide
  have hdescent : baseEnd_2409279 < baseStart_2409279 := by decide
  rcases family_descends (prefixWord ++ tailWord_2409279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2409281 : List Nat := [1, 2, 5, 3, 1, 1, 1, 2, 6]
def baseStart_2409281 : Nat := 118140960795 + 2409281 * 2 ^ 59
def prefixEnd_2409281 : Nat := 4983230072969 + 3 ^ 40 * 2409281 * 2
def baseEnd_2409281 : Nat := 274915374387798535712761

theorem tailTrace_2409281 : CollatzResearch.WordTrace tailWord_2409281 prefixEnd_2409281 274915374387798535712761 := by
  unfold tailWord_2409281
  simp only [CollatzResearch.WordTrace]
  refine ⟨87873697184593884280915697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58582464789729256187277131 87873697184593884280915697)
  ·
    refine ⟨65905272888445413210686773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87873697184593884280915697 65905272888445413210686773)
    ·
      refine ⟨6178619333291757488501885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 65905272888445413210686773 6178619333291757488501885)
      ·
        refine ⟨2316982249984409058188207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6178619333291757488501885 2316982249984409058188207)
        ·
          refine ⟨3475473374976613587282311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2316982249984409058188207 3475473374976613587282311)
          ·
            refine ⟨5213210062464920380923467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3475473374976613587282311 5213210062464920380923467)
            ·
              refine ⟨7819815093697380571385201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5213210062464920380923467 7819815093697380571385201)
              ·
                refine ⟨5864861320273035428538901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7819815093697380571385201 5864861320273035428538901)
                ·
                  refine ⟨274915374387798535712761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5864861320273035428538901 274915374387798535712761)
                  ·
                    rfl

theorem cell22_2409281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 1, 1, 2, 6].length) (baseStart_2409281 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2409281 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2409281 prefixEnd_2409281 := by exact prefixLift 2409281
  have htrace : WordTrace (prefixWord ++ tailWord_2409281) baseStart_2409281 baseEnd_2409281 := by
    simpa [prefixWord, tailWord_2409281, baseEnd_2409281] using wordTrace_append hprefix tailTrace_2409281
  have hstable : (prefixWord ++ tailWord_2409281).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2409281).length < 2 ^ (prefixWord ++ tailWord_2409281).sum := by decide
  have hdescent : baseEnd_2409281 < baseStart_2409281 := by decide
  rcases family_descends (prefixWord ++ tailWord_2409281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2409300 : List Nat := [2, 4, 1, 1, 5, 1, 2, 1, 1, 4]
def baseStart_2409300 : Nat := 118140960795 + 2409300 * 2 ^ 59
def prefixEnd_2409300 : Nat := 4983230072969 + 3 ^ 40 * 2409300 * 2
def baseEnd_2409300 : Nat := 824752627251685890913225

theorem tailTrace_2409300 : CollatzResearch.WordTrace tailWord_2409300 prefixEnd_2409300 824752627251685890913225 := by
  unfold tailWord_2409300
  simp only [CollatzResearch.WordTrace]
  refine ⟨43937195085762525262928677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58582926781016700350571569 43937195085762525262928677)
  ·
    refine ⟨8238224078580473486799127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 43937195085762525262928677 8238224078580473486799127)
    ·
      refine ⟨12357336117870710230198691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8238224078580473486799127 12357336117870710230198691)
      ·
        refine ⟨18536004176806065345298037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12357336117870710230198691 18536004176806065345298037)
        ·
          refine ⟨1737750391575568626121691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 18536004176806065345298037 1737750391575568626121691)
          ·
            refine ⟨2606625587363352939182537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1737750391575568626121691 2606625587363352939182537)
            ·
              refine ⟨1954969190522514704386903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2606625587363352939182537 1954969190522514704386903)
              ·
                refine ⟨2932453785783772056580355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1954969190522514704386903 2932453785783772056580355)
                ·
                  refine ⟨4398680678675658084870533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2932453785783772056580355 4398680678675658084870533)
                  ·
                    refine ⟨824752627251685890913225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4398680678675658084870533 824752627251685890913225)
                    ·
                      rfl

theorem cell22_2409300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 5, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 5, 1, 2, 1, 1, 4].length) (baseStart_2409300 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2409300 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2409300 prefixEnd_2409300 := by exact prefixLift 2409300
  have htrace : WordTrace (prefixWord ++ tailWord_2409300) baseStart_2409300 baseEnd_2409300 := by
    simpa [prefixWord, tailWord_2409300, baseEnd_2409300] using wordTrace_append hprefix tailTrace_2409300
  have hstable : (prefixWord ++ tailWord_2409300).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2409300).length < 2 ^ (prefixWord ++ tailWord_2409300).sum := by decide
  have hdescent : baseEnd_2409300 < baseStart_2409300 := by decide
  rcases family_descends (prefixWord ++ tailWord_2409300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2409354 : List Nat := [3, 1, 2, 4, 1, 1, 1, 2, 7]
def baseStart_2409354 : Nat := 118140960795 + 2409354 * 2 ^ 59
def prefixEnd_2409354 : Nat := 4983230072969 + 3 ^ 40 * 2409354 * 2
def baseEnd_2409354 : Nat := 274923704185082583354353

theorem tailTrace_2409354 : CollatzResearch.WordTrace tailWord_2409354 prefixEnd_2409354 274923704185082583354353 := by
  unfold tailWord_2409354
  simp only [CollatzResearch.WordTrace]
  refine ⟨21969089928332354437080779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58584239808886278498882077 21969089928332354437080779)
  ·
    refine ⟨32953634892498531655621169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21969089928332354437080779 32953634892498531655621169)
    ·
      refine ⟨24715226169373898741715877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32953634892498531655621169 24715226169373898741715877)
      ·
        refine ⟨4634104906757606014071727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 24715226169373898741715877 4634104906757606014071727)
        ·
          refine ⟨6951157360136409021107591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4634104906757606014071727 6951157360136409021107591)
          ·
            refine ⟨10426736040204613531661387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6951157360136409021107591 10426736040204613531661387)
            ·
              refine ⟨15640104060306920297492081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10426736040204613531661387 15640104060306920297492081)
              ·
                refine ⟨11730078045230190223119061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15640104060306920297492081 11730078045230190223119061)
                ·
                  refine ⟨274923704185082583354353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11730078045230190223119061 274923704185082583354353)
                  ·
                    rfl

theorem cell22_2409354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 1, 2, 7].length) (baseStart_2409354 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2409354 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2409354 prefixEnd_2409354 := by exact prefixLift 2409354
  have htrace : WordTrace (prefixWord ++ tailWord_2409354) baseStart_2409354 baseEnd_2409354 := by
    simpa [prefixWord, tailWord_2409354, baseEnd_2409354] using wordTrace_append hprefix tailTrace_2409354
  have hstable : (prefixWord ++ tailWord_2409354).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2409354).length < 2 ^ (prefixWord ++ tailWord_2409354).sum := by decide
  have hdescent : baseEnd_2409354 < baseStart_2409354 := by decide
  rcases family_descends (prefixWord ++ tailWord_2409354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2409375 : List Nat := [1, 1, 2, 5, 2, 2, 3, 2, 1, 3]
def baseStart_2409375 : Nat := 118140960795 + 2409375 * 2 ^ 59
def prefixEnd_2409375 : Nat := 4983230072969 + 3 ^ 40 * 2409375 * 2
def baseEnd_2409375 : Nat := 824778301284410695287995

theorem tailTrace_2409375 : CollatzResearch.WordTrace tailWord_2409375 prefixEnd_2409375 824778301284410695287995 := by
  unfold tailWord_2409375
  simp only [CollatzResearch.WordTrace]
  refine ⟨87877125646253338334837579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58584750430835558889891719 87877125646253338334837579)
  ·
    refine ⟨131815688469380007502256369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87877125646253338334837579 131815688469380007502256369)
    ·
      refine ⟨98861766352035005626692277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 131815688469380007502256369 98861766352035005626692277)
      ·
        refine ⟨9268290595503281777502401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 98861766352035005626692277 9268290595503281777502401)
        ·
          refine ⟨6951217946627461333126801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9268290595503281777502401 6951217946627461333126801)
          ·
            refine ⟨5213413459970595999845101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6951217946627461333126801 5213413459970595999845101)
            ·
              refine ⟨1955030047488973499941913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5213413459970595999845101 1955030047488973499941913)
              ·
                refine ⟨1466272535616730124956435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1955030047488973499941913 1466272535616730124956435)
                ·
                  refine ⟨2199408803425095187434653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1466272535616730124956435 2199408803425095187434653)
                  ·
                    refine ⟨824778301284410695287995, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2199408803425095187434653 824778301284410695287995)
                    ·
                      rfl

theorem cell22_2409375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 2, 3, 2, 1, 3].length) (baseStart_2409375 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2409375 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2409375 prefixEnd_2409375 := by exact prefixLift 2409375
  have htrace : WordTrace (prefixWord ++ tailWord_2409375) baseStart_2409375 baseEnd_2409375 := by
    simpa [prefixWord, tailWord_2409375, baseEnd_2409375] using wordTrace_append hprefix tailTrace_2409375
  have hstable : (prefixWord ++ tailWord_2409375).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2409375).length < 2 ^ (prefixWord ++ tailWord_2409375).sum := by decide
  have hdescent : baseEnd_2409375 < baseStart_2409375 := by decide
  rcases family_descends (prefixWord ++ tailWord_2409375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2409401 : List Nat := [1, 2, 1, 4, 2, 2, 3, 2, 1, 4]
def baseStart_2409401 : Nat := 118140960795 + 2409401 * 2 ^ 59
def prefixEnd_2409401 : Nat := 4983230072969 + 3 ^ 40 * 2409401 * 2
def baseEnd_2409401 : Nat := 824787201615755294137915

theorem tailTrace_2409401 : CollatzResearch.WordTrace tailWord_2409401 prefixEnd_2409401 824787201615755294137915 := by
  unfold tailWord_2409401
  simp only [CollatzResearch.WordTrace]
  refine ⟨87878073944159144775284057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58585382629439429850189371 87878073944159144775284057)
  ·
    refine ⟨65908555458119358581463043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87878073944159144775284057 65908555458119358581463043)
    ·
      refine ⟨98862833187179037872194565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65908555458119358581463043 98862833187179037872194565)
      ·
        refine ⟨18536781222596069601036481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 98862833187179037872194565 18536781222596069601036481)
        ·
          refine ⟨13902585916947052200777361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18536781222596069601036481 13902585916947052200777361)
          ·
            refine ⟨10426939437710289150583021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13902585916947052200777361 10426939437710289150583021)
            ·
              refine ⟨3910102289141358431468633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10426939437710289150583021 3910102289141358431468633)
              ·
                refine ⟨2932576716856018823601475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3910102289141358431468633 2932576716856018823601475)
                ·
                  refine ⟨4398865075284028235402213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2932576716856018823601475 4398865075284028235402213)
                  ·
                    refine ⟨824787201615755294137915, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4398865075284028235402213 824787201615755294137915)
                    ·
                      rfl

theorem cell22_2409401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 3, 2, 1, 4].length) (baseStart_2409401 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2409401 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2409401 prefixEnd_2409401 := by exact prefixLift 2409401
  have htrace : WordTrace (prefixWord ++ tailWord_2409401) baseStart_2409401 baseEnd_2409401 := by
    simpa [prefixWord, tailWord_2409401, baseEnd_2409401] using wordTrace_append hprefix tailTrace_2409401
  have hstable : (prefixWord ++ tailWord_2409401).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2409401).length < 2 ^ (prefixWord ++ tailWord_2409401).sum := by decide
  have hdescent : baseEnd_2409401 < baseStart_2409401 := by decide
  rcases family_descends (prefixWord ++ tailWord_2409401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2409433 : List Nat := [1, 2, 1, 2, 5, 1, 4, 2, 4]
def baseStart_2409433 : Nat := 118140960795 + 2409433 * 2 ^ 59
def prefixEnd_2409433 : Nat := 4983230072969 + 3 ^ 40 * 2409433 * 2
def baseEnd_2409433 : Nat := 274932718623239292445939

theorem tailTrace_2409433 : CollatzResearch.WordTrace tailWord_2409433 prefixEnd_2409433 274932718623239292445939 := by
  unfold tailWord_2409433
  simp only [CollatzResearch.WordTrace]
  refine ⟨87879241080043214240448953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58586160720028809493632635 87879241080043214240448953)
  ·
    refine ⟨65909430810032410680336715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87879241080043214240448953 65909430810032410680336715)
    ·
      refine ⟨98864146215048616020505073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65909430810032410680336715 98864146215048616020505073)
      ·
        refine ⟨74148109661286462015378805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 98864146215048616020505073 74148109661286462015378805)
        ·
          refine ⟨6951385280745605813941763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 74148109661286462015378805 6951385280745605813941763)
          ·
            refine ⟨10427077921118408720912645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6951385280745605813941763 10427077921118408720912645)
            ·
              refine ⟨1955077110209701635171121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10427077921118408720912645 1955077110209701635171121)
              ·
                refine ⟨1466307832657276226378341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1955077110209701635171121 1466307832657276226378341)
                ·
                  refine ⟨274932718623239292445939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1466307832657276226378341 274932718623239292445939)
                  ·
                    rfl

theorem cell22_2409433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 4, 2, 4].length) (baseStart_2409433 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2409433 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2409433 prefixEnd_2409433 := by exact prefixLift 2409433
  have htrace : WordTrace (prefixWord ++ tailWord_2409433) baseStart_2409433 baseEnd_2409433 := by
    simpa [prefixWord, tailWord_2409433, baseEnd_2409433] using wordTrace_append hprefix tailTrace_2409433
  have hstable : (prefixWord ++ tailWord_2409433).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2409433).length < 2 ^ (prefixWord ++ tailWord_2409433).sum := by decide
  have hdescent : baseEnd_2409433 < baseStart_2409433 := by decide
  rcases family_descends (prefixWord ++ tailWord_2409433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2409493 : List Nat := [1, 3, 2, 1, 4, 2, 2, 1, 3, 3]
def baseStart_2409493 : Nat := 118140960795 + 2409493 * 2 ^ 59
def prefixEnd_2409493 : Nat := 4983230072969 + 3 ^ 40 * 2409493 * 2
def baseEnd_2409493 : Nat := 824818695095897720837633

theorem tailTrace_2409493 : CollatzResearch.WordTrace tailWord_2409493 prefixEnd_2409493 824818695095897720837633 := by
  unfold tailWord_2409493
  simp only [CollatzResearch.WordTrace]
  refine ⟨87881429459825844487633133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58587619639883896325088755 87881429459825844487633133)
  ·
    refine ⟨32955536047434691682862425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 87881429459825844487633133 32955536047434691682862425)
    ·
      refine ⟨24716652035576018762146819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32955536047434691682862425 24716652035576018762146819)
      ·
        refine ⟨37074978053364028143220229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24716652035576018762146819 37074978053364028143220229)
        ·
          refine ⟨6951558385005755276853793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 37074978053364028143220229 6951558385005755276853793)
          ·
            refine ⟨5213668788754316457640345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6951558385005755276853793 5213668788754316457640345)
            ·
              refine ⟨3910251591565737343230259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5213668788754316457640345 3910251591565737343230259)
              ·
                refine ⟨5865377387348606014845389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3910251591565737343230259 5865377387348606014845389)
                ·
                  refine ⟨2199516520255727255567021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5865377387348606014845389 2199516520255727255567021)
                  ·
                    refine ⟨824818695095897720837633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2199516520255727255567021 824818695095897720837633)
                    ·
                      rfl

theorem cell22_2409493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 2, 2, 1, 3, 3].length) (baseStart_2409493 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2409493 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2409493 prefixEnd_2409493 := by exact prefixLift 2409493
  have htrace : WordTrace (prefixWord ++ tailWord_2409493) baseStart_2409493 baseEnd_2409493 := by
    simpa [prefixWord, tailWord_2409493, baseEnd_2409493] using wordTrace_append hprefix tailTrace_2409493
  have hstable : (prefixWord ++ tailWord_2409493).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2409493).length < 2 ^ (prefixWord ++ tailWord_2409493).sum := by decide
  have hdescent : baseEnd_2409493 < baseStart_2409493 := by decide
  rcases family_descends (prefixWord ++ tailWord_2409493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2409519 : List Nat := [1, 1, 2, 1, 2, 1, 1, 2, 7, 4]
def baseStart_2409519 : Nat := 118140960795 + 2409519 * 2 ^ 59
def prefixEnd_2409519 : Nat := 4983230072969 + 3 ^ 40 * 2409519 * 2
def baseEnd_2409519 : Nat := 824827595427242319687553

theorem tailTrace_2409519 : CollatzResearch.WordTrace tailWord_2409519 prefixEnd_2409519 824827595427242319687553 := by
  unfold tailWord_2409519
  simp only [CollatzResearch.WordTrace]
  refine ⟨87882377757731650928079611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58588251838487767285386407 87882377757731650928079611)
  ·
    refine ⟨131823566636597476392119417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87882377757731650928079611 131823566636597476392119417)
    ·
      refine ⟨98867674977448107294089563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 131823566636597476392119417 98867674977448107294089563)
      ·
        refine ⟨148301512466172160941134345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98867674977448107294089563 148301512466172160941134345)
        ·
          refine ⟨111226134349629120705850759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 148301512466172160941134345 111226134349629120705850759)
          ·
            refine ⟨166839201524443681058776139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 111226134349629120705850759 166839201524443681058776139)
            ·
              refine ⟨250258802286665521588164209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 166839201524443681058776139 250258802286665521588164209)
              ·
                refine ⟨187694101714999141191123157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 250258802286665521588164209 187694101714999141191123157)
                ·
                  refine ⟨4399080508945292371666949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 187694101714999141191123157 4399080508945292371666949)
                  ·
                    refine ⟨824827595427242319687553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4399080508945292371666949 824827595427242319687553)
                    ·
                      rfl

theorem cell22_2409519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 2, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 2, 7, 4].length) (baseStart_2409519 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2409519 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2409519 prefixEnd_2409519 := by exact prefixLift 2409519
  have htrace : WordTrace (prefixWord ++ tailWord_2409519) baseStart_2409519 baseEnd_2409519 := by
    simpa [prefixWord, tailWord_2409519, baseEnd_2409519] using wordTrace_append hprefix tailTrace_2409519
  have hstable : (prefixWord ++ tailWord_2409519).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2409519).length < 2 ^ (prefixWord ++ tailWord_2409519).sum := by decide
  have hdescent : baseEnd_2409519 < baseStart_2409519 := by decide
  rcases family_descends (prefixWord ++ tailWord_2409519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2409536 : List Nat := [2, 1, 1, 2, 2, 3, 1, 5, 1, 4]
def baseStart_2409536 : Nat := 118140960795 + 2409536 * 2 ^ 59
def prefixEnd_2409536 : Nat := 4983230072969 + 3 ^ 40 * 2409536 * 2
def baseEnd_2409536 : Nat := 824833414874659942012501

theorem tailTrace_2409536 : CollatzResearch.WordTrace tailWord_2409536 prefixEnd_2409536 824833414874659942012501 := by
  unfold tailWord_2409536
  simp only [CollatzResearch.WordTrace]
  refine ⟨43941498899335031415724231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58588665199113375220965641 43941498899335031415724231)
  ·
    refine ⟨65912248349002547123586347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43941498899335031415724231 65912248349002547123586347)
    ·
      refine ⟨98868372523503820685379521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65912248349002547123586347 98868372523503820685379521)
      ·
        refine ⟨74151279392627865514034641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 98868372523503820685379521 74151279392627865514034641)
        ·
          refine ⟨55613459544470899135525981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 74151279392627865514034641 55613459544470899135525981)
          ·
            refine ⟨20855047329176587175822243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 55613459544470899135525981 20855047329176587175822243)
            ·
              refine ⟨31282570993764880763733365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20855047329176587175822243 31282570993764880763733365)
              ·
                refine ⟨2932741030665457571600003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 31282570993764880763733365 2932741030665457571600003)
                ·
                  refine ⟨4399111545998186357400005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2932741030665457571600003 4399111545998186357400005)
                  ·
                    refine ⟨824833414874659942012501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4399111545998186357400005 824833414874659942012501)
                    ·
                      rfl

theorem cell22_2409536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 1, 5, 1, 4].length) (baseStart_2409536 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2409536 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2409536 prefixEnd_2409536 := by exact prefixLift 2409536
  have htrace : WordTrace (prefixWord ++ tailWord_2409536) baseStart_2409536 baseEnd_2409536 := by
    simpa [prefixWord, tailWord_2409536, baseEnd_2409536] using wordTrace_append hprefix tailTrace_2409536
  have hstable : (prefixWord ++ tailWord_2409536).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2409536).length < 2 ^ (prefixWord ++ tailWord_2409536).sum := by decide
  have hdescent : baseEnd_2409536 < baseStart_2409536 := by decide
  rcases family_descends (prefixWord ++ tailWord_2409536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2409570 : List Nat := [3, 3, 2, 2, 1, 1, 3, 2, 1, 4]
def baseStart_2409570 : Nat := 118140960795 + 2409570 * 2 ^ 59
def prefixEnd_2409570 : Nat := 4983230072969 + 3 ^ 40 * 2409570 * 2
def baseEnd_2409570 : Nat := 824845053769495186662397

theorem tailTrace_2409570 : CollatzResearch.WordTrace tailWord_2409570 prefixEnd_2409570 824845053769495186662397 := by
  unfold tailWord_2409570
  simp only [CollatzResearch.WordTrace]
  refine ⟨21971059470136721659546541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58589491920364591092124109 21971059470136721659546541)
  ·
    refine ⟨8239147301301270622329953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21971059470136721659546541 8239147301301270622329953)
    ·
      refine ⟨6179360475975952966747465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8239147301301270622329953 6179360475975952966747465)
      ·
        refine ⟨4634520356981964725060599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6179360475975952966747465 4634520356981964725060599)
        ·
          refine ⟨6951780535472947087590899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4634520356981964725060599 6951780535472947087590899)
          ·
            refine ⟨10427670803209420631386349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6951780535472947087590899 10427670803209420631386349)
            ·
              refine ⟨3910376551203532736769881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10427670803209420631386349 3910376551203532736769881)
              ·
                refine ⟨2932782413402649552577411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3910376551203532736769881 2932782413402649552577411)
                ·
                  refine ⟨4399173620103974328866117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2932782413402649552577411 4399173620103974328866117)
                  ·
                    refine ⟨824845053769495186662397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4399173620103974328866117 824845053769495186662397)
                    ·
                      rfl

theorem cell22_2409570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 3, 2, 1, 4].length) (baseStart_2409570 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2409570 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2409570 prefixEnd_2409570 := by exact prefixLift 2409570
  have htrace : WordTrace (prefixWord ++ tailWord_2409570) baseStart_2409570 baseEnd_2409570 := by
    simpa [prefixWord, tailWord_2409570, baseEnd_2409570] using wordTrace_append hprefix tailTrace_2409570
  have hstable : (prefixWord ++ tailWord_2409570).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2409570).length < 2 ^ (prefixWord ++ tailWord_2409570).sum := by decide
  have hdescent : baseEnd_2409570 < baseStart_2409570 := by decide
  rcases family_descends (prefixWord ++ tailWord_2409570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2409611 : List Nat := [1, 1, 1, 1, 4, 1, 1, 2, 7, 3]
def baseStart_2409611 : Nat := 118140960795 + 2409611 * 2 ^ 59
def prefixEnd_2409611 : Nat := 4983230072969 + 3 ^ 40 * 2409611 * 2
def baseEnd_2409611 : Nat := 824859088907384746387271

theorem tailTrace_2409611 : CollatzResearch.WordTrace tailWord_2409611 prefixEnd_2409611 824859088907384746387271 := by
  unfold tailWord_2409611
  simp only [CollatzResearch.WordTrace]
  refine ⟨87885733273398350640428687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58590488848932233760285791 87885733273398350640428687)
  ·
    refine ⟨131828599910097525960643031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87885733273398350640428687 131828599910097525960643031)
    ·
      refine ⟨197742899865146288940964547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131828599910097525960643031 197742899865146288940964547)
      ·
        refine ⟨296614349797719433411446821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 197742899865146288940964547 296614349797719433411446821)
        ·
          refine ⟨55615190587072393764646279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 296614349797719433411446821 55615190587072393764646279)
          ·
            refine ⟨83422785880608590646969419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55615190587072393764646279 83422785880608590646969419)
            ·
              refine ⟨125134178820912885970454129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 83422785880608590646969419 125134178820912885970454129)
              ·
                refine ⟨93850634115684664477840597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 125134178820912885970454129 93850634115684664477840597)
                ·
                  refine ⟨2199624237086359323699389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 93850634115684664477840597 2199624237086359323699389)
                  ·
                    refine ⟨824859088907384746387271, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2199624237086359323699389 824859088907384746387271)
                    ·
                      rfl

theorem cell22_2409611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 2, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 2, 7, 3].length) (baseStart_2409611 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2409611 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2409611 prefixEnd_2409611 := by exact prefixLift 2409611
  have htrace : WordTrace (prefixWord ++ tailWord_2409611) baseStart_2409611 baseEnd_2409611 := by
    simpa [prefixWord, tailWord_2409611, baseEnd_2409611] using wordTrace_append hprefix tailTrace_2409611
  have hstable : (prefixWord ++ tailWord_2409611).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2409611).length < 2 ^ (prefixWord ++ tailWord_2409611).sum := by decide
  have hdescent : baseEnd_2409611 < baseStart_2409611 := by decide
  rcases family_descends (prefixWord ++ tailWord_2409611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2409628 : List Nat := [2, 2, 3, 2, 1, 2, 1, 1, 5, 3]
def baseStart_2409628 : Nat := 118140960795 + 2409628 * 2 ^ 59
def prefixEnd_2409628 : Nat := 4983230072969 + 3 ^ 40 * 2409628 * 2
def baseEnd_2409628 : Nat := 824864908354802368712219

theorem tailTrace_2409628 : CollatzResearch.WordTrace tailWord_2409628 prefixEnd_2409628 824864908354802368712219 := by
  unfold tailWord_2409628
  simp only [CollatzResearch.WordTrace]
  refine ⟨43943176657168381271898769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58590902209557841695865025 43943176657168381271898769)
  ·
    refine ⟨32957382492876285953924077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43943176657168381271898769 32957382492876285953924077)
    ·
      refine ⟨12359018434828607232721529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32957382492876285953924077 12359018434828607232721529)
      ·
        refine ⟨9269263826121455424541147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12359018434828607232721529 9269263826121455424541147)
        ·
          refine ⟨13903895739182183136811721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9269263826121455424541147 13903895739182183136811721)
          ·
            refine ⟨10427921804386637352608791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13903895739182183136811721 10427921804386637352608791)
            ·
              refine ⟨15641882706579956028913187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10427921804386637352608791 15641882706579956028913187)
              ·
                refine ⟨23462824059869934043369781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15641882706579956028913187 23462824059869934043369781)
                ·
                  refine ⟨2199639755612806316565917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 23462824059869934043369781 2199639755612806316565917)
                  ·
                    refine ⟨824864908354802368712219, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2199639755612806316565917 824864908354802368712219)
                    ·
                      rfl

theorem cell22_2409628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 1, 1, 5, 3].length) (baseStart_2409628 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2409628 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2409628 prefixEnd_2409628 := by exact prefixLift 2409628
  have htrace : WordTrace (prefixWord ++ tailWord_2409628) baseStart_2409628 baseEnd_2409628 := by
    simpa [prefixWord, tailWord_2409628, baseEnd_2409628] using wordTrace_append hprefix tailTrace_2409628
  have hstable : (prefixWord ++ tailWord_2409628).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2409628).length < 2 ^ (prefixWord ++ tailWord_2409628).sum := by decide
  have hdescent : baseEnd_2409628 < baseStart_2409628 := by decide
  rcases family_descends (prefixWord ++ tailWord_2409628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2409630 : List Nat := [4, 3, 1, 1, 2, 2, 3, 6]
def baseStart_2409630 : Nat := 118140960795 + 2409630 * 2 ^ 59
def prefixEnd_2409630 : Nat := 4983230072969 + 3 ^ 40 * 2409630 * 2
def baseEnd_2409630 : Nat := 91651732555075003351357

theorem tailTrace_2409630 : CollatzResearch.WordTrace tailWord_2409630 prefixEnd_2409630 91651732555075003351357 := by
  unfold tailWord_2409630
  simp only [CollatzResearch.WordTrace]
  refine ⟨10985803282541189610671293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 58590950840219677923580229 10985803282541189610671293)
  ·
    refine ⟨4119676230952946104001735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10985803282541189610671293 4119676230952946104001735)
    ·
      refine ⟨6179514346429419156002603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4119676230952946104001735 6179514346429419156002603)
      ·
        refine ⟨9269271519644128734003905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6179514346429419156002603 9269271519644128734003905)
        ·
          refine ⟨6951953639733096550502929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9269271519644128734003905 6951953639733096550502929)
          ·
            refine ⟨5213965229799822412877197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6951953639733096550502929 5213965229799822412877197)
            ·
              refine ⟨1955236961174933404828949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5213965229799822412877197 1955236961174933404828949)
              ·
                refine ⟨91651732555075003351357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1955236961174933404828949 91651732555075003351357)
                ·
                  rfl

theorem cell22_2409630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 2, 3, 6].length) (baseStart_2409630 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2409630 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2409630 prefixEnd_2409630 := by exact prefixLift 2409630
  have htrace : WordTrace (prefixWord ++ tailWord_2409630) baseStart_2409630 baseEnd_2409630 := by
    simpa [prefixWord, tailWord_2409630, baseEnd_2409630] using wordTrace_append hprefix tailTrace_2409630
  have hstable : (prefixWord ++ tailWord_2409630).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2409630).length < 2 ^ (prefixWord ++ tailWord_2409630).sum := by decide
  have hdescent : baseEnd_2409630 < baseStart_2409630 := by decide
  rcases family_descends (prefixWord ++ tailWord_2409630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2409662 : List Nat := [4, 2, 1, 1, 3, 1, 2, 4, 1, 3]
def baseStart_2409662 : Nat := 118140960795 + 2409662 * 2 ^ 59
def prefixEnd_2409662 : Nat := 4983230072969 + 3 ^ 40 * 2409662 * 2
def baseEnd_2409662 : Nat := 824876547249637613362115

theorem tailTrace_2409662 : CollatzResearch.WordTrace tailWord_2409662 prefixEnd_2409662 824876547249637613362115 := by
  unfold tailWord_2409662
  simp only [CollatzResearch.WordTrace]
  refine ⟨10985949174526698293816905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 58591728930809057567023493 10985949174526698293816905)
  ·
    refine ⟨8239461880895023720362679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10985949174526698293816905 8239461880895023720362679)
    ·
      refine ⟨12359192821342535580544019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8239461880895023720362679 12359192821342535580544019)
      ·
        refine ⟨18538789232013803370816029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12359192821342535580544019 18538789232013803370816029)
        ·
          refine ⟨6952045962005176264056011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18538789232013803370816029 6952045962005176264056011)
          ·
            refine ⟨10428068943007764396084017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6952045962005176264056011 10428068943007764396084017)
            ·
              refine ⟨7821051707255823297063013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10428068943007764396084017 7821051707255823297063013)
              ·
                refine ⟨1466447195110466868199315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7821051707255823297063013 1466447195110466868199315)
                ·
                  refine ⟨2199670792665700302298973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1466447195110466868199315 2199670792665700302298973)
                  ·
                    refine ⟨824876547249637613362115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2199670792665700302298973 824876547249637613362115)
                    ·
                      rfl

theorem cell22_2409662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 2, 4, 1, 3].length) (baseStart_2409662 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2409662 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2409662 prefixEnd_2409662 := by exact prefixLift 2409662
  have htrace : WordTrace (prefixWord ++ tailWord_2409662) baseStart_2409662 baseEnd_2409662 := by
    simpa [prefixWord, tailWord_2409662, baseEnd_2409662] using wordTrace_append hprefix tailTrace_2409662
  have hstable : (prefixWord ++ tailWord_2409662).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2409662).length < 2 ^ (prefixWord ++ tailWord_2409662).sum := by decide
  have hdescent : baseEnd_2409662 < baseStart_2409662 := by decide
  rcases family_descends (prefixWord ++ tailWord_2409662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2409671 : List Nat := [1, 1, 4, 1, 1, 1, 1, 3, 5, 4]
def baseStart_2409671 : Nat := 118140960795 + 2409671 * 2 ^ 59
def prefixEnd_2409671 : Nat := 4983230072969 + 3 ^ 40 * 2409671 * 2
def baseEnd_2409671 : Nat := 824879628133564589887087

theorem tailTrace_2409671 : CollatzResearch.WordTrace tailWord_2409671 prefixEnd_2409671 824879628133564589887087 := by
  unfold tailWord_2409671
  simp only [CollatzResearch.WordTrace]
  refine ⟨87887921653180980887612867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58591947768787320591741911 87887921653180980887612867)
  ·
    refine ⟨131831882479771471331419301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87887921653180980887612867 131831882479771471331419301)
    ·
      refine ⟨24718477964957150874641119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 131831882479771471331419301 24718477964957150874641119)
      ·
        refine ⟨37077716947435726311961679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24718477964957150874641119 37077716947435726311961679)
        ·
          refine ⟨55616575421153589467942519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37077716947435726311961679 55616575421153589467942519)
          ·
            refine ⟨83424863131730384201913779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55616575421153589467942519 83424863131730384201913779)
            ·
              refine ⟨125137294697595576302870669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 83424863131730384201913779 125137294697595576302870669)
              ·
                refine ⟨46926485511598341113576501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 125137294697595576302870669 46926485511598341113576501)
                ·
                  refine ⟨4399358016712344479397797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 46926485511598341113576501 4399358016712344479397797)
                  ·
                    refine ⟨824879628133564589887087, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4399358016712344479397797 824879628133564589887087)
                    ·
                      rfl

theorem cell22_2409671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 3, 5, 4].length) (baseStart_2409671 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2409671 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2409671 prefixEnd_2409671 := by exact prefixLift 2409671
  have htrace : WordTrace (prefixWord ++ tailWord_2409671) baseStart_2409671 baseEnd_2409671 := by
    simpa [prefixWord, tailWord_2409671, baseEnd_2409671] using wordTrace_append hprefix tailTrace_2409671
  have hstable : (prefixWord ++ tailWord_2409671).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2409671).length < 2 ^ (prefixWord ++ tailWord_2409671).sum := by decide
  have hdescent : baseEnd_2409671 < baseStart_2409671 := by decide
  rcases family_descends (prefixWord ++ tailWord_2409671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2409731 : List Nat := [1, 1, 1, 3, 2, 4, 1, 9]
def baseStart_2409731 : Nat := 118140960795 + 2409731 * 2 ^ 59
def prefixEnd_2409731 : Nat := 4983230072969 + 3 ^ 40 * 2409731 * 2
def baseEnd_2409731 : Nat := 91655574151082714820767

theorem tailTrace_2409731 : CollatzResearch.WordTrace tailWord_2409731 prefixEnd_2409731 91655574151082714820767 := by
  unfold tailWord_2409731
  simp only [CollatzResearch.WordTrace]
  refine ⟨87890110032963611134797047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58593406688642407423198031 87890110032963611134797047)
  ·
    refine ⟨131835165049445416702195571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87890110032963611134797047 131835165049445416702195571)
    ·
      refine ⟨197752747574168125053293357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131835165049445416702195571 197752747574168125053293357)
      ·
        refine ⟨74157280340313046894985009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 197752747574168125053293357 74157280340313046894985009)
        ·
          refine ⟨55617960255234785171238757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 74157280340313046894985009 55617960255234785171238757)
          ·
            refine ⟨10428367547856522219607267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 55617960255234785171238757 10428367547856522219607267)
            ·
              refine ⟨15642551321784783329410901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10428367547856522219607267 15642551321784783329410901)
              ·
                refine ⟨91655574151082714820767, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 15642551321784783329410901 91655574151082714820767)
                ·
                  rfl

theorem cell22_2409731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 1, 9].length) (baseStart_2409731 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2409731 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2409731 prefixEnd_2409731 := by exact prefixLift 2409731
  have htrace : WordTrace (prefixWord ++ tailWord_2409731) baseStart_2409731 baseEnd_2409731 := by
    simpa [prefixWord, tailWord_2409731, baseEnd_2409731] using wordTrace_append hprefix tailTrace_2409731
  have hstable : (prefixWord ++ tailWord_2409731).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2409731).length < 2 ^ (prefixWord ++ tailWord_2409731).sum := by decide
  have hdescent : baseEnd_2409731 < baseStart_2409731 := by decide
  rcases family_descends (prefixWord ++ tailWord_2409731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2409778 : List Nat := [3, 2, 1, 1, 4, 1, 1, 1, 2, 6]
def baseStart_2409778 : Nat := 118140960795 + 2409778 * 2 ^ 59
def prefixEnd_2409778 : Nat := 4983230072969 + 3 ^ 40 * 2409778 * 2
def baseEnd_2409778 : Nat := 824916256420251977461759

theorem tailTrace_2409778 : CollatzResearch.WordTrace tailWord_2409778 prefixEnd_2409778 824916256420251977461759 := by
  unfold tailWord_2409778
  simp only [CollatzResearch.WordTrace]
  refine ⟨21972956065948334540439497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58594549509195558774505325 21972956065948334540439497)
  ·
    refine ⟨16479717049461250905329623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21972956065948334540439497 16479717049461250905329623)
    ·
      refine ⟨24719575574191876357994435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16479717049461250905329623 24719575574191876357994435)
      ·
        refine ⟨37079363361287814536991653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24719575574191876357994435 37079363361287814536991653)
        ·
          refine ⟨6952380630241465225685935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 37079363361287814536991653 6952380630241465225685935)
          ·
            refine ⟨10428570945362197838528903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6952380630241465225685935 10428570945362197838528903)
            ·
              refine ⟨15642856418043296757793355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10428570945362197838528903 15642856418043296757793355)
              ·
                refine ⟨23464284627064945136690033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15642856418043296757793355 23464284627064945136690033)
                ·
                  refine ⟨17598213470298708852517525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23464284627064945136690033 17598213470298708852517525)
                  ·
                    refine ⟨824916256420251977461759, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17598213470298708852517525 824916256420251977461759)
                    ·
                      rfl

theorem cell22_2409778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 1, 1, 2, 6].length) (baseStart_2409778 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2409778 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2409778 prefixEnd_2409778 := by exact prefixLift 2409778
  have htrace : WordTrace (prefixWord ++ tailWord_2409778) baseStart_2409778 baseEnd_2409778 := by
    simpa [prefixWord, tailWord_2409778, baseEnd_2409778] using wordTrace_append hprefix tailTrace_2409778
  have hstable : (prefixWord ++ tailWord_2409778).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2409778).length < 2 ^ (prefixWord ++ tailWord_2409778).sum := by decide
  have hdescent : baseEnd_2409778 < baseStart_2409778 := by decide
  rcases family_descends (prefixWord ++ tailWord_2409778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2409868 : List Nat := [2, 2, 1, 2, 1, 3, 1, 3, 1, 6]
def baseStart_2409868 : Nat := 118140960795 + 2409868 * 2 ^ 59
def prefixEnd_2409868 : Nat := 4983230072969 + 3 ^ 40 * 2409868 * 2
def baseEnd_2409868 : Nat := 824947065259521742711483

theorem tailTrace_2409868 : CollatzResearch.WordTrace tailWord_2409868 prefixEnd_2409868 824947065259521742711483 := by
  unfold tailWord_2409868
  simp only [CollatzResearch.WordTrace]
  refine ⟨43947553416733641766267129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58596737888978189021689505 43947553416733641766267129)
  ·
    refine ⟨32960665062550231324700347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43947553416733641766267129 32960665062550231324700347)
    ·
      refine ⟨49440997593825346987050521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32960665062550231324700347 49440997593825346987050521)
      ·
        refine ⟨37080748195369010240287891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49440997593825346987050521 37080748195369010240287891)
        ·
          refine ⟨55621122293053515360431837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37080748195369010240287891 55621122293053515360431837)
          ·
            refine ⟨20857920859895068260161939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 55621122293053515360431837 20857920859895068260161939)
            ·
              refine ⟨31286881289842602390242909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20857920859895068260161939 31286881289842602390242909)
              ·
                refine ⟨11732580483690975896341091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31286881289842602390242909 11732580483690975896341091)
                ·
                  refine ⟨17598870725536463844511637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11732580483690975896341091 17598870725536463844511637)
                  ·
                    refine ⟨824947065259521742711483, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17598870725536463844511637 824947065259521742711483)
                    ·
                      rfl

theorem cell22_2409868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 1, 3, 1, 6].length) (baseStart_2409868 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2409868 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2409868 prefixEnd_2409868 := by exact prefixLift 2409868
  have htrace : WordTrace (prefixWord ++ tailWord_2409868) baseStart_2409868 baseEnd_2409868 := by
    simpa [prefixWord, tailWord_2409868, baseEnd_2409868] using wordTrace_append hprefix tailTrace_2409868
  have hstable : (prefixWord ++ tailWord_2409868).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2409868).length < 2 ^ (prefixWord ++ tailWord_2409868).sum := by decide
  have hdescent : baseEnd_2409868 < baseStart_2409868 := by decide
  rcases family_descends (prefixWord ++ tailWord_2409868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2409885 : List Nat := [1, 4, 2, 1, 3, 1, 1, 1, 4, 4]
def baseStart_2409885 : Nat := 118140960795 + 2409885 * 2 ^ 59
def prefixEnd_2409885 : Nat := 4983230072969 + 3 ^ 40 * 2409885 * 2
def baseEnd_2409885 : Nat := 824952884706939365036431

theorem tailTrace_2409885 : CollatzResearch.WordTrace tailWord_2409885 prefixEnd_2409885 824952884706939365036431 := by
  unfold tailWord_2409885
  simp only [CollatzResearch.WordTrace]
  refine ⟨87895726874405695435903109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58597151249603796957268739 87895726874405695435903109)
  ·
    refine ⟨16480448788951067894231833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 87895726874405695435903109 16480448788951067894231833)
    ·
      refine ⟨12360336591713300920673875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16480448788951067894231833 12360336591713300920673875)
      ·
        refine ⟨18540504887569951381010813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12360336591713300920673875 18540504887569951381010813)
        ·
          refine ⟨6952689332838731767879055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18540504887569951381010813 6952689332838731767879055)
          ·
            refine ⟨10429033999258097651818583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6952689332838731767879055 10429033999258097651818583)
            ·
              refine ⟨15643550998887146477727875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10429033999258097651818583 15643550998887146477727875)
              ·
                refine ⟨23465326498330719716591813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15643550998887146477727875 23465326498330719716591813)
                ·
                  refine ⟨4399748718437009946860965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23465326498330719716591813 4399748718437009946860965)
                  ·
                    refine ⟨824952884706939365036431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4399748718437009946860965 824952884706939365036431)
                    ·
                      rfl

theorem cell22_2409885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 1, 1, 4, 4].length) (baseStart_2409885 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2409885 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2409885 prefixEnd_2409885 := by exact prefixLift 2409885
  have htrace : WordTrace (prefixWord ++ tailWord_2409885) baseStart_2409885 baseEnd_2409885 := by
    simpa [prefixWord, tailWord_2409885, baseEnd_2409885] using wordTrace_append hprefix tailTrace_2409885
  have hstable : (prefixWord ++ tailWord_2409885).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2409885).length < 2 ^ (prefixWord ++ tailWord_2409885).sum := by decide
  have hdescent : baseEnd_2409885 < baseStart_2409885 := by decide
  rcases family_descends (prefixWord ++ tailWord_2409885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2409943 : List Nat := [1, 1, 3, 2, 1, 1, 1, 2, 3, 7]
def baseStart_2409943 : Nat := 118140960795 + 2409943 * 2 ^ 59
def prefixEnd_2409943 : Nat := 4983230072969 + 3 ^ 40 * 2409943 * 2
def baseEnd_2409943 : Nat := 824972739292246547086253

theorem tailTrace_2409943 : CollatzResearch.WordTrace tailWord_2409943 prefixEnd_2409943 824972739292246547086253 := by
  unfold tailWord_2409943
  simp only [CollatzResearch.WordTrace]
  refine ⟨87897842308195571341514483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58598561538797047561009655 87897842308195571341514483)
  ·
    refine ⟨131846763462293357012271725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87897842308195571341514483 131846763462293357012271725)
    ·
      refine ⟨49442536298360008879601897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 131846763462293357012271725 49442536298360008879601897)
      ·
        refine ⟨37081902223770006659701423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49442536298360008879601897 37081902223770006659701423)
        ·
          refine ⟨55622853335655009989552135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37081902223770006659701423 55622853335655009989552135)
          ·
            refine ⟨83434280003482514984328203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55622853335655009989552135 83434280003482514984328203)
            ·
              refine ⟨125151420005223772476492305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 83434280003482514984328203 125151420005223772476492305)
              ·
                refine ⟨93863565003917829357369229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 125151420005223772476492305 93863565003917829357369229)
                ·
                  refine ⟨35198836876469186009013461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 93863565003917829357369229 35198836876469186009013461)
                  ·
                    refine ⟨824972739292246547086253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 35198836876469186009013461 824972739292246547086253)
                    ·
                      rfl

theorem cell22_2409943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 2, 3, 7].length) (baseStart_2409943 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2409943 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2409943 prefixEnd_2409943 := by exact prefixLift 2409943
  have htrace : WordTrace (prefixWord ++ tailWord_2409943) baseStart_2409943 baseEnd_2409943 := by
    simpa [prefixWord, tailWord_2409943, baseEnd_2409943] using wordTrace_append hprefix tailTrace_2409943
  have hstable : (prefixWord ++ tailWord_2409943).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2409943).length < 2 ^ (prefixWord ++ tailWord_2409943).sum := by decide
  have hdescent : baseEnd_2409943 < baseStart_2409943 := by decide
  rcases family_descends (prefixWord ++ tailWord_2409943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2409945 : List Nat := [1, 2, 1, 2, 4, 2, 1, 4, 5]
def baseStart_2409945 : Nat := 118140960795 + 2409945 * 2 ^ 59
def prefixEnd_2409945 : Nat := 4983230072969 + 3 ^ 40 * 2409945 * 2
def baseEnd_2409945 : Nat := 274991141311039736178749

theorem tailTrace_2409945 : CollatzResearch.WordTrace tailWord_2409945 prefixEnd_2409945 274991141311039736178749 := by
  unfold tailWord_2409945
  simp only [CollatzResearch.WordTrace]
  refine ⟨87897915254188325683087289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58598610169458883788724859 87897915254188325683087289)
  ·
    refine ⟨65923436440641244262315467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87897915254188325683087289 65923436440641244262315467)
    ·
      refine ⟨98885154660961866393473201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65923436440641244262315467 98885154660961866393473201)
      ·
        refine ⟨74163865995721399795104901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 98885154660961866393473201 74163865995721399795104901)
        ·
          refine ⟨13905724874197762461582169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 74163865995721399795104901 13905724874197762461582169)
          ·
            refine ⟨10429293655648321846186627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13905724874197762461582169 10429293655648321846186627)
            ·
              refine ⟨15643940483472482769279941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10429293655648321846186627 15643940483472482769279941)
              ·
                refine ⟨2933238840651090519239989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15643940483472482769279941 2933238840651090519239989)
                ·
                  refine ⟨274991141311039736178749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2933238840651090519239989 274991141311039736178749)
                  ·
                    rfl

theorem cell22_2409945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 1, 4, 5].length) (baseStart_2409945 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2409945 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2409945 prefixEnd_2409945 := by exact prefixLift 2409945
  have htrace : WordTrace (prefixWord ++ tailWord_2409945) baseStart_2409945 baseEnd_2409945 := by
    simpa [prefixWord, tailWord_2409945, baseEnd_2409945] using wordTrace_append hprefix tailTrace_2409945
  have hstable : (prefixWord ++ tailWord_2409945).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2409945).length < 2 ^ (prefixWord ++ tailWord_2409945).sum := by decide
  have hdescent : baseEnd_2409945 < baseStart_2409945 := by decide
  rcases family_descends (prefixWord ++ tailWord_2409945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2409960 : List Nat := [2, 1, 4, 1, 1, 2, 3, 1, 2, 5]
def baseStart_2409960 : Nat := 118140960795 + 2409960 * 2 ^ 59
def prefixEnd_2409960 : Nat := 4983230072969 + 3 ^ 40 * 2409960 * 2
def baseEnd_2409960 : Nat := 824978558739664169411201

theorem tailTrace_2409960 : CollatzResearch.WordTrace tailWord_2409960 prefixEnd_2409960 824978558739664169411201 := by
  unfold tailWord_2409960
  simp only [CollatzResearch.WordTrace]
  refine ⟨43949231174566991622441667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58598974899422655496588889 43949231174566991622441667)
  ·
    refine ⟨65923846761850487433662501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43949231174566991622441667 65923846761850487433662501)
    ·
      refine ⟨12360721267846966393811719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 65923846761850487433662501 12360721267846966393811719)
      ·
        refine ⟨18541081901770449590717579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12360721267846966393811719 18541081901770449590717579)
        ·
          refine ⟨27811622852655674386076369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18541081901770449590717579 27811622852655674386076369)
          ·
            refine ⟨20858717139491755789557277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27811622852655674386076369 20858717139491755789557277)
            ·
              refine ⟨7822018927309408421083979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20858717139491755789557277 7822018927309408421083979)
              ·
                refine ⟨11733028390964112631625969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7822018927309408421083979 11733028390964112631625969)
                ·
                  refine ⟨8799771293223084473719477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11733028390964112631625969 8799771293223084473719477)
                  ·
                    refine ⟨824978558739664169411201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8799771293223084473719477 824978558739664169411201)
                    ·
                      rfl

theorem cell22_2409960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 3, 1, 2, 5].length) (baseStart_2409960 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2409960 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2409960 prefixEnd_2409960 := by exact prefixLift 2409960
  have htrace : WordTrace (prefixWord ++ tailWord_2409960) baseStart_2409960 baseEnd_2409960 := by
    simpa [prefixWord, tailWord_2409960, baseEnd_2409960] using wordTrace_append hprefix tailTrace_2409960
  have hstable : (prefixWord ++ tailWord_2409960).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2409960).length < 2 ^ (prefixWord ++ tailWord_2409960).sum := by decide
  have hdescent : baseEnd_2409960 < baseStart_2409960 := by decide
  rcases family_descends (prefixWord ++ tailWord_2409960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2410035 : List Nat := [1, 1, 1, 2, 4, 4, 1, 8]
def baseStart_2410035 : Nat := 118140960795 + 2410035 * 2 ^ 59
def prefixEnd_2410035 : Nat := 4983230072969 + 3 ^ 40 * 2410035 * 2
def baseEnd_2410035 : Nat := 91667136974709885976219

theorem tailTrace_2410035 : CollatzResearch.WordTrace tailWord_2410035 prefixEnd_2410035 91667136974709885976219 := by
  unfold tailWord_2410035
  simp only [CollatzResearch.WordTrace]
  refine ⟨87901197823862271053863559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58600798549241514035909039 87901197823862271053863559)
  ·
    refine ⟨131851796735793406580795339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87901197823862271053863559 131851796735793406580795339)
    ·
      refine ⟨197777695103690109871193009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131851796735793406580795339 197777695103690109871193009)
      ·
        refine ⟨148333271327767582403394757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 197777695103690109871193009 148333271327767582403394757)
        ·
          refine ⟨27812488373956421700636517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 148333271327767582403394757 27812488373956421700636517)
          ·
            refine ⟨5214841570116829068869347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27812488373956421700636517 5214841570116829068869347)
            ·
              refine ⟨7822262355175243603304021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5214841570116829068869347 7822262355175243603304021)
              ·
                refine ⟨91667136974709885976219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7822262355175243603304021 91667136974709885976219)
                ·
                  rfl

theorem cell22_2410035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 4, 1, 8].length) (baseStart_2410035 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2410035 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2410035 prefixEnd_2410035 := by exact prefixLift 2410035
  have htrace : WordTrace (prefixWord ++ tailWord_2410035) baseStart_2410035 baseEnd_2410035 := by
    simpa [prefixWord, tailWord_2410035, baseEnd_2410035] using wordTrace_append hprefix tailTrace_2410035
  have hstable : (prefixWord ++ tailWord_2410035).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2410035).length < 2 ^ (prefixWord ++ tailWord_2410035).sum := by decide
  have hdescent : baseEnd_2410035 < baseStart_2410035 := by decide
  rcases family_descends (prefixWord ++ tailWord_2410035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2410065 : List Nat := [1, 2, 2, 1, 3, 2, 2, 1, 2, 6]
def baseStart_2410065 : Nat := 118140960795 + 2410065 * 2 ^ 59
def prefixEnd_2410065 : Nat := 4983230072969 + 3 ^ 40 * 2410065 * 2
def baseEnd_2410065 : Nat := 825014502385478895535879

theorem tailTrace_2410065 : CollatzResearch.WordTrace tailWord_2410065 prefixEnd_2410065 825014502385478895535879 := by
  unfold tailWord_2410065
  simp only [CollatzResearch.WordTrace]
  refine ⟨87902292013753586177455649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58601528009169057451637099 87902292013753586177455649)
  ·
    refine ⟨65926719010315189633091737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87902292013753586177455649 65926719010315189633091737)
    ·
      refine ⟨49445039257736392224818803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65926719010315189633091737 49445039257736392224818803)
      ·
        refine ⟨74167558886604588337228205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49445039257736392224818803 74167558886604588337228205)
        ·
          refine ⟨27812834582476720626460577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 74167558886604588337228205 27812834582476720626460577)
          ·
            refine ⟨20859625936857540469845433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27812834582476720626460577 20859625936857540469845433)
            ·
              refine ⟨15644719452643155352384075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20859625936857540469845433 15644719452643155352384075)
              ·
                refine ⟨23467079178964733028576113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15644719452643155352384075 23467079178964733028576113)
                ·
                  refine ⟨17600309384223549771432085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23467079178964733028576113 17600309384223549771432085)
                  ·
                    refine ⟨825014502385478895535879, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17600309384223549771432085 825014502385478895535879)
                    ·
                      rfl

theorem cell22_2410065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 2, 1, 2, 6].length) (baseStart_2410065 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2410065 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2410065 prefixEnd_2410065 := by exact prefixLift 2410065
  have htrace : WordTrace (prefixWord ++ tailWord_2410065) baseStart_2410065 baseEnd_2410065 := by
    simpa [prefixWord, tailWord_2410065, baseEnd_2410065] using wordTrace_append hprefix tailTrace_2410065
  have hstable : (prefixWord ++ tailWord_2410065).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2410065).length < 2 ^ (prefixWord ++ tailWord_2410065).sum := by decide
  have hdescent : baseEnd_2410065 < baseStart_2410065 := by decide
  rcases family_descends (prefixWord ++ tailWord_2410065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2410095 : List Nat := [1, 1, 2, 1, 3, 2, 1, 2, 4, 5]
def baseStart_2410095 : Nat := 118140960795 + 2410095 * 2 ^ 59
def prefixEnd_2410095 : Nat := 4983230072969 + 3 ^ 40 * 2410095 * 2
def baseEnd_2410095 : Nat := 825024771998568817285787

theorem tailTrace_2410095 : CollatzResearch.WordTrace tailWord_2410095 prefixEnd_2410095 825024771998568817285787 := by
  unfold tailWord_2410095
  simp only [CollatzResearch.WordTrace]
  refine ⟨87903386203644901301047739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58602257469096600867365159 87903386203644901301047739)
  ·
    refine ⟨131855079305467351951571609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87903386203644901301047739 131855079305467351951571609)
    ·
      refine ⟨98891309479100513963678707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 131855079305467351951571609 98891309479100513963678707)
      ·
        refine ⟨148336964218650770945518061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98891309479100513963678707 148336964218650770945518061)
        ·
          refine ⟨55626361581994039104569273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 148336964218650770945518061 55626361581994039104569273)
          ·
            refine ⟨41719771186495529328426955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55626361581994039104569273 41719771186495529328426955)
            ·
              refine ⟨62579656779743293992640433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41719771186495529328426955 62579656779743293992640433)
              ·
                refine ⟨46934742584807470494480325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 62579656779743293992640433 46934742584807470494480325)
                ·
                  refine ⟨8800264234651400717715061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 46934742584807470494480325 8800264234651400717715061)
                  ·
                    refine ⟨825024771998568817285787, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8800264234651400717715061 825024771998568817285787)
                    ·
                      rfl

theorem cell22_2410095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 2, 4, 5].length) (baseStart_2410095 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2410095 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2410095 prefixEnd_2410095 := by exact prefixLift 2410095
  have htrace : WordTrace (prefixWord ++ tailWord_2410095) baseStart_2410095 baseEnd_2410095 := by
    simpa [prefixWord, tailWord_2410095, baseEnd_2410095] using wordTrace_append hprefix tailTrace_2410095
  have hstable : (prefixWord ++ tailWord_2410095).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2410095).length < 2 ^ (prefixWord ++ tailWord_2410095).sum := by decide
  have hdescent : baseEnd_2410095 < baseStart_2410095 := by decide
  rcases family_descends (prefixWord ++ tailWord_2410095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2410152 : List Nat := [2, 1, 7, 1, 1, 1, 2, 3, 1, 3]
def baseStart_2410152 : Nat := 118140960795 + 2410152 * 2 ^ 59
def prefixEnd_2410152 : Nat := 4983230072969 + 3 ^ 40 * 2410152 * 2
def baseEnd_2410152 : Nat := 825044284263439668610613

theorem tailTrace_2410152 : CollatzResearch.WordTrace tailWord_2410152 prefixEnd_2410152 825044284263439668610613 := by
  unfold tailWord_2410152
  simp only [CollatzResearch.WordTrace]
  refine ⟨43952732582219200017936355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58603643442958933357248473 43952732582219200017936355)
  ·
    refine ⟨65929098873328800026904533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43952732582219200017936355 65929098873328800026904533)
    ·
      refine ⟨1545213254843643750630575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 65929098873328800026904533 1545213254843643750630575)
      ·
        refine ⟨2317819882265465625945863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1545213254843643750630575 2317819882265465625945863)
        ·
          refine ⟨3476729823398198438918795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2317819882265465625945863 3476729823398198438918795)
          ·
            refine ⟨5215094735097297658378193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3476729823398198438918795 5215094735097297658378193)
            ·
              refine ⟨3911321051322973243783645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5215094735097297658378193 3911321051322973243783645)
              ·
                refine ⟨1466745394246114966418867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3911321051322973243783645 1466745394246114966418867)
                ·
                  refine ⟨2200118091369172449628301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1466745394246114966418867 2200118091369172449628301)
                  ·
                    refine ⟨825044284263439668610613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2200118091369172449628301 825044284263439668610613)
                    ·
                      rfl

theorem cell22_2410152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 1, 2, 3, 1, 3].length) (baseStart_2410152 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2410152 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2410152 prefixEnd_2410152 := by exact prefixLift 2410152
  have htrace : WordTrace (prefixWord ++ tailWord_2410152) baseStart_2410152 baseEnd_2410152 := by
    simpa [prefixWord, tailWord_2410152, baseEnd_2410152] using wordTrace_append hprefix tailTrace_2410152
  have hstable : (prefixWord ++ tailWord_2410152).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2410152).length < 2 ^ (prefixWord ++ tailWord_2410152).sum := by decide
  have hdescent : baseEnd_2410152 < baseStart_2410152 := by decide
  rcases family_descends (prefixWord ++ tailWord_2410152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2410159 : List Nat := [1, 1, 2, 1, 2, 4, 4, 3, 4]
def baseStart_2410159 : Nat := 118140960795 + 2410159 * 2 ^ 59
def prefixEnd_2410159 : Nat := 4983230072969 + 3 ^ 40 * 2410159 * 2
def baseEnd_2410159 : Nat := 275015560168831327895197

theorem tailTrace_2410159 : CollatzResearch.WordTrace tailWord_2410159 prefixEnd_2410159 275015560168831327895197 := by
  unfold tailWord_2410159
  simp only [CollatzResearch.WordTrace]
  refine ⟨87905720475413040231377531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58603813650275360154251687 87905720475413040231377531)
  ·
    refine ⟨131858580713119560347066297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87905720475413040231377531 131858580713119560347066297)
    ·
      refine ⟨98893935534839670260299723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 131858580713119560347066297 98893935534839670260299723)
      ·
        refine ⟨148340903302259505390449585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98893935534839670260299723 148340903302259505390449585)
        ·
          refine ⟨111255677476694629042837189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 148340903302259505390449585 111255677476694629042837189)
          ·
            refine ⟨20860439526880242945531973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 111255677476694629042837189 20860439526880242945531973)
            ·
              refine ⟨3911332411290045552287245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20860439526880242945531973 3911332411290045552287245)
              ·
                refine ⟨1466749654233767082107717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3911332411290045552287245 1466749654233767082107717)
                ·
                  refine ⟨275015560168831327895197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1466749654233767082107717 275015560168831327895197)
                  ·
                    rfl

theorem cell22_2410159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 4, 3, 4].length) (baseStart_2410159 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2410159 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2410159 prefixEnd_2410159 := by exact prefixLift 2410159
  have htrace : WordTrace (prefixWord ++ tailWord_2410159) baseStart_2410159 baseEnd_2410159 := by
    simpa [prefixWord, tailWord_2410159, baseEnd_2410159] using wordTrace_append hprefix tailTrace_2410159
  have hstable : (prefixWord ++ tailWord_2410159).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2410159).length < 2 ^ (prefixWord ++ tailWord_2410159).sum := by decide
  have hdescent : baseEnd_2410159 < baseStart_2410159 := by decide
  rcases family_descends (prefixWord ++ tailWord_2410159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2410246 : List Nat := [6, 2, 2, 1, 2, 1, 1, 2, 1, 4]
def baseStart_2410246 : Nat := 118140960795 + 2410246 * 2 ^ 59
def prefixEnd_2410246 : Nat := 4983230072969 + 3 ^ 40 * 2410246 * 2
def baseEnd_2410246 : Nat := 825076462384454756760325

theorem tailTrace_2410246 : CollatzResearch.WordTrace tailWord_2410246 prefixEnd_2410246 825076462384454756760325 := by
  unfold tailWord_2410246
  simp only [CollatzResearch.WordTrace]
  refine ⟨2747152925815557940306081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 58605929084065236059863061 2747152925815557940306081)
  ·
    refine ⟨2060364694361668455229561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2747152925815557940306081 2060364694361668455229561)
    ·
      refine ⟨1545273520771251341422171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2060364694361668455229561 1545273520771251341422171)
      ·
        refine ⟨2317910281156877012133257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1545273520771251341422171 2317910281156877012133257)
        ·
          refine ⟨1738432710867657759099943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2317910281156877012133257 1738432710867657759099943)
          ·
            refine ⟨2607649066301486638649915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1738432710867657759099943 2607649066301486638649915)
            ·
              refine ⟨3911473599452229957974873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2607649066301486638649915 3911473599452229957974873)
              ·
                refine ⟨2933605199589172468481155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3911473599452229957974873 2933605199589172468481155)
                ·
                  refine ⟨4400407799383758702721733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2933605199589172468481155 4400407799383758702721733)
                  ·
                    refine ⟨825076462384454756760325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4400407799383758702721733 825076462384454756760325)
                    ·
                      rfl

theorem cell22_2410246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 2, 1, 1, 2, 1, 4].length) (baseStart_2410246 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2410246 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2410246 prefixEnd_2410246 := by exact prefixLift 2410246
  have htrace : WordTrace (prefixWord ++ tailWord_2410246) baseStart_2410246 baseEnd_2410246 := by
    simpa [prefixWord, tailWord_2410246, baseEnd_2410246] using wordTrace_append hprefix tailTrace_2410246
  have hstable : (prefixWord ++ tailWord_2410246).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2410246).length < 2 ^ (prefixWord ++ tailWord_2410246).sum := by decide
  have hdescent : baseEnd_2410246 < baseStart_2410246 := by decide
  rcases family_descends (prefixWord ++ tailWord_2410246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2410309 : List Nat := [1, 3, 1, 1, 1, 2, 6, 1, 1, 5]
def baseStart_2410309 : Nat := 118140960795 + 2410309 * 2 ^ 59
def prefixEnd_2410309 : Nat := 4983230072969 + 3 ^ 40 * 2410309 * 2
def baseEnd_2410309 : Nat := 825098028571943592435131

theorem tailTrace_2410309 : CollatzResearch.WordTrace tailWord_2410309 prefixEnd_2410309 825098028571943592435131 := by
  unfold tailWord_2410309
  simp only [CollatzResearch.WordTrace]
  refine ⟨87911191424869615849337981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58607460949913077232891987 87911191424869615849337981)
  ·
    refine ⟨32966696784326105943501743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 87911191424869615849337981 32966696784326105943501743)
    ·
      refine ⟨49450045176489158915252615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32966696784326105943501743 49450045176489158915252615)
      ·
        refine ⟨74175067764733738372878923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49450045176489158915252615 74175067764733738372878923)
        ·
          refine ⟨111262601647100607559318385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74175067764733738372878923 111262601647100607559318385)
          ·
            refine ⟨83446951235325455669488789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 111262601647100607559318385 83446951235325455669488789)
            ·
              refine ⟨3911575839155880734507287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 83446951235325455669488789 3911575839155880734507287)
              ·
                refine ⟨5867363758733821101760931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3911575839155880734507287 5867363758733821101760931)
                ·
                  refine ⟨8801045638100731652641397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5867363758733821101760931 8801045638100731652641397)
                  ·
                    refine ⟨825098028571943592435131, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8801045638100731652641397 825098028571943592435131)
                    ·
                      rfl

theorem cell22_2410309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 6, 1, 1, 5].length) (baseStart_2410309 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2410309 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2410309 prefixEnd_2410309 := by exact prefixLift 2410309
  have htrace : WordTrace (prefixWord ++ tailWord_2410309) baseStart_2410309 baseEnd_2410309 := by
    simpa [prefixWord, tailWord_2410309, baseEnd_2410309] using wordTrace_append hprefix tailTrace_2410309
  have hstable : (prefixWord ++ tailWord_2410309).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2410309).length < 2 ^ (prefixWord ++ tailWord_2410309).sum := by decide
  have hdescent : baseEnd_2410309 < baseStart_2410309 := by decide
  rcases family_descends (prefixWord ++ tailWord_2410309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2410339 : List Nat := [1, 1, 1, 5, 4, 1, 9]
def baseStart_2410339 : Nat := 118140960795 + 2410339 * 2 ^ 59
def prefixEnd_2410339 : Nat := 4983230072969 + 3 ^ 40 * 2410339 * 2
def baseEnd_2410339 : Nat := 30559566599445685710557

theorem tailTrace_2410339 : CollatzResearch.WordTrace tailWord_2410339 prefixEnd_2410339 30559566599445685710557 := by
  unfold tailWord_2410339
  simp only [CollatzResearch.WordTrace]
  refine ⟨87912285614760930972930071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58608190409840620648620047 87912285614760930972930071)
  ·
    refine ⟨131868428422141396459395107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87912285614760930972930071 131868428422141396459395107)
    ·
      refine ⟨197802642633212094689092661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131868428422141396459395107 197802642633212094689092661)
      ·
        refine ⟨18543997746863633877102437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 197802642633212094689092661 18543997746863633877102437)
        ·
          refine ⟨3476999577536931351956707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18543997746863633877102437 3476999577536931351956707)
          ·
            refine ⟨5215499366305397027935061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3476999577536931351956707 5215499366305397027935061)
            ·
              refine ⟨30559566599445685710557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 5215499366305397027935061 30559566599445685710557)
              ·
                rfl

theorem cell22_2410339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 1, 9].length) (baseStart_2410339 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2410339 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2410339 prefixEnd_2410339 := by exact prefixLift 2410339
  have htrace : WordTrace (prefixWord ++ tailWord_2410339) baseStart_2410339 baseEnd_2410339 := by
    simpa [prefixWord, tailWord_2410339, baseEnd_2410339] using wordTrace_append hprefix tailTrace_2410339
  have hstable : (prefixWord ++ tailWord_2410339).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2410339).length < 2 ^ (prefixWord ++ tailWord_2410339).sum := by decide
  have hdescent : baseEnd_2410339 < baseStart_2410339 := by decide
  rcases family_descends (prefixWord ++ tailWord_2410339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2410371 : List Nat := [1, 1, 1, 3, 4, 2, 2, 2, 3, 3]
def baseStart_2410371 : Nat := 118140960795 + 2410371 * 2 ^ 59
def prefixEnd_2410371 : Nat := 4983230072969 + 3 ^ 40 * 2410371 * 2
def baseEnd_2410371 : Nat := 825119252438996097384941

theorem tailTrace_2410371 : CollatzResearch.WordTrace tailWord_2410371 prefixEnd_2410371 825119252438996097384941 := by
  unfold tailWord_2410371
  simp only [CollatzResearch.WordTrace]
  refine ⟨87913452750645000438094967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58608968500430000292063311 87913452750645000438094967)
  ·
    refine ⟨131870179125967500657142451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87913452750645000438094967 131870179125967500657142451)
    ·
      refine ⟨197805268688951250985713677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131870179125967500657142451 197805268688951250985713677)
      ·
        refine ⟨74176975758356719119642629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 197805268688951250985713677 74176975758356719119642629)
        ·
          refine ⟨13908182954691884834932993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 74176975758356719119642629 13908182954691884834932993)
          ·
            refine ⟨10431137216018913626199745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13908182954691884834932993 10431137216018913626199745)
            ·
              refine ⟨7823352912014185219649809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10431137216018913626199745 7823352912014185219649809)
              ·
                refine ⟨5867514684010638914737357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7823352912014185219649809 5867514684010638914737357)
                ·
                  refine ⟨2200318006503989593026509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5867514684010638914737357 2200318006503989593026509)
                  ·
                    refine ⟨825119252438996097384941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2200318006503989593026509 825119252438996097384941)
                    ·
                      rfl

theorem cell22_2410371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 2, 2, 3, 3].length) (baseStart_2410371 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2410371 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2410371 prefixEnd_2410371 := by exact prefixLift 2410371
  have htrace : WordTrace (prefixWord ++ tailWord_2410371) baseStart_2410371 baseEnd_2410371 := by
    simpa [prefixWord, tailWord_2410371, baseEnd_2410371] using wordTrace_append hprefix tailTrace_2410371
  have hstable : (prefixWord ++ tailWord_2410371).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2410371).length < 2 ^ (prefixWord ++ tailWord_2410371).sum := by decide
  have hdescent : baseEnd_2410371 < baseStart_2410371 := by decide
  rcases family_descends (prefixWord ++ tailWord_2410371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2410390 : List Nat := [5, 3, 1, 1, 2, 2, 8]
def baseStart_2410390 : Nat := 118140960795 + 2410390 * 2 ^ 59
def prefixEnd_2410390 : Nat := 4983230072969 + 3 ^ 40 * 2410390 * 2
def baseEnd_2410390 : Nat := 30560213204714310413329

theorem tailTrace_2410390 : CollatzResearch.WordTrace tailWord_2410390 prefixEnd_2410390 30560213204714310413329 := by
  unfold tailWord_2410390
  simp only [CollatzResearch.WordTrace]
  refine ⟨5494634108598510417689789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 58609430491717444455357749 5494634108598510417689789)
  ·
    refine ⟨2060487790724441406633671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5494634108598510417689789 2060487790724441406633671)
    ·
      refine ⟨3090731686086662109950507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2060487790724441406633671 3090731686086662109950507)
      ·
        refine ⟨4636097529129993164925761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3090731686086662109950507 4636097529129993164925761)
        ·
          refine ⟨3477073146847494873694321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4636097529129993164925761 3477073146847494873694321)
          ·
            refine ⟨2607804860135621155270741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3477073146847494873694321 2607804860135621155270741)
            ·
              refine ⟨30560213204714310413329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2607804860135621155270741 30560213204714310413329)
              ·
                rfl

theorem cell22_2410390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 2, 8].length) (baseStart_2410390 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2410390 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2410390 prefixEnd_2410390 := by exact prefixLift 2410390
  have htrace : WordTrace (prefixWord ++ tailWord_2410390) baseStart_2410390 baseEnd_2410390 := by
    simpa [prefixWord, tailWord_2410390, baseEnd_2410390] using wordTrace_append hprefix tailTrace_2410390
  have hstable : (prefixWord ++ tailWord_2410390).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2410390).length < 2 ^ (prefixWord ++ tailWord_2410390).sum := by decide
  have hdescent : baseEnd_2410390 < baseStart_2410390 := by decide
  rcases family_descends (prefixWord ++ tailWord_2410390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2410463 : List Nat := [1, 1, 2, 3, 4, 2, 1, 4, 4]
def baseStart_2410463 : Nat := 118140960795 + 2410463 * 2 ^ 59
def prefixEnd_2410463 : Nat := 4983230072969 + 3 ^ 40 * 2410463 * 2
def baseEnd_2410463 : Nat := 275050248639712841361553

theorem tailTrace_2410463 : CollatzResearch.WordTrace tailWord_2410463 prefixEnd_2410463 275050248639712841361553 := by
  unfold tailWord_2410463
  simp only [CollatzResearch.WordTrace]
  refine ⟨87916808266311700150444043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58611205510874466766962695 87916808266311700150444043)
  ·
    refine ⟨131875212399467550225666065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87916808266311700150444043 131875212399467550225666065)
    ·
      refine ⟨98906409299600662669249549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 131875212399467550225666065 98906409299600662669249549)
      ·
        refine ⟨37089903487350248500968581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 98906409299600662669249549 37089903487350248500968581)
        ·
          refine ⟨6954356903878171593931609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 37089903487350248500968581 6954356903878171593931609)
          ·
            refine ⟨5215767677908628695448707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6954356903878171593931609 5215767677908628695448707)
            ·
              refine ⟨7823651516862943043173061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5215767677908628695448707 7823651516862943043173061)
              ·
                refine ⟨1466934659411801820594949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7823651516862943043173061 1466934659411801820594949)
                ·
                  refine ⟨275050248639712841361553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1466934659411801820594949 275050248639712841361553)
                  ·
                    rfl

theorem cell22_2410463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 2, 1, 4, 4].length) (baseStart_2410463 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2410463 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2410463 prefixEnd_2410463 := by exact prefixLift 2410463
  have htrace : WordTrace (prefixWord ++ tailWord_2410463) baseStart_2410463 baseEnd_2410463 := by
    simpa [prefixWord, tailWord_2410463, baseEnd_2410463] using wordTrace_append hprefix tailTrace_2410463
  have hstable : (prefixWord ++ tailWord_2410463).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2410463).length < 2 ^ (prefixWord ++ tailWord_2410463).sum := by decide
  have hdescent : baseEnd_2410463 < baseStart_2410463 := by decide
  rcases family_descends (prefixWord ++ tailWord_2410463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2410478 : List Nat := [4, 1, 2, 1, 3, 2, 2, 1, 1, 5]
def baseStart_2410478 : Nat := 118140960795 + 2410478 * 2 ^ 59
def prefixEnd_2410478 : Nat := 4983230072969 + 3 ^ 40 * 2410478 * 2
def baseEnd_2410478 : Nat := 825155880725683484959613

theorem tailTrace_2410478 : CollatzResearch.WordTrace tailWord_2410478 prefixEnd_2410478 825155880725683484959613 := by
  unfold tailWord_2410478
  simp only [CollatzResearch.WordTrace]
  refine ⟨10989669420157169714030011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 58611570240838238474826725 10989669420157169714030011)
  ·
    refine ⟨16484504130235754571045017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10989669420157169714030011 16484504130235754571045017)
    ·
      refine ⟨12363378097676815928283763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16484504130235754571045017 12363378097676815928283763)
      ·
        refine ⟨18545067146515223892425645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12363378097676815928283763 18545067146515223892425645)
        ·
          refine ⟨6954400179943208959659617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18545067146515223892425645 6954400179943208959659617)
          ·
            refine ⟨5215800134957406719744713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6954400179943208959659617 5215800134957406719744713)
            ·
              refine ⟨3911850101218055039808535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5215800134957406719744713 3911850101218055039808535)
              ·
                refine ⟨5867775151827082559712803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3911850101218055039808535 5867775151827082559712803)
                ·
                  refine ⟨8801662727740623839569205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5867775151827082559712803 8801662727740623839569205)
                  ·
                    refine ⟨825155880725683484959613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8801662727740623839569205 825155880725683484959613)
                    ·
                      rfl

theorem cell22_2410478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 2, 2, 1, 1, 5].length) (baseStart_2410478 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2410478 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2410478 prefixEnd_2410478 := by exact prefixLift 2410478
  have htrace : WordTrace (prefixWord ++ tailWord_2410478) baseStart_2410478 baseEnd_2410478 := by
    simpa [prefixWord, tailWord_2410478, baseEnd_2410478] using wordTrace_append hprefix tailTrace_2410478
  have hstable : (prefixWord ++ tailWord_2410478).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2410478).length < 2 ^ (prefixWord ++ tailWord_2410478).sum := by decide
  have hdescent : baseEnd_2410478 < baseStart_2410478 := by decide
  rcases family_descends (prefixWord ++ tailWord_2410478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2410626 : List Nat := [3, 4, 15]
def baseStart_2410626 : Nat := 118140960795 + 2410626 * 2 ^ 59
def prefixEnd_2410626 : Nat := 4983230072969 + 3 ^ 40 * 2410626 * 2
def baseEnd_2410626 : Nat := 377323522702451043557

theorem tailTrace_2410626 : CollatzResearch.WordTrace tailWord_2410626 prefixEnd_2410626 377323522702451043557 := by
  unfold tailWord_2410626
  simp only [CollatzResearch.WordTrace]
  refine ⟨21980688341180294747156933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58615168909814119325751821 21980688341180294747156933)
  ·
    refine ⟨4121379063971305265091925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 21980688341180294747156933 4121379063971305265091925)
    ·
      refine ⟨377323522702451043557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 15 4121379063971305265091925 377323522702451043557)
      ·
        rfl

theorem cell22_2410626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 15].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 15].length) (baseStart_2410626 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2410626 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2410626 prefixEnd_2410626 := by exact prefixLift 2410626
  have htrace : WordTrace (prefixWord ++ tailWord_2410626) baseStart_2410626 baseEnd_2410626 := by
    simpa [prefixWord, tailWord_2410626, baseEnd_2410626] using wordTrace_append hprefix tailTrace_2410626
  have hstable : (prefixWord ++ tailWord_2410626).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2410626).length < 2 ^ (prefixWord ++ tailWord_2410626).sum := by decide
  have hdescent : baseEnd_2410626 < baseStart_2410626 := by decide
  rcases family_descends (prefixWord ++ tailWord_2410626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2410628 : List Nat := [2, 3, 2, 1, 2, 1, 1, 4, 2, 4]
def baseStart_2410628 : Nat := 118140960795 + 2410628 * 2 ^ 59
def prefixEnd_2410628 : Nat := 4983230072969 + 3 ^ 40 * 2410628 * 2
def baseEnd_2410628 : Nat := 825207228791133093709153

theorem tailTrace_2410628 : CollatzResearch.WordTrace tailWord_2410628 prefixEnd_2410628 825207228791133093709153 := by
  unfold tailWord_2410628
  simp only [CollatzResearch.WordTrace]
  refine ⟨43961413155356966665100269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58615217540475955553467025 43961413155356966665100269)
  ·
    refine ⟨16485529933258862499412601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43961413155356966665100269 16485529933258862499412601)
    ·
      refine ⟨12364147449944146874559451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16485529933258862499412601 12364147449944146874559451)
      ·
        refine ⟨18546221174916220311839177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12364147449944146874559451 18546221174916220311839177)
        ·
          refine ⟨13909665881187165233879383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18546221174916220311839177 13909665881187165233879383)
          ·
            refine ⟨20864498821780747850819075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13909665881187165233879383 20864498821780747850819075)
            ·
              refine ⟨31296748232671121776228613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20864498821780747850819075 31296748232671121776228613)
              ·
                refine ⟨5868140293625835333042865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 31296748232671121776228613 5868140293625835333042865)
                ·
                  refine ⟨4401105220219376499782149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5868140293625835333042865 4401105220219376499782149)
                  ·
                    refine ⟨825207228791133093709153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4401105220219376499782149 825207228791133093709153)
                    ·
                      rfl

theorem cell22_2410628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 1, 4, 2, 4].length) (baseStart_2410628 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2410628 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2410628 prefixEnd_2410628 := by exact prefixLift 2410628
  have htrace : WordTrace (prefixWord ++ tailWord_2410628) baseStart_2410628 baseEnd_2410628 := by
    simpa [prefixWord, tailWord_2410628, baseEnd_2410628] using wordTrace_append hprefix tailTrace_2410628
  have hstable : (prefixWord ++ tailWord_2410628).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2410628).length < 2 ^ (prefixWord ++ tailWord_2410628).sum := by decide
  have hdescent : baseEnd_2410628 < baseStart_2410628 := by decide
  rcases family_descends (prefixWord ++ tailWord_2410628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2410632 : List Nat := [2, 1, 3, 4, 1, 1, 4, 2, 4]
def baseStart_2410632 : Nat := 118140960795 + 2410632 * 2 ^ 59
def prefixEnd_2410632 : Nat := 4983230072969 + 3 ^ 40 * 2410632 * 2
def baseEnd_2410632 : Nat := 275069532690959472203047

theorem tailTrace_2410632 : CollatzResearch.WordTrace tailWord_2410632 prefixEnd_2410632 275069532690959472203047 := by
  unfold tailWord_2410632
  simp only [CollatzResearch.WordTrace]
  refine ⟨43961486101349721006673075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58615314801799628008897433 43961486101349721006673075)
  ·
    refine ⟨65942229152024581510009613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43961486101349721006673075 65942229152024581510009613)
    ·
      refine ⟨24728335932009218066253605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 65942229152024581510009613 24728335932009218066253605)
      ·
        refine ⟨4636562987251728387422551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 24728335932009218066253605 4636562987251728387422551)
        ·
          refine ⟨6954844480877592581133827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4636562987251728387422551 6954844480877592581133827)
          ·
            refine ⟨10432266721316388871700741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6954844480877592581133827 10432266721316388871700741)
            ·
              refine ⟨1956050010246822913443889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10432266721316388871700741 1956050010246822913443889)
              ·
                refine ⟨1467037507685117185082917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1956050010246822913443889 1467037507685117185082917)
                ·
                  refine ⟨275069532690959472203047, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1467037507685117185082917 275069532690959472203047)
                  ·
                    rfl

theorem cell22_2410632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 4, 2, 4].length) (baseStart_2410632 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2410632 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2410632 prefixEnd_2410632 := by exact prefixLift 2410632
  have htrace : WordTrace (prefixWord ++ tailWord_2410632) baseStart_2410632 baseEnd_2410632 := by
    simpa [prefixWord, tailWord_2410632, baseEnd_2410632] using wordTrace_append hprefix tailTrace_2410632
  have hstable : (prefixWord ++ tailWord_2410632).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2410632).length < 2 ^ (prefixWord ++ tailWord_2410632).sum := by decide
  have hdescent : baseEnd_2410632 < baseStart_2410632 := by decide
  rcases family_descends (prefixWord ++ tailWord_2410632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2410660 : List Nat := [2, 3, 1, 2, 4, 1, 3, 6]
def baseStart_2410660 : Nat := 118140960795 + 2410660 * 2 ^ 59
def prefixEnd_2410660 : Nat := 4983230072969 + 3 ^ 40 * 2410660 * 2
def baseEnd_2410660 : Nat := 91690909227232852989895

theorem tailTrace_2410660 : CollatzResearch.WordTrace tailWord_2410660 prefixEnd_2410660 91690909227232852989895 := by
  unfold tailWord_2410660
  simp only [CollatzResearch.WordTrace]
  refine ⟨43961996723299001397682717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58615995631065335196910289 43961996723299001397682717)
  ·
    refine ⟨16485748771237125524131019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43961996723299001397682717 16485748771237125524131019)
    ·
      refine ⟨24728623156855688286196529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16485748771237125524131019 24728623156855688286196529)
      ·
        refine ⟨18546467367641766214647397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24728623156855688286196529 18546467367641766214647397)
        ·
          refine ⟨3477462631432831165246387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18546467367641766214647397 3477462631432831165246387)
          ·
            refine ⟨5216193947149246747869581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3477462631432831165246387 5216193947149246747869581)
            ·
              refine ⟨1956072730180967530451093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5216193947149246747869581 1956072730180967530451093)
              ·
                refine ⟨91690909227232852989895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1956072730180967530451093 91690909227232852989895)
                ·
                  rfl

theorem cell22_2410660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 1, 3, 6].length) (baseStart_2410660 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2410660 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2410660 prefixEnd_2410660 := by exact prefixLift 2410660
  have htrace : WordTrace (prefixWord ++ tailWord_2410660) baseStart_2410660 baseEnd_2410660 := by
    simpa [prefixWord, tailWord_2410660, baseEnd_2410660] using wordTrace_append hprefix tailTrace_2410660
  have hstable : (prefixWord ++ tailWord_2410660).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2410660).length < 2 ^ (prefixWord ++ tailWord_2410660).sum := by decide
  have hdescent : baseEnd_2410660 < baseStart_2410660 := by decide
  rcases family_descends (prefixWord ++ tailWord_2410660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2410671 : List Nat := [1, 1, 2, 1, 2, 3, 1, 4, 7]
def baseStart_2410671 : Nat := 118140960795 + 2410671 * 2 ^ 59
def prefixEnd_2410671 : Nat := 4983230072969 + 3 ^ 40 * 2410671 * 2
def baseEnd_2410671 : Nat := 275073982856631771628007

theorem tailTrace_2410671 : CollatzResearch.WordTrace tailWord_2410671 prefixEnd_2410671 275073982856631771628007 := by
  unfold tailWord_2410671
  simp only [CollatzResearch.WordTrace]
  refine ⟨87924394649558151674015867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58616263099705434449343911 87924394649558151674015867)
  ·
    refine ⟨131886591974337227511023801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87924394649558151674015867 131886591974337227511023801)
    ·
      refine ⟨98914943980752920633267851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 131886591974337227511023801 98914943980752920633267851)
      ·
        refine ⟨148372415971129380949901777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98914943980752920633267851 148372415971129380949901777)
        ·
          refine ⟨111279311978347035712426333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 148372415971129380949901777 111279311978347035712426333)
          ·
            refine ⟨41729741991880138392159875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 111279311978347035712426333 41729741991880138392159875)
            ·
              refine ⟨62594612987820207588239813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41729741991880138392159875 62594612987820207588239813)
              ·
                refine ⟨11736489935216288922794965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 62594612987820207588239813 11736489935216288922794965)
                ·
                  refine ⟨275073982856631771628007, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11736489935216288922794965 275073982856631771628007)
                  ·
                    rfl

theorem cell22_2410671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 4, 7].length) (baseStart_2410671 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2410671 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2410671 prefixEnd_2410671 := by exact prefixLift 2410671
  have htrace : WordTrace (prefixWord ++ tailWord_2410671) baseStart_2410671 baseEnd_2410671 := by
    simpa [prefixWord, tailWord_2410671, baseEnd_2410671] using wordTrace_append hprefix tailTrace_2410671
  have hstable : (prefixWord ++ tailWord_2410671).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2410671).length < 2 ^ (prefixWord ++ tailWord_2410671).sum := by decide
  have hdescent : baseEnd_2410671 < baseStart_2410671 := by decide
  rcases family_descends (prefixWord ++ tailWord_2410671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2410688 : List Nat := [2, 1, 1, 2, 5, 2, 1, 1, 7]
def baseStart_2410688 : Nat := 118140960795 + 2410688 * 2 ^ 59
def prefixEnd_2410688 : Nat := 4983230072969 + 3 ^ 40 * 2410688 * 2
def baseEnd_2410688 : Nat := 275075922672437645736323

theorem tailTrace_2410688 : CollatzResearch.WordTrace tailWord_2410688 prefixEnd_2410688 275075922672437645736323 := by
  unfold tailWord_2410688
  simp only [CollatzResearch.WordTrace]
  refine ⟨43962507345248281788692359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58616676460331042384923145 43962507345248281788692359)
  ·
    refine ⟨65943761017872422683038539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43962507345248281788692359 65943761017872422683038539)
    ·
      refine ⟨98915641526808634024557809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65943761017872422683038539 98915641526808634024557809)
      ·
        refine ⟨74186731145106475518418357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 98915641526808634024557809 74186731145106475518418357)
        ·
          refine ⟨6955006044853732079851721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 74186731145106475518418357 6955006044853732079851721)
          ·
            refine ⟨5216254533640299059888791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6955006044853732079851721 5216254533640299059888791)
            ·
              refine ⟨7824381800460448589833187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5216254533640299059888791 7824381800460448589833187)
              ·
                refine ⟨11736572700690672884749781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7824381800460448589833187 11736572700690672884749781)
                ·
                  refine ⟨275075922672437645736323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11736572700690672884749781 275075922672437645736323)
                  ·
                    rfl

theorem cell22_2410688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 2, 1, 1, 7].length) (baseStart_2410688 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2410688 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2410688 prefixEnd_2410688 := by exact prefixLift 2410688
  have htrace : WordTrace (prefixWord ++ tailWord_2410688) baseStart_2410688 baseEnd_2410688 := by
    simpa [prefixWord, tailWord_2410688, baseEnd_2410688] using wordTrace_append hprefix tailTrace_2410688
  have hstable : (prefixWord ++ tailWord_2410688).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2410688).length < 2 ^ (prefixWord ++ tailWord_2410688).sum := by decide
  have hdescent : baseEnd_2410688 < baseStart_2410688 := by decide
  rcases family_descends (prefixWord ++ tailWord_2410688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2410692 : List Nat := [2, 3, 3, 1, 2, 2, 2, 1, 3, 3]
def baseStart_2410692 : Nat := 118140960795 + 2410692 * 2 ^ 59
def prefixEnd_2410692 : Nat := 4983230072969 + 3 ^ 40 * 2410692 * 2
def baseEnd_2410692 : Nat := 825229137299058260108957

theorem tailTrace_2410692 : CollatzResearch.WordTrace tailWord_2410692 prefixEnd_2410692 825229137299058260108957 := by
  unfold tailWord_2410692
  simp only [CollatzResearch.WordTrace]
  refine ⟨43962580291241036130265165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58616773721654714840353553 43962580291241036130265165)
  ·
    refine ⟨16485967609215388548849437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43962580291241036130265165 16485967609215388548849437)
    ·
      refine ⟨6182237853455770705818539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16485967609215388548849437 6182237853455770705818539)
      ·
        refine ⟨9273356780183656058727809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6182237853455770705818539 9273356780183656058727809)
        ·
          refine ⟨6955017585137742044045857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9273356780183656058727809 6955017585137742044045857)
          ·
            refine ⟨5216263188853306533034393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6955017585137742044045857 5216263188853306533034393)
            ·
              refine ⟨3912197391639979899775795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5216263188853306533034393 3912197391639979899775795)
              ·
                refine ⟨5868296087459969849663693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3912197391639979899775795 5868296087459969849663693)
                ·
                  refine ⟨2200611032797488693623885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5868296087459969849663693 2200611032797488693623885)
                  ·
                    refine ⟨825229137299058260108957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2200611032797488693623885 825229137299058260108957)
                    ·
                      rfl

theorem cell22_2410692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 2, 2, 1, 3, 3].length) (baseStart_2410692 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2410692 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2410692 prefixEnd_2410692 := by exact prefixLift 2410692
  have htrace : WordTrace (prefixWord ++ tailWord_2410692) baseStart_2410692 baseEnd_2410692 := by
    simpa [prefixWord, tailWord_2410692, baseEnd_2410692] using wordTrace_append hprefix tailTrace_2410692
  have hstable : (prefixWord ++ tailWord_2410692).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2410692).length < 2 ^ (prefixWord ++ tailWord_2410692).sum := by decide
  have hdescent : baseEnd_2410692 < baseStart_2410692 := by decide
  rcases family_descends (prefixWord ++ tailWord_2410692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2410735 : List Nat := [1, 1, 2, 1, 6, 1, 2, 3, 1, 4]
def baseStart_2410735 : Nat := 118140960795 + 2410735 * 2 ^ 59
def prefixEnd_2410735 : Nat := 4983230072969 + 3 ^ 40 * 2410735 * 2
def baseEnd_2410735 : Nat := 825243857077820481283825

theorem tailTrace_2410735 : CollatzResearch.WordTrace tailWord_2410735 prefixEnd_2410735 825243857077820481283825 := by
  unfold tailWord_2410735
  simp only [CollatzResearch.WordTrace]
  refine ⟨87926728921326290604345659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58617819280884193736230439 87926728921326290604345659)
  ·
    refine ⟨131890093381989435906518489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87926728921326290604345659 131890093381989435906518489)
    ·
      refine ⟨98917570036492076929888867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 131890093381989435906518489 98917570036492076929888867)
      ·
        refine ⟨148376355054738115394833301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98917570036492076929888867 148376355054738115394833301)
        ·
          refine ⟨6955141643190849159132811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 148376355054738115394833301 6955141643190849159132811)
          ·
            refine ⟨10432712464786273738699217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6955141643190849159132811 10432712464786273738699217)
            ·
              refine ⟨7824534348589705304024413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10432712464786273738699217 7824534348589705304024413)
              ·
                refine ⟨2934200380721139489009155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7824534348589705304024413 2934200380721139489009155)
                ·
                  refine ⟨4401300571081709233513733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2934200380721139489009155 4401300571081709233513733)
                  ·
                    refine ⟨825243857077820481283825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4401300571081709233513733 825243857077820481283825)
                    ·
                      rfl

theorem cell22_2410735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 2, 3, 1, 4].length) (baseStart_2410735 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2410735 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2410735 prefixEnd_2410735 := by exact prefixLift 2410735
  have htrace : WordTrace (prefixWord ++ tailWord_2410735) baseStart_2410735 baseEnd_2410735 := by
    simpa [prefixWord, tailWord_2410735, baseEnd_2410735] using wordTrace_append hprefix tailTrace_2410735
  have hstable : (prefixWord ++ tailWord_2410735).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2410735).length < 2 ^ (prefixWord ++ tailWord_2410735).sum := by decide
  have hdescent : baseEnd_2410735 < baseStart_2410735 := by decide
  rcases family_descends (prefixWord ++ tailWord_2410735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2410763 : List Nat := [1, 1, 1, 1, 5, 2, 1, 2, 4, 4]
def baseStart_2410763 : Nat := 118140960795 + 2410763 * 2 ^ 59
def prefixEnd_2410763 : Nat := 4983230072969 + 3 ^ 40 * 2410763 * 2
def baseEnd_2410763 : Nat := 825253442050037741583739

theorem tailTrace_2410763 : CollatzResearch.WordTrace tailWord_2410763 prefixEnd_2410763 825253442050037741583739 := by
  unfold tailWord_2410763
  simp only [CollatzResearch.WordTrace]
  refine ⟨87927750165224851386364943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58618500110149900924243295 87927750165224851386364943)
  ·
    refine ⟨131891625247837277079547415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87927750165224851386364943 131891625247837277079547415)
    ·
      refine ⟨197837437871755915619321123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131891625247837277079547415 197837437871755915619321123)
      ·
        refine ⟨296756156807633873428981685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 197837437871755915619321123 296756156807633873428981685)
        ·
          refine ⟨27820889700715675633967033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 296756156807633873428981685 27820889700715675633967033)
          ·
            refine ⟨20865667275536756725475275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27820889700715675633967033 20865667275536756725475275)
            ·
              refine ⟨31298500913305135088212913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20865667275536756725475275 31298500913305135088212913)
              ·
                refine ⟨23473875684978851316159685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31298500913305135088212913 23473875684978851316159685)
                ·
                  refine ⟨4401351690933534621779941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23473875684978851316159685 4401351690933534621779941)
                  ·
                    refine ⟨825253442050037741583739, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4401351690933534621779941 825253442050037741583739)
                    ·
                      rfl

theorem cell22_2410763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 1, 2, 4, 4].length) (baseStart_2410763 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2410763 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2410763 prefixEnd_2410763 := by exact prefixLift 2410763
  have htrace : WordTrace (prefixWord ++ tailWord_2410763) baseStart_2410763 baseEnd_2410763 := by
    simpa [prefixWord, tailWord_2410763, baseEnd_2410763] using wordTrace_append hprefix tailTrace_2410763
  have hstable : (prefixWord ++ tailWord_2410763).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2410763).length < 2 ^ (prefixWord ++ tailWord_2410763).sum := by decide
  have hdescent : baseEnd_2410763 < baseStart_2410763 := by decide
  rcases family_descends (prefixWord ++ tailWord_2410763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2410782 : List Nat := [4, 3, 2, 1, 1, 1, 1, 1, 3, 5]
def baseStart_2410782 : Nat := 118140960795 + 2410782 * 2 ^ 59
def prefixEnd_2410782 : Nat := 4983230072969 + 3 ^ 40 * 2410782 * 2
def baseEnd_2410782 : Nat := 825259946138328025358681

theorem tailTrace_2410782 : CollatzResearch.WordTrace tailWord_2410782 prefixEnd_2410782 825259946138328025358681 := by
  unfold tailWord_2410782
  simp only [CollatzResearch.WordTrace]
  refine ⟨10991055394019502203913325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 58618962101437345087537733 10991055394019502203913325)
  ·
    refine ⟨4121645772757313326467497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10991055394019502203913325 4121645772757313326467497)
    ·
      refine ⟨3091234329567984994850623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4121645772757313326467497 3091234329567984994850623)
      ·
        refine ⟨4636851494351977492275935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3091234329567984994850623 4636851494351977492275935)
        ·
          refine ⟨6955277241527966238413903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4636851494351977492275935 6955277241527966238413903)
          ·
            refine ⟨10432915862291949357620855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6955277241527966238413903 10432915862291949357620855)
            ·
              refine ⟨15649373793437924036431283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10432915862291949357620855 15649373793437924036431283)
              ·
                refine ⟨23474060690156886054646925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15649373793437924036431283 23474060690156886054646925)
                ·
                  refine ⟨8802772758808832270492597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23474060690156886054646925 8802772758808832270492597)
                  ·
                    refine ⟨825259946138328025358681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8802772758808832270492597 825259946138328025358681)
                    ·
                      rfl

theorem cell22_2410782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 1, 1, 3, 5].length) (baseStart_2410782 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2410782 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2410782 prefixEnd_2410782 := by exact prefixLift 2410782
  have htrace : WordTrace (prefixWord ++ tailWord_2410782) baseStart_2410782 baseEnd_2410782 := by
    simpa [prefixWord, tailWord_2410782, baseEnd_2410782] using wordTrace_append hprefix tailTrace_2410782
  have hstable : (prefixWord ++ tailWord_2410782).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2410782).length < 2 ^ (prefixWord ++ tailWord_2410782).sum := by decide
  have hdescent : baseEnd_2410782 < baseStart_2410782 := by decide
  rcases family_descends (prefixWord ++ tailWord_2410782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2410801 : List Nat := [1, 2, 2, 3, 5, 1, 2, 2, 4]
def baseStart_2410801 : Nat := 118140960795 + 2410801 * 2 ^ 59
def prefixEnd_2410801 : Nat := 4983230072969 + 3 ^ 40 * 2410801 * 2
def baseEnd_2410801 : Nat := 275088816742206103044541

theorem tailTrace_2410801 : CollatzResearch.WordTrace tailWord_2410801 prefixEnd_2410801 275088816742206103044541 := by
  unfold tailWord_2410801
  simp only [CollatzResearch.WordTrace]
  refine ⟨87929136139087183876248257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58619424092724789250832171 87929136139087183876248257)
  ·
    refine ⟨65946852104315387907186193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87929136139087183876248257 65946852104315387907186193)
    ·
      refine ⟨49460139078236540930389645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65946852104315387907186193 49460139078236540930389645)
      ·
        refine ⟨18547552154338702848896117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 49460139078236540930389645 18547552154338702848896117)
        ·
          refine ⟨1738833014469253392084011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 18547552154338702848896117 1738833014469253392084011)
          ·
            refine ⟨2608249521703880088126017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1738833014469253392084011 2608249521703880088126017)
            ·
              refine ⟨1956187141277910066094513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2608249521703880088126017 1956187141277910066094513)
              ·
                refine ⟨1467140355958432549570885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1956187141277910066094513 1467140355958432549570885)
                ·
                  refine ⟨275088816742206103044541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1467140355958432549570885 275088816742206103044541)
                  ·
                    rfl

theorem cell22_2410801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 5, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 5, 1, 2, 2, 4].length) (baseStart_2410801 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2410801 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2410801 prefixEnd_2410801 := by exact prefixLift 2410801
  have htrace : WordTrace (prefixWord ++ tailWord_2410801) baseStart_2410801 baseEnd_2410801 := by
    simpa [prefixWord, tailWord_2410801, baseEnd_2410801] using wordTrace_append hprefix tailTrace_2410801
  have hstable : (prefixWord ++ tailWord_2410801).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2410801).length < 2 ^ (prefixWord ++ tailWord_2410801).sum := by decide
  have hdescent : baseEnd_2410801 < baseStart_2410801 := by decide
  rcases family_descends (prefixWord ++ tailWord_2410801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2410808 : List Nat := [2, 1, 2, 1, 3, 1, 3, 1, 2, 6]
def baseStart_2410808 : Nat := 118140960795 + 2410808 * 2 ^ 59
def prefixEnd_2410808 : Nat := 4983230072969 + 3 ^ 40 * 2410808 * 2
def baseEnd_2410808 : Nat := 825268846469672624208601

theorem tailTrace_2410808 : CollatzResearch.WordTrace tailWord_2410808 prefixEnd_2410808 825268846469672624208601 := by
  unfold tailWord_2410808
  simp only [CollatzResearch.WordTrace]
  refine ⟨43964695725030912035876539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58619594300041216047835385 43964695725030912035876539)
  ·
    refine ⟨65947043587546368053814809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43964695725030912035876539 65947043587546368053814809)
    ·
      refine ⟨49460282690659776040361107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65947043587546368053814809 49460282690659776040361107)
      ·
        refine ⟨74190424035989664060541661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49460282690659776040361107 74190424035989664060541661)
        ·
          refine ⟨27821409013496124022703123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 74190424035989664060541661 27821409013496124022703123)
          ·
            refine ⟨41732113520244186034054685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27821409013496124022703123 41732113520244186034054685)
            ·
              refine ⟨15649542570091569762770507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 41732113520244186034054685 15649542570091569762770507)
              ·
                refine ⟨23474313855137354644155761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15649542570091569762770507 23474313855137354644155761)
                ·
                  refine ⟨17605735391353015983116821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23474313855137354644155761 17605735391353015983116821)
                  ·
                    refine ⟨825268846469672624208601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17605735391353015983116821 825268846469672624208601)
                    ·
                      rfl

theorem cell22_2410808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 3, 1, 2, 6].length) (baseStart_2410808 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2410808 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2410808 prefixEnd_2410808 := by exact prefixLift 2410808
  have htrace : WordTrace (prefixWord ++ tailWord_2410808) baseStart_2410808 baseEnd_2410808 := by
    simpa [prefixWord, tailWord_2410808, baseEnd_2410808] using wordTrace_append hprefix tailTrace_2410808
  have hstable : (prefixWord ++ tailWord_2410808).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2410808).length < 2 ^ (prefixWord ++ tailWord_2410808).sum := by decide
  have hdescent : baseEnd_2410808 < baseStart_2410808 := by decide
  rcases family_descends (prefixWord ++ tailWord_2410808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2410846 : List Nat := [4, 4, 2, 1, 1, 1, 9]
def baseStart_2410846 : Nat := 118140960795 + 2410846 * 2 ^ 59
def prefixEnd_2410846 : Nat := 4983230072969 + 3 ^ 40 * 2410846 * 2
def baseEnd_2410846 : Nat := 30565994616527895991055

theorem tailTrace_2410846 : CollatzResearch.WordTrace tailWord_2410846 prefixEnd_2410846 30565994616527895991055 := by
  unfold tailWord_2410846
  simp only [CollatzResearch.WordTrace]
  refine ⟨10991347177990519570204549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 58620518282616104374424261 10991347177990519570204549)
  ·
    refine ⟨2060877595873222419413353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10991347177990519570204549 2060877595873222419413353)
    ·
      refine ⟨1545658196904916814560015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2060877595873222419413353 1545658196904916814560015)
      ·
        refine ⟨2318487295357375221840023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1545658196904916814560015 2318487295357375221840023)
        ·
          refine ⟨3477730943036062832760035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2318487295357375221840023 3477730943036062832760035)
          ·
            refine ⟨5216596414554094249140053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3477730943036062832760035 5216596414554094249140053)
            ·
              refine ⟨30565994616527895991055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 5216596414554094249140053 30565994616527895991055)
              ·
                rfl

theorem cell22_2410846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 1, 9].length) (baseStart_2410846 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2410846 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2410846 prefixEnd_2410846 := by exact prefixLift 2410846
  have htrace : WordTrace (prefixWord ++ tailWord_2410846) baseStart_2410846 baseEnd_2410846 := by
    simpa [prefixWord, tailWord_2410846, baseEnd_2410846] using wordTrace_append hprefix tailTrace_2410846
  have hstable : (prefixWord ++ tailWord_2410846).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2410846).length < 2 ^ (prefixWord ++ tailWord_2410846).sum := by decide
  have hdescent : baseEnd_2410846 < baseStart_2410846 := by decide
  rcases family_descends (prefixWord ++ tailWord_2410846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2410855 : List Nat := [1, 1, 5, 1, 3, 1, 1, 2, 2, 5]
def baseStart_2410855 : Nat := 118140960795 + 2410855 * 2 ^ 59
def prefixEnd_2410855 : Nat := 4983230072969 + 3 ^ 40 * 2410855 * 2
def baseEnd_2410855 : Nat := 825284935530180168283457

theorem tailTrace_2410855 : CollatzResearch.WordTrace tailWord_2410855 prefixEnd_2410855 825284935530180168283457 := by
  unfold tailWord_2410855
  simp only [CollatzResearch.WordTrace]
  refine ⟨87931105680891551098714019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58620737120594367399142679 87931105680891551098714019)
  ·
    refine ⟨131896658521337326648071029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87931105680891551098714019 131896658521337326648071029)
    ·
      refine ⟨12365311736375374373256659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 131896658521337326648071029 12365311736375374373256659)
      ·
        refine ⟨18547967604563061559884989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12365311736375374373256659 18547967604563061559884989)
        ·
          refine ⟨6955487851711148084956871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18547967604563061559884989 6955487851711148084956871)
          ·
            refine ⟨10433231777566722127435307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6955487851711148084956871 10433231777566722127435307)
            ·
              refine ⟨15649847666350083191152961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10433231777566722127435307 15649847666350083191152961)
              ·
                refine ⟨11737385749762562393364721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15649847666350083191152961 11737385749762562393364721)
                ·
                  refine ⟨8803039312321921795023541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11737385749762562393364721 8803039312321921795023541)
                  ·
                    refine ⟨825284935530180168283457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8803039312321921795023541 825284935530180168283457)
                    ·
                      rfl

theorem cell22_2410855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 1, 2, 2, 5].length) (baseStart_2410855 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2410855 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2410855 prefixEnd_2410855 := by exact prefixLift 2410855
  have htrace : WordTrace (prefixWord ++ tailWord_2410855) baseStart_2410855 baseEnd_2410855 := by
    simpa [prefixWord, tailWord_2410855, baseEnd_2410855] using wordTrace_append hprefix tailTrace_2410855
  have hstable : (prefixWord ++ tailWord_2410855).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2410855).length < 2 ^ (prefixWord ++ tailWord_2410855).sum := by decide
  have hdescent : baseEnd_2410855 < baseStart_2410855 := by decide
  rcases family_descends (prefixWord ++ tailWord_2410855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2410887 : List Nat := [1, 1, 4, 2, 2, 1, 4, 2, 1, 4]
def baseStart_2410887 : Nat := 118140960795 + 2410887 * 2 ^ 59
def prefixEnd_2410887 : Nat := 4983230072969 + 3 ^ 40 * 2410887 * 2
def baseEnd_2410887 : Nat := 825295889784142751483359

theorem tailTrace_2410887 : CollatzResearch.WordTrace tailWord_2410887 prefixEnd_2410887 825295889784142751483359 := by
  unfold tailWord_2410887
  simp only [CollatzResearch.WordTrace]
  refine ⟨87932272816775620563878915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58621515211183747042585943 87932272816775620563878915)
  ·
    refine ⟨131898409225163430845818373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87932272816775620563878915 131898409225163430845818373)
    ·
      refine ⟨24730951729718143283590945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 131898409225163430845818373 24730951729718143283590945)
      ·
        refine ⟨18548213797288607462693209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24730951729718143283590945 18548213797288607462693209)
        ·
          refine ⟨13911160347966455597019907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18548213797288607462693209 13911160347966455597019907)
          ·
            refine ⟨20866740521949683395529861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13911160347966455597019907 20866740521949683395529861)
            ·
              refine ⟨3912513847865565636661849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20866740521949683395529861 3912513847865565636661849)
              ·
                refine ⟨2934385385899174227496387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3912513847865565636661849 2934385385899174227496387)
                ·
                  refine ⟨4401578078848761341244581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2934385385899174227496387 4401578078848761341244581)
                  ·
                    refine ⟨825295889784142751483359, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4401578078848761341244581 825295889784142751483359)
                    ·
                      rfl

theorem cell22_2410887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 4, 2, 1, 4].length) (baseStart_2410887 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2410887 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2410887 prefixEnd_2410887 := by exact prefixLift 2410887
  have htrace : WordTrace (prefixWord ++ tailWord_2410887) baseStart_2410887 baseEnd_2410887 := by
    simpa [prefixWord, tailWord_2410887, baseEnd_2410887] using wordTrace_append hprefix tailTrace_2410887
  have hstable : (prefixWord ++ tailWord_2410887).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2410887).length < 2 ^ (prefixWord ++ tailWord_2410887).sum := by decide
  have hdescent : baseEnd_2410887 < baseStart_2410887 := by decide
  rcases family_descends (prefixWord ++ tailWord_2410887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2410915 : List Nat := [1, 1, 1, 4, 1, 4, 1, 1, 4, 4]
def baseStart_2410915 : Nat := 118140960795 + 2410915 * 2 ^ 59
def prefixEnd_2410915 : Nat := 4983230072969 + 3 ^ 40 * 2410915 * 2
def baseEnd_2410915 : Nat := 825305474756360011783273

theorem tailTrace_2410915 : CollatzResearch.WordTrace tailWord_2410915 prefixEnd_2410915 825305474756360011783273 := by
  unfold tailWord_2410915
  simp only [CollatzResearch.WordTrace]
  refine ⟨87933294060674181345898199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58622196040449454230598799 87933294060674181345898199)
  ·
    refine ⟨131899941091011272018847299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87933294060674181345898199 131899941091011272018847299)
    ·
      refine ⟨197849911636516908028270949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131899941091011272018847299 197849911636516908028270949)
      ·
        refine ⟨37096858431846920255300803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 197849911636516908028270949 37096858431846920255300803)
        ·
          refine ⟨55645287647770380382951205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37096858431846920255300803 55645287647770380382951205)
          ·
            refine ⟨10433491433956946321803351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 55645287647770380382951205 10433491433956946321803351)
            ·
              refine ⟨15650237150935419482705027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10433491433956946321803351 15650237150935419482705027)
              ·
                refine ⟨23475355726403129224057541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15650237150935419482705027 23475355726403129224057541)
                ·
                  refine ⟨4401629198700586729510789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23475355726403129224057541 4401629198700586729510789)
                  ·
                    refine ⟨825305474756360011783273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4401629198700586729510789 825305474756360011783273)
                    ·
                      rfl

theorem cell22_2410915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 1, 1, 4, 4].length) (baseStart_2410915 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2410915 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2410915 prefixEnd_2410915 := by exact prefixLift 2410915
  have htrace : WordTrace (prefixWord ++ tailWord_2410915) baseStart_2410915 baseEnd_2410915 := by
    simpa [prefixWord, tailWord_2410915, baseEnd_2410915] using wordTrace_append hprefix tailTrace_2410915
  have hstable : (prefixWord ++ tailWord_2410915).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2410915).length < 2 ^ (prefixWord ++ tailWord_2410915).sum := by decide
  have hdescent : baseEnd_2410915 < baseStart_2410915 := by decide
  rcases family_descends (prefixWord ++ tailWord_2410915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2410917 : List Nat := [1, 3, 1, 2, 1, 1, 4, 4, 2, 3]
def baseStart_2410917 : Nat := 118140960795 + 2410917 * 2 ^ 59
def prefixEnd_2410917 : Nat := 4983230072969 + 3 ^ 40 * 2410917 * 2
def baseEnd_2410917 : Nat := 825306159397232673233267

theorem tailTrace_2410917 : CollatzResearch.WordTrace tailWord_2410917 prefixEnd_2410917 825306159397232673233267 := by
  unfold tailWord_2410917
  simp only [CollatzResearch.WordTrace]
  refine ⟨87933367006666935687471005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58622244671111290458314003 87933367006666935687471005)
  ·
    refine ⟨32975012627500100882801627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 87933367006666935687471005 32975012627500100882801627)
    ·
      refine ⟨49462518941250151324202441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32975012627500100882801627 49462518941250151324202441)
      ·
        refine ⟨37096889205937613493151831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49462518941250151324202441 37096889205937613493151831)
        ·
          refine ⟨55645333808906420239727747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37096889205937613493151831 55645333808906420239727747)
          ·
            refine ⟨83468000713359630359591621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55645333808906420239727747 83468000713359630359591621)
            ·
              refine ⟨15650250133754930692423429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 83468000713359630359591621 15650250133754930692423429)
              ·
                refine ⟨2934421900079049504829393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15650250133754930692423429 2934421900079049504829393)
                ·
                  refine ⟨2200816425059287128622045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2934421900079049504829393 2200816425059287128622045)
                  ·
                    refine ⟨825306159397232673233267, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2200816425059287128622045 825306159397232673233267)
                    ·
                      rfl

theorem cell22_2410917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 4, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 4, 4, 2, 3].length) (baseStart_2410917 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2410917 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2410917 prefixEnd_2410917 := by exact prefixLift 2410917
  have htrace : WordTrace (prefixWord ++ tailWord_2410917) baseStart_2410917 baseEnd_2410917 := by
    simpa [prefixWord, tailWord_2410917, baseEnd_2410917] using wordTrace_append hprefix tailTrace_2410917
  have hstable : (prefixWord ++ tailWord_2410917).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2410917).length < 2 ^ (prefixWord ++ tailWord_2410917).sum := by decide
  have hdescent : baseEnd_2410917 < baseStart_2410917 := by decide
  rcases family_descends (prefixWord ++ tailWord_2410917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2410930 : List Nat := [3, 2, 1, 1, 1, 1, 6, 7]
def baseStart_2410930 : Nat := 118140960795 + 2410930 * 2 ^ 59
def prefixEnd_2410930 : Nat := 4983230072969 + 3 ^ 40 * 2410930 * 2
def baseEnd_2410930 : Nat := 91701178840322774739803

theorem tailTrace_2410930 : CollatzResearch.WordTrace tailWord_2410930 prefixEnd_2410930 91701178840322774739803 := by
  unfold tailWord_2410930
  simp only [CollatzResearch.WordTrace]
  refine ⟨21983460288904959726923561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58622560770413225938462829 21983460288904959726923561)
  ·
    refine ⟨16487595216678719795192671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21983460288904959726923561 16487595216678719795192671)
    ·
      refine ⟨24731392825018079692789007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16487595216678719795192671 24731392825018079692789007)
      ·
        refine ⟨37097089237527119539183511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24731392825018079692789007 37097089237527119539183511)
        ·
          refine ⟨55645633856290679308775267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37097089237527119539183511 55645633856290679308775267)
          ·
            refine ⟨83468450784436018963162901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55645633856290679308775267 83468450784436018963162901)
            ·
              refine ⟨3912583630520438388898261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 83468450784436018963162901 3912583630520438388898261)
              ·
                refine ⟨91701178840322774739803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3912583630520438388898261 91701178840322774739803)
                ·
                  rfl

theorem cell22_2410930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 6, 7].length) (baseStart_2410930 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2410930 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2410930 prefixEnd_2410930 := by exact prefixLift 2410930
  have htrace : WordTrace (prefixWord ++ tailWord_2410930) baseStart_2410930 baseEnd_2410930 := by
    simpa [prefixWord, tailWord_2410930, baseEnd_2410930] using wordTrace_append hprefix tailTrace_2410930
  have hstable : (prefixWord ++ tailWord_2410930).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2410930).length < 2 ^ (prefixWord ++ tailWord_2410930).sum := by decide
  have hdescent : baseEnd_2410930 < baseStart_2410930 := by decide
  rcases family_descends (prefixWord ++ tailWord_2410930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2411037 : List Nat := [1, 4, 2, 2, 1, 2, 1, 3, 6]
def baseStart_2411037 : Nat := 118140960795 + 2411037 * 2 ^ 59
def prefixEnd_2411037 : Nat := 4983230072969 + 3 ^ 40 * 2411037 * 2
def baseEnd_2411037 : Nat := 275115745949864120077633

theorem tailTrace_2411037 : CollatzResearch.WordTrace tailWord_2411037 prefixEnd_2411037 275115745949864120077633 := by
  unfold tailWord_2411037
  simp only [CollatzResearch.WordTrace]
  refine ⟨87937743766232196181839365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58625162510821464121226243 87937743766232196181839365)
  ·
    refine ⟨16488326956168536784094881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 87937743766232196181839365 16488326956168536784094881)
    ·
      refine ⟨12366245217126402588071161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16488326956168536784094881 12366245217126402588071161)
      ·
        refine ⟨9274683912844801941053371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12366245217126402588071161 9274683912844801941053371)
        ·
          refine ⟨13912025869267202911580057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9274683912844801941053371 13912025869267202911580057)
          ·
            refine ⟨10434019401950402183685043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13912025869267202911580057 10434019401950402183685043)
            ·
              refine ⟨15651029102925603275527565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10434019401950402183685043 15651029102925603275527565)
              ·
                refine ⟨5869135913597101228322837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15651029102925603275527565 5869135913597101228322837)
                ·
                  refine ⟨275115745949864120077633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5869135913597101228322837 275115745949864120077633)
                  ·
                    rfl

theorem cell22_2411037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 1, 3, 6].length) (baseStart_2411037 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2411037 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2411037 prefixEnd_2411037 := by exact prefixLift 2411037
  have htrace : WordTrace (prefixWord ++ tailWord_2411037) baseStart_2411037 baseEnd_2411037 := by
    simpa [prefixWord, tailWord_2411037, baseEnd_2411037] using wordTrace_append hprefix tailTrace_2411037
  have hstable : (prefixWord ++ tailWord_2411037).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2411037).length < 2 ^ (prefixWord ++ tailWord_2411037).sum := by decide
  have hdescent : baseEnd_2411037 < baseStart_2411037 := by decide
  rcases family_descends (prefixWord ++ tailWord_2411037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2411069 : List Nat := [1, 4, 1, 3, 2, 1, 1, 2, 4, 3]
def baseStart_2411069 : Nat := 118140960795 + 2411069 * 2 ^ 59
def prefixEnd_2411069 : Nat := 4983230072969 + 3 ^ 40 * 2411069 * 2
def baseEnd_2411069 : Nat := 825358192103554943432801

theorem tailTrace_2411069 : CollatzResearch.WordTrace tailWord_2411069 prefixEnd_2411069 825358192103554943432801 := by
  unfold tailWord_2411069
  simp only [CollatzResearch.WordTrace]
  refine ⟨87938910902116265647004261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58625940601410843764669507 87938910902116265647004261)
  ·
    refine ⟨16488545794146799808813299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 87938910902116265647004261 16488545794146799808813299)
    ·
      refine ⟨24732818691220199713219949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16488545794146799808813299 24732818691220199713219949)
      ·
        refine ⟨9274807009207574892457481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24732818691220199713219949 9274807009207574892457481)
        ·
          refine ⟨6956105256905681169343111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9274807009207574892457481 6956105256905681169343111)
          ·
            refine ⟨10434157885358521754014667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6956105256905681169343111 10434157885358521754014667)
            ·
              refine ⟨15651236828037782631022001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10434157885358521754014667 15651236828037782631022001)
              ·
                refine ⟨11738427621028336973266501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15651236828037782631022001 11738427621028336973266501)
                ·
                  refine ⟨2200955178942813182487469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11738427621028336973266501 2200955178942813182487469)
                  ·
                    refine ⟨825358192103554943432801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2200955178942813182487469 825358192103554943432801)
                    ·
                      rfl

theorem cell22_2411069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 1, 2, 4, 3].length) (baseStart_2411069 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2411069 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2411069 prefixEnd_2411069 := by exact prefixLift 2411069
  have htrace : WordTrace (prefixWord ++ tailWord_2411069) baseStart_2411069 baseEnd_2411069 := by
    simpa [prefixWord, tailWord_2411069, baseEnd_2411069] using wordTrace_append hprefix tailTrace_2411069
  have hstable : (prefixWord ++ tailWord_2411069).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2411069).length < 2 ^ (prefixWord ++ tailWord_2411069).sum := by decide
  have hdescent : baseEnd_2411069 < baseStart_2411069 := by decide
  rcases family_descends (prefixWord ++ tailWord_2411069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2411082 : List Nat := [3, 1, 2, 1, 1, 6, 8]
def baseStart_2411082 : Nat := 118140960795 + 2411082 * 2 ^ 59
def prefixEnd_2411082 : Nat := 4983230072969 + 3 ^ 40 * 2411082 * 2
def baseEnd_2411082 : Nat := 30568986750712120105843

theorem tailTrace_2411082 : CollatzResearch.WordTrace tailWord_2411082 prefixEnd_2411082 30568986750712120105843 := by
  unfold tailWord_2411082
  simp only [CollatzResearch.WordTrace]
  refine ⟨21984846262767292216806875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58626256700712779244818333 21984846262767292216806875)
  ·
    refine ⟨32977269394150938325210313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21984846262767292216806875 32977269394150938325210313)
    ·
      refine ⟨24732952045613203743907735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32977269394150938325210313 24732952045613203743907735)
      ·
        refine ⟨37099428068419805615861603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24732952045613203743907735 37099428068419805615861603)
        ·
          refine ⟨55649142102629708423792405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37099428068419805615861603 55649142102629708423792405)
          ·
            refine ⟨2608553536060767582365269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 55649142102629708423792405 2608553536060767582365269)
            ·
              refine ⟨30568986750712120105843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2608553536060767582365269 30568986750712120105843)
              ·
                rfl

theorem cell22_2411082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 6, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 6, 8].length) (baseStart_2411082 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2411082 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2411082 prefixEnd_2411082 := by exact prefixLift 2411082
  have htrace : WordTrace (prefixWord ++ tailWord_2411082) baseStart_2411082 baseEnd_2411082 := by
    simpa [prefixWord, tailWord_2411082, baseEnd_2411082] using wordTrace_append hprefix tailTrace_2411082
  have hstable : (prefixWord ++ tailWord_2411082).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2411082).length < 2 ^ (prefixWord ++ tailWord_2411082).sum := by decide
  have hdescent : baseEnd_2411082 < baseStart_2411082 := by decide
  rcases family_descends (prefixWord ++ tailWord_2411082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2411114 : List Nat := [3, 1, 3, 2, 1, 1, 2, 1, 5, 3]
def baseStart_2411114 : Nat := 118140960795 + 2411114 * 2 ^ 59
def prefixEnd_2411114 : Nat := 4983230072969 + 3 ^ 40 * 2411114 * 2
def baseEnd_2411114 : Nat := 825373596523189826057663

theorem tailTrace_2411114 : CollatzResearch.WordTrace tailWord_2411114 prefixEnd_2411114 825373596523189826057663 := by
  unfold tailWord_2411114
  simp only [CollatzResearch.WordTrace]
  refine ⟨21985138046738309583098099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58627034791302158888261597 21985138046738309583098099)
  ·
    refine ⟨32977707070107464374647149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21985138046738309583098099 32977707070107464374647149)
    ·
      refine ⟨12366640151290299140492681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32977707070107464374647149 12366640151290299140492681)
      ·
        refine ⟨9274980113467724355369511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12366640151290299140492681 9274980113467724355369511)
        ·
          refine ⟨13912470170201586533054267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9274980113467724355369511 13912470170201586533054267)
          ·
            refine ⟨20868705255302379799581401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13912470170201586533054267 20868705255302379799581401)
            ·
              refine ⟨15651528941476784849686051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20868705255302379799581401 15651528941476784849686051)
              ·
                refine ⟨23477293412215177274529077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15651528941476784849686051 23477293412215177274529077)
                ·
                  refine ⟨2200996257395172869487101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 23477293412215177274529077 2200996257395172869487101)
                  ·
                    refine ⟨825373596523189826057663, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2200996257395172869487101 825373596523189826057663)
                    ·
                      rfl

theorem cell22_2411114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 2, 1, 5, 3].length) (baseStart_2411114 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2411114 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2411114 prefixEnd_2411114 := by exact prefixLift 2411114
  have htrace : WordTrace (prefixWord ++ tailWord_2411114) baseStart_2411114 baseEnd_2411114 := by
    simpa [prefixWord, tailWord_2411114, baseEnd_2411114] using wordTrace_append hprefix tailTrace_2411114
  have hstable : (prefixWord ++ tailWord_2411114).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2411114).length < 2 ^ (prefixWord ++ tailWord_2411114).sum := by decide
  have hdescent : baseEnd_2411114 < baseStart_2411114 := by decide
  rcases family_descends (prefixWord ++ tailWord_2411114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2411191 : List Nat := [1, 1, 3, 1, 6, 1, 1, 3, 1, 4]
def baseStart_2411191 : Nat := 118140960795 + 2411191 * 2 ^ 59
def prefixEnd_2411191 : Nat := 4983230072969 + 3 ^ 40 * 2411191 * 2
def baseEnd_2411191 : Nat := 825399955196787291882427

theorem tailTrace_2411191 : CollatzResearch.WordTrace tailWord_2411191 prefixEnd_2411191 825399955196787291882427 := by
  unfold tailWord_2411191
  simp only [CollatzResearch.WordTrace]
  refine ⟨87943360607674280482945427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58628907071782853655296951 87943360607674280482945427)
  ·
    refine ⟨131915040911511420724418141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87943360607674280482945427 131915040911511420724418141)
    ·
      refine ⟨49468140341816782771656803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 131915040911511420724418141 49468140341816782771656803)
      ·
        refine ⟨74202210512725174157485205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49468140341816782771656803 74202210512725174157485205)
        ·
          refine ⟨3478228617783992538632119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 74202210512725174157485205 3478228617783992538632119)
          ·
            refine ⟨5217342926675988807948179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3478228617783992538632119 5217342926675988807948179)
            ·
              refine ⟨7826014390013983211922269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5217342926675988807948179 7826014390013983211922269)
              ·
                refine ⟨2934755396255243704470851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7826014390013983211922269 2934755396255243704470851)
                ·
                  refine ⟨4402133094382865556706277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2934755396255243704470851 4402133094382865556706277)
                  ·
                    refine ⟨825399955196787291882427, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4402133094382865556706277 825399955196787291882427)
                    ·
                      rfl

theorem cell22_2411191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 1, 1, 3, 1, 4].length) (baseStart_2411191 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2411191 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2411191 prefixEnd_2411191 := by exact prefixLift 2411191
  have htrace : WordTrace (prefixWord ++ tailWord_2411191) baseStart_2411191 baseEnd_2411191 := by
    simpa [prefixWord, tailWord_2411191, baseEnd_2411191] using wordTrace_append hprefix tailTrace_2411191
  have hstable : (prefixWord ++ tailWord_2411191).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2411191).length < 2 ^ (prefixWord ++ tailWord_2411191).sum := by decide
  have hdescent : baseEnd_2411191 < baseStart_2411191 := by decide
  rcases family_descends (prefixWord ++ tailWord_2411191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2411217 : List Nat := [1, 2, 2, 1, 2, 3, 2, 9]
def baseStart_2411217 : Nat := 118140960795 + 2411217 * 2 ^ 59
def prefixEnd_2411217 : Nat := 4983230072969 + 3 ^ 40 * 2411217 * 2
def baseEnd_2411217 : Nat := 91712095058681321192483

theorem tailTrace_2411217 : CollatzResearch.WordTrace tailWord_2411217 prefixEnd_2411217 91712095058681321192483 := by
  unfold tailWord_2411217
  simp only [CollatzResearch.WordTrace]
  refine ⟨87944308905580086923391905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58629539270386724615594603 87944308905580086923391905)
  ·
    refine ⟨65958231679185065192543929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87944308905580086923391905 65958231679185065192543929)
    ·
      refine ⟨49468673759388798894407947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65958231679185065192543929 49468673759388798894407947)
      ·
        refine ⟨74203010639083198341611921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49468673759388798894407947 74203010639083198341611921)
        ·
          refine ⟨55652257979312398756208941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 74203010639083198341611921 55652257979312398756208941)
          ·
            refine ⟨20869596742242149533578353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 55652257979312398756208941 20869596742242149533578353)
            ·
              refine ⟨15652197556681612150183765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20869596742242149533578353 15652197556681612150183765)
              ·
                refine ⟨91712095058681321192483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 15652197556681612150183765 91712095058681321192483)
                ·
                  rfl

theorem cell22_2411217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 2, 9].length) (baseStart_2411217 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2411217 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2411217 prefixEnd_2411217 := by exact prefixLift 2411217
  have htrace : WordTrace (prefixWord ++ tailWord_2411217) baseStart_2411217 baseEnd_2411217 := by
    simpa [prefixWord, tailWord_2411217, baseEnd_2411217] using wordTrace_append hprefix tailTrace_2411217
  have hstable : (prefixWord ++ tailWord_2411217).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2411217).length < 2 ^ (prefixWord ++ tailWord_2411217).sum := by decide
  have hdescent : baseEnd_2411217 < baseStart_2411217 := by decide
  rcases family_descends (prefixWord ++ tailWord_2411217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2411232 : List Nat := [2, 1, 1, 3, 1, 2, 1, 1, 1, 9]
def baseStart_2411232 : Nat := 118140960795 + 2411232 * 2 ^ 59
def prefixEnd_2411232 : Nat := 4983230072969 + 3 ^ 40 * 2411232 * 2
def baseEnd_2411232 : Nat := 825413990334676851607301

theorem tailTrace_2411232 : CollatzResearch.WordTrace tailWord_2411232 prefixEnd_2411232 825413990334676851607301 := by
  unfold tailWord_2411232
  simp only [CollatzResearch.WordTrace]
  refine ⟨43972428000262872242593975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58629904000350496323458633 43972428000262872242593975)
  ·
    refine ⟨65958642000394308363890963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43972428000262872242593975 65958642000394308363890963)
    ·
      refine ⟨98937963000591462545836445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65958642000394308363890963 98937963000591462545836445)
      ·
        refine ⟨37101736125221798454688667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 98937963000591462545836445 37101736125221798454688667)
        ·
          refine ⟨55652604187832697682033001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37101736125221798454688667 55652604187832697682033001)
          ·
            refine ⟨41739453140874523261524751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55652604187832697682033001 41739453140874523261524751)
            ·
              refine ⟨62609179711311784892287127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41739453140874523261524751 62609179711311784892287127)
              ·
                refine ⟨93913769566967677338430691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 62609179711311784892287127 93913769566967677338430691)
                ·
                  refine ⟨140870654350451516007646037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 93913769566967677338430691 140870654350451516007646037)
                  ·
                    refine ⟨825413990334676851607301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 140870654350451516007646037 825413990334676851607301)
                    ·
                      rfl

theorem cell22_2411232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 1, 1, 9].length) (baseStart_2411232 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2411232 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2411232 prefixEnd_2411232 := by exact prefixLift 2411232
  have htrace : WordTrace (prefixWord ++ tailWord_2411232) baseStart_2411232 baseEnd_2411232 := by
    simpa [prefixWord, tailWord_2411232, baseEnd_2411232] using wordTrace_append hprefix tailTrace_2411232
  have hstable : (prefixWord ++ tailWord_2411232).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2411232).length < 2 ^ (prefixWord ++ tailWord_2411232).sum := by decide
  have hdescent : baseEnd_2411232 < baseStart_2411232 := by decide
  rcases family_descends (prefixWord ++ tailWord_2411232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2411240 : List Nat := [2, 1, 4, 1, 5, 1, 1, 3, 4]
def baseStart_2411240 : Nat := 118140960795 + 2411240 * 2 ^ 59
def prefixEnd_2411240 : Nat := 4983230072969 + 3 ^ 40 * 2411240 * 2
def baseEnd_2411240 : Nat := 275138909632722499135759

theorem tailTrace_2411240 : CollatzResearch.WordTrace tailWord_2411240 prefixEnd_2411240 275138909632722499135759 := by
  unfold tailWord_2411240
  simp only [CollatzResearch.WordTrace]
  refine ⟨43972573892248380925739587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58630098522997841234319449 43972573892248380925739587)
  ·
    refine ⟨65958860838372571388609381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43972573892248380925739587 65958860838372571388609381)
    ·
      refine ⟨12367286407194857135364259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 65958860838372571388609381 12367286407194857135364259)
      ·
        refine ⟨18550929610792285703046389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12367286407194857135364259 18550929610792285703046389)
        ·
          refine ⟨1739149651011776784660599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 18550929610792285703046389 1739149651011776784660599)
          ·
            refine ⟨2608724476517665176990899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1739149651011776784660599 2608724476517665176990899)
            ·
              refine ⟨3913086714776497765486349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2608724476517665176990899 3913086714776497765486349)
              ·
                refine ⟨1467407518041186662057381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3913086714776497765486349 1467407518041186662057381)
                ·
                  refine ⟨275138909632722499135759, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1467407518041186662057381 275138909632722499135759)
                  ·
                    rfl

theorem cell22_2411240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 5, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 5, 1, 1, 3, 4].length) (baseStart_2411240 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2411240 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2411240 prefixEnd_2411240 := by exact prefixLift 2411240
  have htrace : WordTrace (prefixWord ++ tailWord_2411240) baseStart_2411240 baseEnd_2411240 := by
    simpa [prefixWord, tailWord_2411240, baseEnd_2411240] using wordTrace_append hprefix tailTrace_2411240
  have hstable : (prefixWord ++ tailWord_2411240).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2411240).length < 2 ^ (prefixWord ++ tailWord_2411240).sum := by decide
  have hdescent : baseEnd_2411240 < baseStart_2411240 := by decide
  rcases family_descends (prefixWord ++ tailWord_2411240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2411279 : List Nat := [1, 1, 2, 1, 1, 1, 7, 3, 5]
def baseStart_2411279 : Nat := 118140960795 + 2411279 * 2 ^ 59
def prefixEnd_2411279 : Nat := 4983230072969 + 3 ^ 40 * 2411279 * 2
def baseEnd_2411279 : Nat := 275143359798394798560719

theorem tailTrace_2411279 : CollatzResearch.WordTrace tailWord_2411279 prefixEnd_2411279 275143359798394798560719 := by
  unfold tailWord_2411279
  simp only [CollatzResearch.WordTrace]
  refine ⟨87946570231355471512148891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58631046820903647674765927 87946570231355471512148891)
  ·
    refine ⟨131919855347033207268223337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87946570231355471512148891 131919855347033207268223337)
    ·
      refine ⟨98939891510274905451167503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 131919855347033207268223337 98939891510274905451167503)
      ·
        refine ⟨148409837265412358176751255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98939891510274905451167503 148409837265412358176751255)
        ·
          refine ⟨222614755898118537265126883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 148409837265412358176751255 222614755898118537265126883)
          ·
            refine ⟨333922133847177805897690325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 222614755898118537265126883 333922133847177805897690325)
            ·
              refine ⟨7826300012043229825727117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 333922133847177805897690325 7826300012043229825727117)
              ·
                refine ⟨2934862504516211184647669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7826300012043229825727117 2934862504516211184647669)
                ·
                  refine ⟨275143359798394798560719, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2934862504516211184647669 275143359798394798560719)
                  ·
                    rfl

theorem cell22_2411279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 7, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 7, 3, 5].length) (baseStart_2411279 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2411279 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2411279 prefixEnd_2411279 := by exact prefixLift 2411279
  have htrace : WordTrace (prefixWord ++ tailWord_2411279) baseStart_2411279 baseEnd_2411279 := by
    simpa [prefixWord, tailWord_2411279, baseEnd_2411279] using wordTrace_append hprefix tailTrace_2411279
  have hstable : (prefixWord ++ tailWord_2411279).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2411279).length < 2 ^ (prefixWord ++ tailWord_2411279).sum := by decide
  have hdescent : baseEnd_2411279 < baseStart_2411279 := by decide
  rcases family_descends (prefixWord ++ tailWord_2411279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2411317 : List Nat := [1, 3, 3, 1, 3, 3, 2, 2, 1, 3]
def baseStart_2411317 : Nat := 118140960795 + 2411317 * 2 ^ 59
def prefixEnd_2411317 : Nat := 4983230072969 + 3 ^ 40 * 2411317 * 2
def baseEnd_2411317 : Nat := 825443087571764963232041

theorem tailTrace_2411317 : CollatzResearch.WordTrace tailWord_2411317 prefixEnd_2411317 825443087571764963232041 := by
  unfold tailWord_2411317
  simp only [CollatzResearch.WordTrace]
  refine ⟨87947956205217804002032205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58631970803478536001354803 87947956205217804002032205)
  ·
    refine ⟨32980483576956676500762077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 87947956205217804002032205 32980483576956676500762077)
    ·
      refine ⟨12367681341358753687785779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32980483576956676500762077 12367681341358753687785779)
      ·
        refine ⟨18551522012038130531678669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12367681341358753687785779 18551522012038130531678669)
        ·
          refine ⟨6956820754514298949379501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18551522012038130531678669 6956820754514298949379501)
          ·
            refine ⟨2608807782942862106017313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6956820754514298949379501 2608807782942862106017313)
            ·
              refine ⟨1956605837207146579512985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2608807782942862106017313 1956605837207146579512985)
              ·
                refine ⟨1467454377905359934634739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1956605837207146579512985 1467454377905359934634739)
                ·
                  refine ⟨2201181566858039901952109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1467454377905359934634739 2201181566858039901952109)
                  ·
                    refine ⟨825443087571764963232041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2201181566858039901952109 825443087571764963232041)
                    ·
                      rfl

theorem cell22_2411317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 3, 2, 2, 1, 3].length) (baseStart_2411317 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2411317 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2411317 prefixEnd_2411317 := by exact prefixLift 2411317
  have htrace : WordTrace (prefixWord ++ tailWord_2411317) baseStart_2411317 baseEnd_2411317 := by
    simpa [prefixWord, tailWord_2411317, baseEnd_2411317] using wordTrace_append hprefix tailTrace_2411317
  have hstable : (prefixWord ++ tailWord_2411317).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2411317).length < 2 ^ (prefixWord ++ tailWord_2411317).sum := by decide
  have hdescent : baseEnd_2411317 < baseStart_2411317 := by decide
  rcases family_descends (prefixWord ++ tailWord_2411317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2411324 : List Nat := [2, 2, 2, 2, 1, 1, 1, 5, 6]
def baseStart_2411324 : Nat := 118140960795 + 2411324 * 2 ^ 59
def prefixEnd_2411324 : Nat := 4983230072969 + 3 ^ 40 * 2411324 * 2
def baseEnd_2411324 : Nat := 275148494604939759435673

theorem tailTrace_2411324 : CollatzResearch.WordTrace tailWord_2411324 prefixEnd_2411324 275148494604939759435673 := by
  unfold tailWord_2411324
  simp only [CollatzResearch.WordTrace]
  refine ⟨43974105758096222098768513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58632141010794962798358017 43974105758096222098768513)
  ·
    refine ⟨32980579318572166574076385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43974105758096222098768513 32980579318572166574076385)
    ·
      refine ⟨24735434488929124930557289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32980579318572166574076385 24735434488929124930557289)
      ·
        refine ⟨18551575866696843697917967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24735434488929124930557289 18551575866696843697917967)
        ·
          refine ⟨27827363800045265546876951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18551575866696843697917967 27827363800045265546876951)
          ·
            refine ⟨41741045700067898320315427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27827363800045265546876951 41741045700067898320315427)
            ·
              refine ⟨62611568550101847480473141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41741045700067898320315427 62611568550101847480473141)
              ·
                refine ⟨5869834551572048201294357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 62611568550101847480473141 5869834551572048201294357)
                ·
                  refine ⟨275148494604939759435673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5869834551572048201294357 275148494604939759435673)
                  ·
                    rfl

theorem cell22_2411324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 5, 6].length) (baseStart_2411324 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2411324 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2411324 prefixEnd_2411324 := by exact prefixLift 2411324
  have htrace : WordTrace (prefixWord ++ tailWord_2411324) baseStart_2411324 baseEnd_2411324 := by
    simpa [prefixWord, tailWord_2411324, baseEnd_2411324] using wordTrace_append hprefix tailTrace_2411324
  have hstable : (prefixWord ++ tailWord_2411324).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2411324).length < 2 ^ (prefixWord ++ tailWord_2411324).sum := by decide
  have hdescent : baseEnd_2411324 < baseStart_2411324 := by decide
  rcases family_descends (prefixWord ++ tailWord_2411324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2411448 : List Nat := [2, 1, 2, 1, 2, 4, 4, 1, 5]
def baseStart_2411448 : Nat := 118140960795 + 2411448 * 2 ^ 59
def prefixEnd_2411448 : Nat := 4983230072969 + 3 ^ 40 * 2411448 * 2
def baseEnd_2411448 : Nat := 275162643849641429402213

theorem tailTrace_2411448 : CollatzResearch.WordTrace tailWord_2411448 prefixEnd_2411448 275162643849641429402213 := by
  unfold tailWord_2411448
  simp only [CollatzResearch.WordTrace]
  refine ⟨43976367083871606687525499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58635156111828808916700665 43976367083871606687525499)
  ·
    refine ⟨65964550625807410031288249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43976367083871606687525499 65964550625807410031288249)
    ·
      refine ⟨49473412969355557523466187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65964550625807410031288249 49473412969355557523466187)
      ·
        refine ⟨74210119454033336285199281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49473412969355557523466187 74210119454033336285199281)
        ·
          refine ⟨55657589590525002213899461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 74210119454033336285199281 55657589590525002213899461)
          ·
            refine ⟨10435798048223437915106149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 55657589590525002213899461 10435798048223437915106149)
            ·
              refine ⟨1956712134041894609082403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10435798048223437915106149 1956712134041894609082403)
              ·
                refine ⟨2935068201062841913623605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1956712134041894609082403 2935068201062841913623605)
                ·
                  refine ⟨275162643849641429402213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2935068201062841913623605 275162643849641429402213)
                  ·
                    rfl

theorem cell22_2411448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 4, 1, 5].length) (baseStart_2411448 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2411448 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2411448 prefixEnd_2411448 := by exact prefixLift 2411448
  have htrace : WordTrace (prefixWord ++ tailWord_2411448) baseStart_2411448 baseEnd_2411448 := by
    simpa [prefixWord, tailWord_2411448, baseEnd_2411448] using wordTrace_append hprefix tailTrace_2411448
  have hstable : (prefixWord ++ tailWord_2411448).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2411448).length < 2 ^ (prefixWord ++ tailWord_2411448).sum := by decide
  have hdescent : baseEnd_2411448 < baseStart_2411448 := by decide
  rcases family_descends (prefixWord ++ tailWord_2411448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2411491 : List Nat := [1, 1, 1, 6, 1, 1, 1, 2, 3, 5]
def baseStart_2411491 : Nat := 118140960795 + 2411491 * 2 ^ 59
def prefixEnd_2411491 : Nat := 4983230072969 + 3 ^ 40 * 2411491 * 2
def baseEnd_2411491 : Nat := 825502651327686509381507

theorem tailTrace_2411491 : CollatzResearch.WordTrace tailWord_2411491 prefixEnd_2411491 825502651327686509381507 := by
  unfold tailWord_2411491
  simp only [CollatzResearch.WordTrace]
  refine ⟨87954302506587431718866327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58636201671058287812577551 87954302506587431718866327)
  ·
    refine ⟨131931453759881147578299491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87954302506587431718866327 131931453759881147578299491)
    ·
      refine ⟨197897180639821721367449237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131931453759881147578299491 197897180639821721367449237)
      ·
        refine ⟨9276430342491643189099183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 197897180639821721367449237 9276430342491643189099183)
        ·
          refine ⟨13914645513737464783648775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9276430342491643189099183 13914645513737464783648775)
          ·
            refine ⟨20871968270606197175473163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13914645513737464783648775 20871968270606197175473163)
            ·
              refine ⟨31307952405909295763209745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20871968270606197175473163 31307952405909295763209745)
              ·
                refine ⟨23480964304431971822407309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31307952405909295763209745 23480964304431971822407309)
                ·
                  refine ⟨8805361614161989433402741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23480964304431971822407309 8805361614161989433402741)
                  ·
                    refine ⟨825502651327686509381507, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8805361614161989433402741 825502651327686509381507)
                    ·
                      rfl

theorem cell22_2411491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 1, 2, 3, 5].length) (baseStart_2411491 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2411491 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2411491 prefixEnd_2411491 := by exact prefixLift 2411491
  have htrace : WordTrace (prefixWord ++ tailWord_2411491) baseStart_2411491 baseEnd_2411491 := by
    simpa [prefixWord, tailWord_2411491, baseEnd_2411491] using wordTrace_append hprefix tailTrace_2411491
  have hstable : (prefixWord ++ tailWord_2411491).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2411491).length < 2 ^ (prefixWord ++ tailWord_2411491).sum := by decide
  have hdescent : baseEnd_2411491 < baseStart_2411491 := by decide
  rcases family_descends (prefixWord ++ tailWord_2411491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2411559 : List Nat := [1, 1, 7, 1, 1, 2, 3, 1, 2, 3]
def baseStart_2411559 : Nat := 118140960795 + 2411559 * 2 ^ 59
def prefixEnd_2411559 : Nat := 4983230072969 + 3 ^ 40 * 2411559 * 2
def baseEnd_2411559 : Nat := 825525929117356998681299

theorem tailTrace_2411559 : CollatzResearch.WordTrace tailWord_2411559 prefixEnd_2411559 825525929117356998681299 := by
  unfold tailWord_2411559
  simp only [CollatzResearch.WordTrace]
  refine ⟨87956782670341079332341731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58637855113560719554894487 87956782670341079332341731)
  ·
    refine ⟨131935174005511618998512597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87956782670341079332341731 131935174005511618998512597)
    ·
      refine ⟨3092230640754178570277639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 131935174005511618998512597 3092230640754178570277639)
      ·
        refine ⟨4638345961131267855416459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3092230640754178570277639 4638345961131267855416459)
        ·
          refine ⟨6957518941696901783124689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4638345961131267855416459 6957518941696901783124689)
          ·
            refine ⟨5218139206272676337343517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6957518941696901783124689 5218139206272676337343517)
            ·
              refine ⟨1956802202352253626503819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5218139206272676337343517 1956802202352253626503819)
              ·
                refine ⟨2935203303528380439755729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1956802202352253626503819 2935203303528380439755729)
                ·
                  refine ⟨2201402477646285329816797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2935203303528380439755729 2201402477646285329816797)
                  ·
                    refine ⟨825525929117356998681299, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2201402477646285329816797 825525929117356998681299)
                    ·
                      rfl

theorem cell22_2411559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 2, 3, 1, 2, 3].length) (baseStart_2411559 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2411559 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2411559 prefixEnd_2411559 := by exact prefixLift 2411559
  have htrace : WordTrace (prefixWord ++ tailWord_2411559) baseStart_2411559 baseEnd_2411559 := by
    simpa [prefixWord, tailWord_2411559, baseEnd_2411559] using wordTrace_append hprefix tailTrace_2411559
  have hstable : (prefixWord ++ tailWord_2411559).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2411559).length < 2 ^ (prefixWord ++ tailWord_2411559).sum := by decide
  have hdescent : baseEnd_2411559 < baseStart_2411559 := by decide
  rcases family_descends (prefixWord ++ tailWord_2411559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2411572 : List Nat := [2, 5, 1, 2, 1, 3, 2, 6]
def baseStart_2411572 : Nat := 118140960795 + 2411572 * 2 ^ 59
def prefixEnd_2411572 : Nat := 4983230072969 + 3 ^ 40 * 2411572 * 2
def baseEnd_2411572 : Nat := 91725597698114366456251

theorem tailTrace_2411572 : CollatzResearch.WordTrace tailWord_2411572 prefixEnd_2411572 91725597698114366456251 := by
  unfold tailWord_2411572
  simp only [CollatzResearch.WordTrace]
  refine ⟨43978628409646991276282485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58638171212862655035043313 43978628409646991276282485)
  ·
    refine ⟨4122996413404405432151483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 43978628409646991276282485 4122996413404405432151483)
    ·
      refine ⟨6184494620106608148227225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4122996413404405432151483 6184494620106608148227225)
      ·
        refine ⟨4638370965079956111170419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6184494620106608148227225 4638370965079956111170419)
        ·
          refine ⟨6957556447619934166755629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4638370965079956111170419 6957556447619934166755629)
          ·
            refine ⟨2609083667857475312533361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6957556447619934166755629 2609083667857475312533361)
            ·
              refine ⟨1956812750893106484400021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2609083667857475312533361 1956812750893106484400021)
              ·
                refine ⟨91725597698114366456251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1956812750893106484400021 91725597698114366456251)
                ·
                  rfl

theorem cell22_2411572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 3, 2, 6].length) (baseStart_2411572 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2411572 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2411572 prefixEnd_2411572 := by exact prefixLift 2411572
  have htrace : WordTrace (prefixWord ++ tailWord_2411572) baseStart_2411572 baseEnd_2411572 := by
    simpa [prefixWord, tailWord_2411572, baseEnd_2411572] using wordTrace_append hprefix tailTrace_2411572
  have hstable : (prefixWord ++ tailWord_2411572).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2411572).length < 2 ^ (prefixWord ++ tailWord_2411572).sum := by decide
  have hdescent : baseEnd_2411572 < baseStart_2411572 := by decide
  rcases family_descends (prefixWord ++ tailWord_2411572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2411630 : List Nat := [4, 1, 2, 2, 1, 3, 1, 1, 3, 4]
def baseStart_2411630 : Nat := 118140960795 + 2411630 * 2 ^ 59
def prefixEnd_2411630 : Nat := 4983230072969 + 3 ^ 40 * 2411630 * 2
def baseEnd_2411630 : Nat := 825550233868336480156081

theorem tailTrace_2411630 : CollatzResearch.WordTrace tailWord_2411630 prefixEnd_2411630 825550233868336480156081 := by
  unfold tailWord_2411630
  simp only [CollatzResearch.WordTrace]
  refine ⟨10994921531635482307272043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 58639581502055905638784229 10994921531635482307272043)
  ·
    refine ⟨16492382297453223460908065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10994921531635482307272043 16492382297453223460908065)
    ·
      refine ⟨12369286723089917595681049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16492382297453223460908065 12369286723089917595681049)
      ·
        refine ⟨9276965042317438196760787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12369286723089917595681049 9276965042317438196760787)
        ·
          refine ⟨13915447563476157295141181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9276965042317438196760787 13915447563476157295141181)
          ·
            refine ⟨5218292836303558985677943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13915447563476157295141181 5218292836303558985677943)
            ·
              refine ⟨7827439254455338478516915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5218292836303558985677943 7827439254455338478516915)
              ·
                refine ⟨11741158881683007717775373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7827439254455338478516915 11741158881683007717775373)
                ·
                  refine ⟨4402934580631127894165765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11741158881683007717775373 4402934580631127894165765)
                  ·
                    refine ⟨825550233868336480156081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4402934580631127894165765 825550233868336480156081)
                    ·
                      rfl

theorem cell22_2411630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 3, 1, 1, 3, 4].length) (baseStart_2411630 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2411630 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2411630 prefixEnd_2411630 := by exact prefixLift 2411630
  have htrace : WordTrace (prefixWord ++ tailWord_2411630) baseStart_2411630 baseEnd_2411630 := by
    simpa [prefixWord, tailWord_2411630, baseEnd_2411630] using wordTrace_append hprefix tailTrace_2411630
  have hstable : (prefixWord ++ tailWord_2411630).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2411630).length < 2 ^ (prefixWord ++ tailWord_2411630).sum := by decide
  have hdescent : baseEnd_2411630 < baseStart_2411630 := by decide
  rcases family_descends (prefixWord ++ tailWord_2411630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2411643 : List Nat := [1, 1, 1, 1, 1, 4, 1, 3, 6, 3]
def baseStart_2411643 : Nat := 118140960795 + 2411643 * 2 ^ 59
def prefixEnd_2411643 : Nat := 4983230072969 + 3 ^ 40 * 2411643 * 2
def baseEnd_2411643 : Nat := 825554684034008779581041

theorem tailTrace_2411643 : CollatzResearch.WordTrace tailWord_2411643 prefixEnd_2411643 825554684034008779581041 := by
  unfold tailWord_2411643
  simp only [CollatzResearch.WordTrace]
  refine ⟨87959846402036761678399583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58639897601357841118933055 87959846402036761678399583)
  ·
    refine ⟨131939769603055142517599375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87959846402036761678399583 131939769603055142517599375)
    ·
      refine ⟨197909654404582713776399063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131939769603055142517599375 197909654404582713776399063)
      ·
        refine ⟨296864481606874070664598595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 197909654404582713776399063 296864481606874070664598595)
        ·
          refine ⟨445296722410311105996897893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 296864481606874070664598595 445296722410311105996897893)
          ·
            refine ⟨83493135451933332374418355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 445296722410311105996897893 83493135451933332374418355)
            ·
              refine ⟨125239703177899998561627533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 83493135451933332374418355 125239703177899998561627533)
              ·
                refine ⟨46964888691712499460610325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 125239703177899998561627533 46964888691712499460610325)
                ·
                  refine ⟨2201479157424023412216109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 46964888691712499460610325 2201479157424023412216109)
                  ·
                    refine ⟨825554684034008779581041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2201479157424023412216109 825554684034008779581041)
                    ·
                      rfl

theorem cell22_2411643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 3, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 3, 6, 3].length) (baseStart_2411643 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2411643 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2411643 prefixEnd_2411643 := by exact prefixLift 2411643
  have htrace : WordTrace (prefixWord ++ tailWord_2411643) baseStart_2411643 baseEnd_2411643 := by
    simpa [prefixWord, tailWord_2411643, baseEnd_2411643] using wordTrace_append hprefix tailTrace_2411643
  have hstable : (prefixWord ++ tailWord_2411643).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2411643).length < 2 ^ (prefixWord ++ tailWord_2411643).sum := by decide
  have hdescent : baseEnd_2411643 < baseStart_2411643 := by decide
  rcases family_descends (prefixWord ++ tailWord_2411643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2411645 : List Nat := [1, 4, 1, 1, 3, 1, 2, 5, 4]
def baseStart_2411645 : Nat := 118140960795 + 2411645 * 2 ^ 59
def prefixEnd_2411645 : Nat := 4983230072969 + 3 ^ 40 * 2411645 * 2
def baseEnd_2411645 : Nat := 275185122891627147010345

theorem tailTrace_2411645 : CollatzResearch.WordTrace tailWord_2411645 prefixEnd_2411645 275185122891627147010345 := by
  unfold tailWord_2411645
  simp only [CollatzResearch.WordTrace]
  refine ⟨87959919348029516019972389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58639946232019677346648259 87959919348029516019972389)
  ·
    refine ⟨16492484877755534253744823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 87959919348029516019972389 16492484877755534253744823)
    ·
      refine ⟨24738727316633301380617235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16492484877755534253744823 24738727316633301380617235)
      ·
        refine ⟨37108090974949952070925853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24738727316633301380617235 37108090974949952070925853)
        ·
          refine ⟨13915534115606232026597195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37108090974949952070925853 13915534115606232026597195)
          ·
            refine ⟨20873301173409348039895793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13915534115606232026597195 20873301173409348039895793)
            ·
              refine ⟨15654975880057011029921845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20873301173409348039895793 15654975880057011029921845)
              ·
                refine ⟨1467653988755344784055173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 15654975880057011029921845 1467653988755344784055173)
                ·
                  refine ⟨275185122891627147010345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1467653988755344784055173 275185122891627147010345)
                  ·
                    rfl

theorem cell22_2411645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 2, 5, 4].length) (baseStart_2411645 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2411645 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2411645 prefixEnd_2411645 := by exact prefixLift 2411645
  have htrace : WordTrace (prefixWord ++ tailWord_2411645) baseStart_2411645 baseEnd_2411645 := by
    simpa [prefixWord, tailWord_2411645, baseEnd_2411645] using wordTrace_append hprefix tailTrace_2411645
  have hstable : (prefixWord ++ tailWord_2411645).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2411645).length < 2 ^ (prefixWord ++ tailWord_2411645).sum := by decide
  have hdescent : baseEnd_2411645 < baseStart_2411645 := by decide
  rcases family_descends (prefixWord ++ tailWord_2411645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2411662 : List Nat := [4, 1, 1, 3, 2, 2, 1, 4, 4]
def baseStart_2411662 : Nat := 118140960795 + 2411662 * 2 ^ 59
def prefixEnd_2411662 : Nat := 4983230072969 + 3 ^ 40 * 2411662 * 2
def baseEnd_2411662 : Nat := 275187062707433021118661

theorem tailTrace_2411662 : CollatzResearch.WordTrace tailWord_2411662 prefixEnd_2411662 275187062707433021118661 := by
  unfold tailWord_2411662
  simp only [CollatzResearch.WordTrace]
  refine ⟨10995067423620990990417655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 58640359592645285282227493 10995067423620990990417655)
  ·
    refine ⟨16492601135431486485626483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10995067423620990990417655 16492601135431486485626483)
    ·
      refine ⟨24738901703147229728439725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16492601135431486485626483 24738901703147229728439725)
      ·
        refine ⟨9277088138680211148164897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24738901703147229728439725 9277088138680211148164897)
        ·
          refine ⟨6957816104010158361123673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9277088138680211148164897 6957816104010158361123673)
          ·
            refine ⟨5218362078007618770842755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6957816104010158361123673 5218362078007618770842755)
            ·
              refine ⟨7827543117011428156264133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5218362078007618770842755 7827543117011428156264133)
              ·
                refine ⟨1467664334439642779299525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7827543117011428156264133 1467664334439642779299525)
                ·
                  refine ⟨275187062707433021118661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1467664334439642779299525 275187062707433021118661)
                  ·
                    rfl

theorem cell22_2411662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 2, 1, 4, 4].length) (baseStart_2411662 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2411662 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2411662 prefixEnd_2411662 := by exact prefixLift 2411662
  have htrace : WordTrace (prefixWord ++ tailWord_2411662) baseStart_2411662 baseEnd_2411662 := by
    simpa [prefixWord, tailWord_2411662, baseEnd_2411662] using wordTrace_append hprefix tailTrace_2411662
  have hstable : (prefixWord ++ tailWord_2411662).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2411662).length < 2 ^ (prefixWord ++ tailWord_2411662).sum := by decide
  have hdescent : baseEnd_2411662 < baseStart_2411662 := by decide
  rcases family_descends (prefixWord ++ tailWord_2411662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2411722 : List Nat := [3, 1, 2, 1, 3, 3, 2, 1, 3, 3]
def baseStart_2411722 : Nat := 118140960795 + 2411722 * 2 ^ 59
def prefixEnd_2411722 : Nat := 4983230072969 + 3 ^ 40 * 2411722 * 2
def baseEnd_2411722 : Nat := 825581727348478906855799

theorem tailTrace_2411722 : CollatzResearch.WordTrace tailWord_2411722 prefixEnd_2411722 825581727348478906855799 := by
  unfold tailWord_2411722
  simp only [CollatzResearch.WordTrace]
  refine ⟨21990681942187639542631355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58641818512500372113683613 21990681942187639542631355)
  ·
    refine ⟨32986022913281459313947033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21990681942187639542631355 32986022913281459313947033)
    ·
      refine ⟨24739517184961094485460275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32986022913281459313947033 24739517184961094485460275)
      ·
        refine ⟨37109275777441641728190413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24739517184961094485460275 37109275777441641728190413)
        ·
          refine ⟨13915978416540615648071405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37109275777441641728190413 13915978416540615648071405)
          ·
            refine ⟨5218491906202730868026777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13915978416540615648071405 5218491906202730868026777)
            ·
              refine ⟨3913868929652048151020083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5218491906202730868026777 3913868929652048151020083)
              ·
                refine ⟨5870803394478072226530125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3913868929652048151020083 5870803394478072226530125)
                ·
                  refine ⟨2201551272929277084948797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5870803394478072226530125 2201551272929277084948797)
                  ·
                    refine ⟨825581727348478906855799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2201551272929277084948797 825581727348478906855799)
                    ·
                      rfl

theorem cell22_2411722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 3, 2, 1, 3, 3].length) (baseStart_2411722 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2411722 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2411722 prefixEnd_2411722 := by exact prefixLift 2411722
  have htrace : WordTrace (prefixWord ++ tailWord_2411722) baseStart_2411722 baseEnd_2411722 := by
    simpa [prefixWord, tailWord_2411722, baseEnd_2411722] using wordTrace_append hprefix tailTrace_2411722
  have hstable : (prefixWord ++ tailWord_2411722).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2411722).length < 2 ^ (prefixWord ++ tailWord_2411722).sum := by decide
  have hdescent : baseEnd_2411722 < baseStart_2411722 := by decide
  rcases family_descends (prefixWord ++ tailWord_2411722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2411829 : List Nat := [1, 3, 3, 1, 2, 3, 2, 2, 2, 3]
def baseStart_2411829 : Nat := 118140960795 + 2411829 * 2 ^ 59
def prefixEnd_2411829 : Nat := 4983230072969 + 3 ^ 40 * 2411829 * 2
def baseEnd_2411829 : Nat := 825618355635166294430471

theorem tailTrace_2411829 : CollatzResearch.WordTrace tailWord_2411829 prefixEnd_2411829 825618355635166294430471 := by
  unfold tailWord_2411829
  simp only [CollatzResearch.WordTrace]
  refine ⟨87966630379362915444670541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58644420252908610296447027 87966630379362915444670541)
  ·
    refine ⟨32987486392261093291751453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 87966630379362915444670541 32987486392261093291751453)
    ·
      refine ⟨12370307397097909984406795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32987486392261093291751453 12370307397097909984406795)
      ·
        refine ⟨18555461095646864976610193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12370307397097909984406795 18555461095646864976610193)
        ·
          refine ⟨13916595821735148732457645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18555461095646864976610193 13916595821735148732457645)
          ·
            refine ⟨5218723433150680774671617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13916595821735148732457645 5218723433150680774671617)
            ·
              refine ⟨3914042574863010581003713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5218723433150680774671617 3914042574863010581003713)
              ·
                refine ⟨2935531931147257935752785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3914042574863010581003713 2935531931147257935752785)
                ·
                  refine ⟨2201648948360443451814589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2935531931147257935752785 2201648948360443451814589)
                  ·
                    refine ⟨825618355635166294430471, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2201648948360443451814589 825618355635166294430471)
                    ·
                      rfl

theorem cell22_2411829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 3, 2, 2, 2, 3].length) (baseStart_2411829 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2411829 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2411829 prefixEnd_2411829 := by exact prefixLift 2411829
  have htrace : WordTrace (prefixWord ++ tailWord_2411829) baseStart_2411829 baseEnd_2411829 := by
    simpa [prefixWord, tailWord_2411829, baseEnd_2411829] using wordTrace_append hprefix tailTrace_2411829
  have hstable : (prefixWord ++ tailWord_2411829).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2411829).length < 2 ^ (prefixWord ++ tailWord_2411829).sum := by decide
  have hdescent : baseEnd_2411829 < baseStart_2411829 := by decide
  rcases family_descends (prefixWord ++ tailWord_2411829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2411857 : List Nat := [1, 2, 2, 1, 4, 1, 3, 2, 3, 3]
def baseStart_2411857 : Nat := 118140960795 + 2411857 * 2 ^ 59
def prefixEnd_2411857 : Nat := 4983230072969 + 3 ^ 40 * 2411857 * 2
def baseEnd_2411857 : Nat := 825627940607383554730385

theorem tailTrace_2411857 : CollatzResearch.WordTrace tailWord_2411857 prefixEnd_2411857 825627940607383554730385 := by
  unfold tailWord_2411857
  simp only [CollatzResearch.WordTrace]
  refine ⟨87967651623261476226689825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58645101082174317484459883 87967651623261476226689825)
  ·
    refine ⟨65975738717446107170017369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87967651623261476226689825 65975738717446107170017369)
    ·
      refine ⟨49481804038084580377513027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65975738717446107170017369 49481804038084580377513027)
      ·
        refine ⟨74222706057126870566269541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49481804038084580377513027 74222706057126870566269541)
        ·
          refine ⟨13916757385711288231175539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 74222706057126870566269541 13916757385711288231175539)
          ·
            refine ⟨20875136078566932346763309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13916757385711288231175539 20875136078566932346763309)
            ·
              refine ⟨7828176029462599630036241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20875136078566932346763309 7828176029462599630036241)
              ·
                refine ⟨5871132022096949722527181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7828176029462599630036241 5871132022096949722527181)
                ·
                  refine ⟨2201674508286356145947693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5871132022096949722527181 2201674508286356145947693)
                  ·
                    refine ⟨825627940607383554730385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2201674508286356145947693 825627940607383554730385)
                    ·
                      rfl

theorem cell22_2411857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 3, 2, 3, 3].length) (baseStart_2411857 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2411857 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2411857 prefixEnd_2411857 := by exact prefixLift 2411857
  have htrace : WordTrace (prefixWord ++ tailWord_2411857) baseStart_2411857 baseEnd_2411857 := by
    simpa [prefixWord, tailWord_2411857, baseEnd_2411857] using wordTrace_append hprefix tailTrace_2411857
  have hstable : (prefixWord ++ tailWord_2411857).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2411857).length < 2 ^ (prefixWord ++ tailWord_2411857).sum := by decide
  have hdescent : baseEnd_2411857 < baseStart_2411857 := by decide
  rcases family_descends (prefixWord ++ tailWord_2411857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2411915 : List Nat := [1, 1, 1, 1, 4, 3, 1, 4, 6]
def baseStart_2411915 : Nat := 118140960795 + 2411915 * 2 ^ 59
def prefixEnd_2411915 : Nat := 4983230072969 + 3 ^ 40 * 2411915 * 2
def baseEnd_2411915 : Nat := 275215931730896912260069

theorem tailTrace_2411915 : CollatzResearch.WordTrace tailWord_2411915 prefixEnd_2411915 275215931730896912260069 := by
  unfold tailWord_2411915
  simp only [CollatzResearch.WordTrace]
  refine ⟨87969767057051352132301199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58646511371367568088200799 87969767057051352132301199)
  ·
    refine ⟨131954650585577028198451799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87969767057051352132301199 131954650585577028198451799)
    ·
      refine ⟨197931975878365542297677699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131954650585577028198451799 197931975878365542297677699)
      ·
        refine ⟨296897963817548313446516549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 197931975878365542297677699 296897963817548313446516549)
        ·
          refine ⟨55668368215790308771221853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 296897963817548313446516549 55668368215790308771221853)
          ·
            refine ⟨20875638080921365789208195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 55668368215790308771221853 20875638080921365789208195)
            ·
              refine ⟨31313457121382048683812293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20875638080921365789208195 31313457121382048683812293)
              ·
                refine ⟨5871273210259134128214805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 31313457121382048683812293 5871273210259134128214805)
                ·
                  refine ⟨275215931730896912260069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5871273210259134128214805 275215931730896912260069)
                  ·
                    rfl

theorem cell22_2411915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 1, 4, 6].length) (baseStart_2411915 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2411915 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2411915 prefixEnd_2411915 := by exact prefixLift 2411915
  have htrace : WordTrace (prefixWord ++ tailWord_2411915) baseStart_2411915 baseEnd_2411915 := by
    simpa [prefixWord, tailWord_2411915, baseEnd_2411915] using wordTrace_append hprefix tailTrace_2411915
  have hstable : (prefixWord ++ tailWord_2411915).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2411915).length < 2 ^ (prefixWord ++ tailWord_2411915).sum := by decide
  have hdescent : baseEnd_2411915 < baseStart_2411915 := by decide
  rcases family_descends (prefixWord ++ tailWord_2411915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2411949 : List Nat := [1, 5, 2, 2, 1, 1, 3, 1, 6]
def baseStart_2411949 : Nat := 118140960795 + 2411949 * 2 ^ 59
def prefixEnd_2411949 : Nat := 4983230072969 + 3 ^ 40 * 2411949 * 2
def baseEnd_2411949 : Nat := 275219811362508660476701

theorem tailTrace_2411949 : CollatzResearch.WordTrace tailWord_2411949 prefixEnd_2411949 275219811362508660476701 := by
  unfold tailWord_2411949
  simp only [CollatzResearch.WordTrace]
  refine ⟨87971007138928175939038901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58647338092618783959359267 87971007138928175939038901)
  ·
    refine ⟨8247281919274516494284897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 87971007138928175939038901 8247281919274516494284897)
    ·
      refine ⟨6185461439455887370713673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8247281919274516494284897 6185461439455887370713673)
      ·
        refine ⟨4639096079591915528035255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6185461439455887370713673 4639096079591915528035255)
        ·
          refine ⟨6958644119387873292052883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4639096079591915528035255 6958644119387873292052883)
          ·
            refine ⟨10437966179081809938079325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6958644119387873292052883 10437966179081809938079325)
            ·
              refine ⟨3914237317155678726779747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10437966179081809938079325 3914237317155678726779747)
              ·
                refine ⟨5871355975733518090169621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3914237317155678726779747 5871355975733518090169621)
                ·
                  refine ⟨275219811362508660476701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5871355975733518090169621 275219811362508660476701)
                  ·
                    rfl

theorem cell22_2411949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 3, 1, 6].length) (baseStart_2411949 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2411949 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2411949 prefixEnd_2411949 := by exact prefixLift 2411949
  have htrace : WordTrace (prefixWord ++ tailWord_2411949) baseStart_2411949 baseEnd_2411949 := by
    simpa [prefixWord, tailWord_2411949, baseEnd_2411949] using wordTrace_append hprefix tailTrace_2411949
  have hstable : (prefixWord ++ tailWord_2411949).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2411949).length < 2 ^ (prefixWord ++ tailWord_2411949).sum := by decide
  have hdescent : baseEnd_2411949 < baseStart_2411949 := by decide
  rcases family_descends (prefixWord ++ tailWord_2411949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2411960 : List Nat := [2, 1, 2, 1, 2, 2, 3, 9]
def baseStart_2411960 : Nat := 118140960795 + 2411960 * 2 ^ 59
def prefixEnd_2411960 : Nat := 4983230072969 + 3 ^ 40 * 2411960 * 2
def baseEnd_2411960 : Nat := 91740355512480624378341

theorem tailTrace_2411960 : CollatzResearch.WordTrace tailWord_2411960 prefixEnd_2411960 91740355512480624378341 := by
  unfold tailWord_2411960
  simp only [CollatzResearch.WordTrace]
  refine ⟨43985704170944162408844667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58647605561258883211792889 43985704170944162408844667)
  ·
    refine ⟨65978556256416243613267001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43985704170944162408844667 65978556256416243613267001)
    ·
      refine ⟨49483917192312182709950251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65978556256416243613267001 49483917192312182709950251)
      ·
        refine ⟨74225875788468274064925377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49483917192312182709950251 74225875788468274064925377)
        ·
          refine ⟨55669406841351205548694033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 74225875788468274064925377 55669406841351205548694033)
          ·
            refine ⟨41752055131013404161520525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55669406841351205548694033 41752055131013404161520525)
            ·
              refine ⟨15657020674130026560570197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 41752055131013404161520525 15657020674130026560570197)
              ·
                refine ⟨91740355512480624378341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 15657020674130026560570197 91740355512480624378341)
                ·
                  rfl

theorem cell22_2411960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 3, 9].length) (baseStart_2411960 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2411960 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2411960 prefixEnd_2411960 := by exact prefixLift 2411960
  have htrace : WordTrace (prefixWord ++ tailWord_2411960) baseStart_2411960 baseEnd_2411960 := by
    simpa [prefixWord, tailWord_2411960, baseEnd_2411960] using wordTrace_append hprefix tailTrace_2411960
  have hstable : (prefixWord ++ tailWord_2411960).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2411960).length < 2 ^ (prefixWord ++ tailWord_2411960).sum := by decide
  have hdescent : baseEnd_2411960 < baseStart_2411960 := by decide
  rcases family_descends (prefixWord ++ tailWord_2411960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2412007 : List Nat := [1, 1, 5, 2, 1, 2, 1, 1, 2, 6]
def baseStart_2412007 : Nat := 118140960795 + 2412007 * 2 ^ 59
def prefixEnd_2412007 : Nat := 4983230072969 + 3 ^ 40 * 2412007 * 2
def baseEnd_2412007 : Nat := 825679288672833163479925

theorem tailTrace_2412007 : CollatzResearch.WordTrace tailWord_2412007 prefixEnd_2412007 825679288672833163479925 := by
  unfold tailWord_2412007
  simp only [CollatzResearch.WordTrace]
  refine ⟨87973122572718051844650275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58648748381812034563100183 87973122572718051844650275)
  ·
    refine ⟨131959683859077077766975413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87973122572718051844650275 131959683859077077766975413)
    ·
      refine ⟨12371220361788476040653945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 131959683859077077766975413 12371220361788476040653945)
      ·
        refine ⟨9278415271341357030490459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12371220361788476040653945 9278415271341357030490459)
        ·
          refine ⟨13917622907012035545735689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9278415271341357030490459 13917622907012035545735689)
          ·
            refine ⟨10438217180259026659301767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13917622907012035545735689 10438217180259026659301767)
            ·
              refine ⟨15657325770388539988952651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10438217180259026659301767 15657325770388539988952651)
              ·
                refine ⟨23485988655582809983428977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15657325770388539988952651 23485988655582809983428977)
                ·
                  refine ⟨17614491491687107487571733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23485988655582809983428977 17614491491687107487571733)
                  ·
                    refine ⟨825679288672833163479925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17614491491687107487571733 825679288672833163479925)
                    ·
                      rfl

theorem cell22_2412007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 1, 1, 2, 6].length) (baseStart_2412007 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2412007 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2412007 prefixEnd_2412007 := by exact prefixLift 2412007
  have htrace : WordTrace (prefixWord ++ tailWord_2412007) baseStart_2412007 baseEnd_2412007 := by
    simpa [prefixWord, tailWord_2412007, baseEnd_2412007] using wordTrace_append hprefix tailTrace_2412007
  have hstable : (prefixWord ++ tailWord_2412007).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2412007).length < 2 ^ (prefixWord ++ tailWord_2412007).sum := by decide
  have hdescent : baseEnd_2412007 < baseStart_2412007 := by decide
  rcases family_descends (prefixWord ++ tailWord_2412007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2412030 : List Nat := [4, 2, 2, 3, 2, 1, 1, 1, 2, 4]
def baseStart_2412030 : Nat := 118140960795 + 2412030 * 2 ^ 59
def prefixEnd_2412030 : Nat := 4983230072969 + 3 ^ 40 * 2412030 * 2
def baseEnd_2412030 : Nat := 825687162042868770154855

theorem tailTrace_2412030 : CollatzResearch.WordTrace tailWord_2412030 prefixEnd_2412030 825687162042868770154855 := by
  unfold tailWord_2412030
  simp only [CollatzResearch.WordTrace]
  refine ⟨10996745181454340846592193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 58649307634423151181825029 10996745181454340846592193)
  ·
    refine ⟨8247558886090755634944145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10996745181454340846592193 8247558886090755634944145)
    ·
      refine ⟨6185669164568066726208109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8247558886090755634944145 6185669164568066726208109)
      ·
        refine ⟨2319625936713025022328041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6185669164568066726208109 2319625936713025022328041)
        ·
          refine ⟨1739719452534768766746031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2319625936713025022328041 1739719452534768766746031)
          ·
            refine ⟨2609579178802153150119047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1739719452534768766746031 2609579178802153150119047)
            ·
              refine ⟨3914368768203229725178571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2609579178802153150119047 3914368768203229725178571)
              ·
                refine ⟨5871553152304844587767857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3914368768203229725178571 5871553152304844587767857)
                ·
                  refine ⟨4403664864228633440825893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5871553152304844587767857 4403664864228633440825893)
                  ·
                    refine ⟨825687162042868770154855, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4403664864228633440825893 825687162042868770154855)
                    ·
                      rfl

theorem cell22_2412030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 2, 1, 1, 1, 2, 4].length) (baseStart_2412030 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2412030 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2412030 prefixEnd_2412030 := by exact prefixLift 2412030
  have htrace : WordTrace (prefixWord ++ tailWord_2412030) baseStart_2412030 baseEnd_2412030 := by
    simpa [prefixWord, tailWord_2412030, baseEnd_2412030] using wordTrace_append hprefix tailTrace_2412030
  have hstable : (prefixWord ++ tailWord_2412030).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2412030).length < 2 ^ (prefixWord ++ tailWord_2412030).sum := by decide
  have hdescent : baseEnd_2412030 < baseStart_2412030 := by decide
  rcases family_descends (prefixWord ++ tailWord_2412030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2412043 : List Nat := [1, 1, 1, 1, 8, 1, 2, 3, 1, 3]
def baseStart_2412043 : Nat := 118140960795 + 2412043 * 2 ^ 59
def prefixEnd_2412043 : Nat := 4983230072969 + 3 ^ 40 * 2412043 * 2
def baseEnd_2412043 : Nat := 825691612208541069579815

theorem tailTrace_2412043 : CollatzResearch.WordTrace tailWord_2412043 prefixEnd_2412043 825691612208541069579815 := by
  unfold tailWord_2412043
  simp only [CollatzResearch.WordTrace]
  refine ⟨87974435600587629992960783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58649623733725086661973855 87974435600587629992960783)
  ·
    refine ⟨131961653400881444989441175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87974435600587629992960783 131961653400881444989441175)
    ·
      refine ⟨197942480101322167484161763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131961653400881444989441175 197942480101322167484161763)
      ·
        refine ⟨296913720151983251226242645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 197942480101322167484161763 296913720151983251226242645)
        ·
          refine ⟨3479457658031053725307531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 296913720151983251226242645 3479457658031053725307531)
          ·
            refine ⟨5219186487046580587961297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3479457658031053725307531 5219186487046580587961297)
            ·
              refine ⟨3914389865284935440970973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5219186487046580587961297 3914389865284935440970973)
              ·
                refine ⟨1467896199481850790364115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3914389865284935440970973 1467896199481850790364115)
                ·
                  refine ⟨2201844299222776185546173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1467896199481850790364115 2201844299222776185546173)
                  ·
                    refine ⟨825691612208541069579815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2201844299222776185546173 825691612208541069579815)
                    ·
                      rfl

theorem cell22_2412043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 1, 2, 3, 1, 3].length) (baseStart_2412043 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2412043 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2412043 prefixEnd_2412043 := by exact prefixLift 2412043
  have htrace : WordTrace (prefixWord ++ tailWord_2412043) baseStart_2412043 baseEnd_2412043 := by
    simpa [prefixWord, tailWord_2412043, baseEnd_2412043] using wordTrace_append hprefix tailTrace_2412043
  have hstable : (prefixWord ++ tailWord_2412043).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2412043).length < 2 ^ (prefixWord ++ tailWord_2412043).sum := by decide
  have hdescent : baseEnd_2412043 < baseStart_2412043 := by decide
  rcases family_descends (prefixWord ++ tailWord_2412043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2412056 : List Nat := [2, 1, 2, 3, 4, 2, 1, 2, 5]
def baseStart_2412056 : Nat := 118140960795 + 2412056 * 2 ^ 59
def prefixEnd_2412056 : Nat := 4983230072969 + 3 ^ 40 * 2412056 * 2
def baseEnd_2412056 : Nat := 275232020791404456334925

theorem tailTrace_2412056 : CollatzResearch.WordTrace tailWord_2412056 prefixEnd_2412056 275232020791404456334925 := by
  unfold tailWord_2412056
  simp only [CollatzResearch.WordTrace]
  refine ⟨43987454874770266606592011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58649939833027022142122681 43987454874770266606592011)
  ·
    refine ⟨65981182312155399909888017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43987454874770266606592011 65981182312155399909888017)
    ·
      refine ⟨49485886734116549932416013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65981182312155399909888017 49485886734116549932416013)
      ·
        refine ⟨18557207525293706224656005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 49485886734116549932416013 18557207525293706224656005)
        ·
          refine ⟨3479476410992569917123001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18557207525293706224656005 3479476410992569917123001)
          ·
            refine ⟨2609607308244427437842251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3479476410992569917123001 2609607308244427437842251)
            ·
              refine ⟨3914410962366641156763377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2609607308244427437842251 3914410962366641156763377)
              ·
                refine ⟨2935808221774980867572533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3914410962366641156763377 2935808221774980867572533)
                ·
                  refine ⟨275232020791404456334925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2935808221774980867572533 275232020791404456334925)
                  ·
                    rfl

theorem cell22_2412056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 2, 1, 2, 5].length) (baseStart_2412056 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2412056 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2412056 prefixEnd_2412056 := by exact prefixLift 2412056
  have htrace : WordTrace (prefixWord ++ tailWord_2412056) baseStart_2412056 baseEnd_2412056 := by
    simpa [prefixWord, tailWord_2412056, baseEnd_2412056] using wordTrace_append hprefix tailTrace_2412056
  have hstable : (prefixWord ++ tailWord_2412056).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2412056).length < 2 ^ (prefixWord ++ tailWord_2412056).sum := by decide
  have hdescent : baseEnd_2412056 < baseStart_2412056 := by decide
  rcases family_descends (prefixWord ++ tailWord_2412056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2412114 : List Nat := [3, 2, 2, 1, 2, 2, 1, 1, 4, 4]
def baseStart_2412114 : Nat := 118140960795 + 2412114 * 2 ^ 59
def prefixEnd_2412114 : Nat := 4983230072969 + 3 ^ 40 * 2412114 * 2
def baseEnd_2412114 : Nat := 825715916959520551054597

theorem tailTrace_2412114 : CollatzResearch.WordTrace tailWord_2412114 prefixEnd_2412114 825715916959520551054597 := by
  unfold tailWord_2412114
  simp only [CollatzResearch.WordTrace]
  refine ⟨21994256295832602279698849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58651350122220272745863597 21994256295832602279698849)
  ·
    refine ⟨16495692221874451709774137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21994256295832602279698849 16495692221874451709774137)
    ·
      refine ⟨12371769166405838782330603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16495692221874451709774137 12371769166405838782330603)
      ·
        refine ⟨18557653749608758173495905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12371769166405838782330603 18557653749608758173495905)
        ·
          refine ⟨13918240312206568630121929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18557653749608758173495905 13918240312206568630121929)
          ·
            refine ⟨10438680234154926472591447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13918240312206568630121929 10438680234154926472591447)
            ·
              refine ⟨15658020351232389708887171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10438680234154926472591447 15658020351232389708887171)
              ·
                refine ⟨23487030526848584563330757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15658020351232389708887171 23487030526848584563330757)
                ·
                  refine ⟨4403818223784109605624517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23487030526848584563330757 4403818223784109605624517)
                  ·
                    refine ⟨825715916959520551054597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4403818223784109605624517 825715916959520551054597)
                    ·
                      rfl

theorem cell22_2412114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 1, 1, 4, 4].length) (baseStart_2412114 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2412114 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2412114 prefixEnd_2412114 := by exact prefixLift 2412114
  have htrace : WordTrace (prefixWord ++ tailWord_2412114) baseStart_2412114 baseEnd_2412114 := by
    simpa [prefixWord, tailWord_2412114, baseEnd_2412114] using wordTrace_append hprefix tailTrace_2412114
  have hstable : (prefixWord ++ tailWord_2412114).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2412114).length < 2 ^ (prefixWord ++ tailWord_2412114).sum := by decide
  have hdescent : baseEnd_2412114 < baseStart_2412114 := by decide
  rcases family_descends (prefixWord ++ tailWord_2412114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2412116 : List Nat := [2, 4, 1, 1, 1, 2, 2, 4, 2, 3]
def baseStart_2412116 : Nat := 118140960795 + 2412116 * 2 ^ 59
def prefixEnd_2412116 : Nat := 4983230072969 + 3 ^ 40 * 2412116 * 2
def baseEnd_2412116 : Nat := 825716601600393212504591

theorem tailTrace_2412116 : CollatzResearch.WordTrace tailWord_2412116 prefixEnd_2412116 825716601600393212504591 := by
  unfold tailWord_2412116
  simp only [CollatzResearch.WordTrace]
  refine ⟨43988549064661581730184101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58651398752882108973578801 43988549064661581730184101)
  ·
    refine ⟨8247852949624046574409519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 43988549064661581730184101 8247852949624046574409519)
    ·
      refine ⟨12371779424436069861614279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8247852949624046574409519 12371779424436069861614279)
      ·
        refine ⟨18557669136654104792421419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12371779424436069861614279 18557669136654104792421419)
        ·
          refine ⟨27836503704981157188632129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18557669136654104792421419 27836503704981157188632129)
          ·
            refine ⟨20877377778735867891474097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27836503704981157188632129 20877377778735867891474097)
            ·
              refine ⟨15658033334051900918605573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20877377778735867891474097 15658033334051900918605573)
              ·
                refine ⟨2935881250134731422238545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15658033334051900918605573 2935881250134731422238545)
                ·
                  refine ⟨2201910937601048566678909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2935881250134731422238545 2201910937601048566678909)
                  ·
                    refine ⟨825716601600393212504591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2201910937601048566678909 825716601600393212504591)
                    ·
                      rfl

theorem cell22_2412116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 2, 4, 2, 3].length) (baseStart_2412116 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2412116 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2412116 prefixEnd_2412116 := by exact prefixLift 2412116
  have htrace : WordTrace (prefixWord ++ tailWord_2412116) baseStart_2412116 baseEnd_2412116 := by
    simpa [prefixWord, tailWord_2412116, baseEnd_2412116] using wordTrace_append hprefix tailTrace_2412116
  have hstable : (prefixWord ++ tailWord_2412116).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2412116).length < 2 ^ (prefixWord ++ tailWord_2412116).sum := by decide
  have hdescent : baseEnd_2412116 < baseStart_2412116 := by decide
  rcases family_descends (prefixWord ++ tailWord_2412116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2412133 : List Nat := [1, 3, 1, 3, 3, 1, 4, 1, 2, 3]
def baseStart_2412133 : Nat := 118140960795 + 2412133 * 2 ^ 59
def prefixEnd_2412133 : Nat := 4983230072969 + 3 ^ 40 * 2412133 * 2
def baseEnd_2412133 : Nat := 825722421047810834829539

theorem tailTrace_2412133 : CollatzResearch.WordTrace tailWord_2412133 prefixEnd_2412133 825722421047810834829539 := by
  unfold tailWord_2412133
  simp only [CollatzResearch.WordTrace]
  refine ⟨87977718170261575363737053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58651812113507716909158035 87977718170261575363737053)
  ·
    refine ⟨32991644313848090761401395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 87977718170261575363737053 32991644313848090761401395)
    ·
      refine ⟨49487466470772136142102093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32991644313848090761401395 49487466470772136142102093)
      ·
        refine ⟨18557799926539551053288285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 49487466470772136142102093 18557799926539551053288285)
        ·
          refine ⟨6959174972452331644983107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18557799926539551053288285 6959174972452331644983107)
          ·
            refine ⟨10438762458678497467474661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6959174972452331644983107 10438762458678497467474661)
            ·
              refine ⟨1957267961002218275151499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10438762458678497467474661 1957267961002218275151499)
              ·
                refine ⟨2935901941503327412727249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1957267961002218275151499 2935901941503327412727249)
                ·
                  refine ⟨2201926456127495559545437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2935901941503327412727249 2201926456127495559545437)
                  ·
                    refine ⟨825722421047810834829539, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2201926456127495559545437 825722421047810834829539)
                    ·
                      rfl

theorem cell22_2412133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 4, 1, 2, 3].length) (baseStart_2412133 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2412133 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2412133 prefixEnd_2412133 := by exact prefixLift 2412133
  have htrace : WordTrace (prefixWord ++ tailWord_2412133) baseStart_2412133 baseEnd_2412133 := by
    simpa [prefixWord, tailWord_2412133, baseEnd_2412133] using wordTrace_append hprefix tailTrace_2412133
  have hstable : (prefixWord ++ tailWord_2412133).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2412133).length < 2 ^ (prefixWord ++ tailWord_2412133).sum := by decide
  have hdescent : baseEnd_2412133 < baseStart_2412133 := by decide
  rcases family_descends (prefixWord ++ tailWord_2412133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2412221 : List Nat := [1, 4, 1, 2, 1, 2, 3, 3, 1, 4]
def baseStart_2412221 : Nat := 118140960795 + 2412221 * 2 ^ 59
def prefixEnd_2412221 : Nat := 4983230072969 + 3 ^ 40 * 2412221 * 2
def baseEnd_2412221 : Nat := 825752545246207938629269

theorem tailTrace_2412221 : CollatzResearch.WordTrace tailWord_2412221 prefixEnd_2412221 825752545246207938629269 := by
  unfold tailWord_2412221
  simp only [CollatzResearch.WordTrace]
  refine ⟨87980927793942766392940517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58653951862628510928627011 87980927793942766392940517)
  ·
    refine ⟨16496423961364268698676347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 87980927793942766392940517 16496423961364268698676347)
    ·
      refine ⟨24744635942046403048014521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16496423961364268698676347 24744635942046403048014521)
      ·
        refine ⟨18558476956534802286010891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24744635942046403048014521 18558476956534802286010891)
        ·
          refine ⟨27837715434802203429016337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18558476956534802286010891 27837715434802203429016337)
          ·
            refine ⟨20878286576101652571762253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27837715434802203429016337 20878286576101652571762253)
            ·
              refine ⟨7829357466038119714410845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20878286576101652571762253 7829357466038119714410845)
              ·
                refine ⟨2936009049764294892904067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7829357466038119714410845 2936009049764294892904067)
                ·
                  refine ⟨4404013574646442339356101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2936009049764294892904067 4404013574646442339356101)
                  ·
                    refine ⟨825752545246207938629269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4404013574646442339356101 825752545246207938629269)
                    ·
                      rfl

theorem cell22_2412221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 3, 3, 1, 4].length) (baseStart_2412221 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2412221 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2412221 prefixEnd_2412221 := by exact prefixLift 2412221
  have htrace : WordTrace (prefixWord ++ tailWord_2412221) baseStart_2412221 baseEnd_2412221 := by
    simpa [prefixWord, tailWord_2412221, baseEnd_2412221] using wordTrace_append hprefix tailTrace_2412221
  have hstable : (prefixWord ++ tailWord_2412221).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2412221).length < 2 ^ (prefixWord ++ tailWord_2412221).sum := by decide
  have hdescent : baseEnd_2412221 < baseStart_2412221 := by decide
  rcases family_descends (prefixWord ++ tailWord_2412221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2412249 : List Nat := [1, 2, 1, 2, 3, 3, 1, 2, 1, 6]
def baseStart_2412249 : Nat := 118140960795 + 2412249 * 2 ^ 59
def prefixEnd_2412249 : Nat := 4983230072969 + 3 ^ 40 * 2412249 * 2
def baseEnd_2412249 : Nat := 825762130218425198929183

theorem tailTrace_2412249 : CollatzResearch.WordTrace tailWord_2412249 prefixEnd_2412249 825762130218425198929183 := by
  unfold tailWord_2412249
  simp only [CollatzResearch.WordTrace]
  refine ⟨87981949037841327174959801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58654632691894218116639867 87981949037841327174959801)
  ·
    refine ⟨65986461778380995381219851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87981949037841327174959801 65986461778380995381219851)
    ·
      refine ⟨98979692667571493071829777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65986461778380995381219851 98979692667571493071829777)
      ·
        refine ⟨74234769500678619803872333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 98979692667571493071829777 74234769500678619803872333)
        ·
          refine ⟨27838038562754482426452125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 74234769500678619803872333 27838038562754482426452125)
          ·
            refine ⟨10439264461032930909919547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27838038562754482426452125 10439264461032930909919547)
            ·
              refine ⟨15658896691549396364879321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10439264461032930909919547 15658896691549396364879321)
              ·
                refine ⟨11744172518662047273659491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15658896691549396364879321 11744172518662047273659491)
                ·
                  refine ⟨17616258777993070910489237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11744172518662047273659491 17616258777993070910489237)
                  ·
                    refine ⟨825762130218425198929183, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17616258777993070910489237 825762130218425198929183)
                    ·
                      rfl

theorem cell22_2412249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 1, 2, 1, 6].length) (baseStart_2412249 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2412249 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2412249 prefixEnd_2412249 := by exact prefixLift 2412249
  have htrace : WordTrace (prefixWord ++ tailWord_2412249) baseStart_2412249 baseEnd_2412249 := by
    simpa [prefixWord, tailWord_2412249, baseEnd_2412249] using wordTrace_append hprefix tailTrace_2412249
  have hstable : (prefixWord ++ tailWord_2412249).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2412249).length < 2 ^ (prefixWord ++ tailWord_2412249).sum := by decide
  have hdescent : baseEnd_2412249 < baseStart_2412249 := by decide
  rcases family_descends (prefixWord ++ tailWord_2412249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2412401 : List Nat := [1, 2, 2, 2, 1, 3, 2, 1, 4, 4]
def baseStart_2412401 : Nat := 118140960795 + 2412401 * 2 ^ 59
def prefixEnd_2412401 : Nat := 4983230072969 + 3 ^ 40 * 2412401 * 2
def baseEnd_2412401 : Nat := 825814162924747469128717

theorem tailTrace_2412401 : CollatzResearch.WordTrace tailWord_2412401 prefixEnd_2412401 825814162924747469128717 := by
  unfold tailWord_2412401
  simp only [CollatzResearch.WordTrace]
  refine ⟨87987492933290657134493057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58658328622193771422995371 87987492933290657134493057)
  ·
    refine ⟨65990619699967992850869793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87987492933290657134493057 65990619699967992850869793)
    ·
      refine ⟨49492964774975994638152345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65990619699967992850869793 49492964774975994638152345)
      ·
        refine ⟨37119723581231995978614259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49492964774975994638152345 37119723581231995978614259)
        ·
          refine ⟨55679585371847993967921389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37119723581231995978614259 55679585371847993967921389)
          ·
            refine ⟨20879844514442997737970521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 55679585371847993967921389 20879844514442997737970521)
            ·
              refine ⟨15659883385832248303477891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20879844514442997737970521 15659883385832248303477891)
              ·
                refine ⟨23489825078748372455216837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15659883385832248303477891 23489825078748372455216837)
                ·
                  refine ⟨4404342202265319835353157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23489825078748372455216837 4404342202265319835353157)
                  ·
                    refine ⟨825814162924747469128717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4404342202265319835353157 825814162924747469128717)
                    ·
                      rfl

theorem cell22_2412401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 2, 1, 4, 4].length) (baseStart_2412401 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2412401 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2412401 prefixEnd_2412401 := by exact prefixLift 2412401
  have htrace : WordTrace (prefixWord ++ tailWord_2412401) baseStart_2412401 baseEnd_2412401 := by
    simpa [prefixWord, tailWord_2412401, baseEnd_2412401] using wordTrace_append hprefix tailTrace_2412401
  have hstable : (prefixWord ++ tailWord_2412401).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2412401).length < 2 ^ (prefixWord ++ tailWord_2412401).sum := by decide
  have hdescent : baseEnd_2412401 < baseStart_2412401 := by decide
  rcases family_descends (prefixWord ++ tailWord_2412401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2412450 : List Nat := [3, 3, 1, 2, 4, 1, 8]
def baseStart_2412450 : Nat := 118140960795 + 2412450 * 2 ^ 59
def prefixEnd_2412450 : Nat := 4983230072969 + 3 ^ 40 * 2412450 * 2
def baseEnd_2412450 : Nat := 30586330986152876839021

theorem tailTrace_2412450 : CollatzResearch.WordTrace tailWord_2412450 prefixEnd_2412450 30586330986152876839021 := by
  unfold tailWord_2412450
  simp only [CollatzResearch.WordTrace]
  refine ⟨21997320027528284625756701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58659520073408759002017869 21997320027528284625756701)
  ·
    refine ⟨8248995010323106734658763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21997320027528284625756701 8248995010323106734658763)
    ·
      refine ⟨12373492515484660101988145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8248995010323106734658763 12373492515484660101988145)
      ·
        refine ⟨9280119386613495076491109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12373492515484660101988145 9280119386613495076491109)
        ·
          refine ⟨1740022384990030326842083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9280119386613495076491109 1740022384990030326842083)
          ·
            refine ⟨2610033577485045490263125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1740022384990030326842083 2610033577485045490263125)
            ·
              refine ⟨30586330986152876839021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2610033577485045490263125 30586330986152876839021)
              ·
                rfl

theorem cell22_2412450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 4, 1, 8].length) (baseStart_2412450 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2412450 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2412450 prefixEnd_2412450 := by exact prefixLift 2412450
  have htrace : WordTrace (prefixWord ++ tailWord_2412450) baseStart_2412450 baseEnd_2412450 := by
    simpa [prefixWord, tailWord_2412450, baseEnd_2412450] using wordTrace_append hprefix tailTrace_2412450
  have hstable : (prefixWord ++ tailWord_2412450).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2412450).length < 2 ^ (prefixWord ++ tailWord_2412450).sum := by decide
  have hdescent : baseEnd_2412450 < baseStart_2412450 := by decide
  rcases family_descends (prefixWord ++ tailWord_2412450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2412465 : List Nat := [1, 2, 2, 4, 2, 1, 3, 1, 3, 3]
def baseStart_2412465 : Nat := 118140960795 + 2412465 * 2 ^ 59
def prefixEnd_2412465 : Nat := 4983230072969 + 3 ^ 40 * 2412465 * 2
def baseEnd_2412465 : Nat := 825836071432672635528521

theorem tailTrace_2412465 : CollatzResearch.WordTrace tailWord_2412465 prefixEnd_2412465 825836071432672635528521 := by
  unfold tailWord_2412465
  simp only [CollatzResearch.WordTrace]
  refine ⟨87989827205058796064822849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58659884803372530709881899 87989827205058796064822849)
  ·
    refine ⟨65992370403794097048617137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87989827205058796064822849 65992370403794097048617137)
    ·
      refine ⟨49494277802845572786462853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65992370403794097048617137 49494277802845572786462853)
      ·
        refine ⟨9280177088033544897461785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 49494277802845572786462853 9280177088033544897461785)
        ·
          refine ⟨6960132816025158673096339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9280177088033544897461785 6960132816025158673096339)
          ·
            refine ⟨10440199224037738009644509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6960132816025158673096339 10440199224037738009644509)
            ·
              refine ⟨3915074709014151753616691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10440199224037738009644509 3915074709014151753616691)
              ·
                refine ⟨5872612063521227630425037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3915074709014151753616691 5872612063521227630425037)
                ·
                  refine ⟨2202229523820460361409389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5872612063521227630425037 2202229523820460361409389)
                  ·
                    refine ⟨825836071432672635528521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2202229523820460361409389 825836071432672635528521)
                    ·
                      rfl

theorem cell22_2412465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 3, 1, 3, 3].length) (baseStart_2412465 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2412465 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2412465 prefixEnd_2412465 := by exact prefixLift 2412465
  have htrace : WordTrace (prefixWord ++ tailWord_2412465) baseStart_2412465 baseEnd_2412465 := by
    simpa [prefixWord, tailWord_2412465, baseEnd_2412465] using wordTrace_append hprefix tailTrace_2412465
  have hstable : (prefixWord ++ tailWord_2412465).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2412465).length < 2 ^ (prefixWord ++ tailWord_2412465).sum := by decide
  have hdescent : baseEnd_2412465 < baseStart_2412465 := by decide
  rcases family_descends (prefixWord ++ tailWord_2412465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2412538 : List Nat := [3, 1, 1, 1, 1, 2, 1, 1, 8, 3]
def baseStart_2412538 : Nat := 118140960795 + 2412538 * 2 ^ 59
def prefixEnd_2412538 : Nat := 4983230072969 + 3 ^ 40 * 2412538 * 2
def baseEnd_2412538 : Nat := 825861060824524778453297

theorem tailTrace_2412538 : CollatzResearch.WordTrace tailWord_2412538 prefixEnd_2412538 825861060824524778453297 := by
  unfold tailWord_2412538
  simp only [CollatzResearch.WordTrace]
  refine ⟨21998122433448582383057567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58661659822529553021486845 21998122433448582383057567)
  ·
    refine ⟨32997183650172873574586351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21998122433448582383057567 32997183650172873574586351)
    ·
      refine ⟨49495775475259310361879527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32997183650172873574586351 49495775475259310361879527)
      ·
        refine ⟨74243663212888965542819291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49495775475259310361879527 74243663212888965542819291)
        ·
          refine ⟨111365494819333448314228937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74243663212888965542819291 111365494819333448314228937)
          ·
            refine ⟨83524121114500086235671703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 111365494819333448314228937 83524121114500086235671703)
            ·
              refine ⟨125286181671750129353507555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 83524121114500086235671703 125286181671750129353507555)
              ·
                refine ⟨187929272507625194030261333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 125286181671750129353507555 187929272507625194030261333)
                ·
                  refine ⟨2202296162198732742542125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 187929272507625194030261333 2202296162198732742542125)
                  ·
                    refine ⟨825861060824524778453297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2202296162198732742542125 825861060824524778453297)
                    ·
                      rfl

theorem cell22_2412538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 1, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 1, 8, 3].length) (baseStart_2412538 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2412538 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2412538 prefixEnd_2412538 := by exact prefixLift 2412538
  have htrace : WordTrace (prefixWord ++ tailWord_2412538) baseStart_2412538 baseEnd_2412538 := by
    simpa [prefixWord, tailWord_2412538, baseEnd_2412538] using wordTrace_append hprefix tailTrace_2412538
  have hstable : (prefixWord ++ tailWord_2412538).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2412538).length < 2 ^ (prefixWord ++ tailWord_2412538).sum := by decide
  have hdescent : baseEnd_2412538 < baseStart_2412538 := by decide
  rcases family_descends (prefixWord ++ tailWord_2412538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2412550 : List Nat := [6, 2, 1, 2, 1, 1, 2, 3, 1, 3]
def baseStart_2412550 : Nat := 118140960795 + 2412550 * 2 ^ 59
def prefixEnd_2412550 : Nat := 4983230072969 + 3 ^ 40 * 2412550 * 2
def baseEnd_2412550 : Nat := 825865168669760747153261

theorem tailTrace_2412550 : CollatzResearch.WordTrace tailWord_2412550 prefixEnd_2412550 825865168669760747153261 := by
  unfold tailWord_2412550
  simp only [CollatzResearch.WordTrace]
  refine ⟨2749778981554714236927097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 58661951606500570387778069 2749778981554714236927097)
  ·
    refine ⟨2062334236166035677695323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2749778981554714236927097 2062334236166035677695323)
    ·
      refine ⟨3093501354249053516542985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2062334236166035677695323 3093501354249053516542985)
      ·
        refine ⟨2320126015686790137407239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3093501354249053516542985 2320126015686790137407239)
        ·
          refine ⟨3480189023530185206110859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2320126015686790137407239 3480189023530185206110859)
          ·
            refine ⟨5220283535295277809166289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3480189023530185206110859 5220283535295277809166289)
            ·
              refine ⟨3915212651471458356874717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5220283535295277809166289 3915212651471458356874717)
              ·
                refine ⟨1468204744301796883828019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3915212651471458356874717 1468204744301796883828019)
                ·
                  refine ⟨2202307116452695325742029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1468204744301796883828019 2202307116452695325742029)
                  ·
                    refine ⟨825865168669760747153261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2202307116452695325742029 825865168669760747153261)
                    ·
                      rfl

theorem cell22_2412550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 1, 2, 3, 1, 3].length) (baseStart_2412550 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2412550 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2412550 prefixEnd_2412550 := by exact prefixLift 2412550
  have htrace : WordTrace (prefixWord ++ tailWord_2412550) baseStart_2412550 baseEnd_2412550 := by
    simpa [prefixWord, tailWord_2412550, baseEnd_2412550] using wordTrace_append hprefix tailTrace_2412550
  have hstable : (prefixWord ++ tailWord_2412550).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2412550).length < 2 ^ (prefixWord ++ tailWord_2412550).sum := by decide
  have hdescent : baseEnd_2412550 < baseStart_2412550 := by decide
  rcases family_descends (prefixWord ++ tailWord_2412550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2412572 : List Nat := [2, 2, 3, 1, 3, 1, 3, 2, 2, 3]
def baseStart_2412572 : Nat := 118140960795 + 2412572 * 2 ^ 59
def prefixEnd_2412572 : Nat := 4983230072969 + 3 ^ 40 * 2412572 * 2
def baseEnd_2412572 : Nat := 825872699719360023103193

theorem tailTrace_2412572 : CollatzResearch.WordTrace tailWord_2412572 prefixEnd_2412572 825872699719360023103193 := by
  unfold tailWord_2412572
  simp only [CollatzResearch.WordTrace]
  refine ⟨43996864907835576669483985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58662486543780768892645313 43996864907835576669483985)
  ·
    refine ⟨32997648680876682502112989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43996864907835576669483985 32997648680876682502112989)
    ·
      refine ⟨12374118255328755938292371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32997648680876682502112989 12374118255328755938292371)
      ·
        refine ⟨18561177382993133907438557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12374118255328755938292371 18561177382993133907438557)
        ·
          refine ⟨6960441518622425215289459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18561177382993133907438557 6960441518622425215289459)
          ·
            refine ⟨10440662277933637822934189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6960441518622425215289459 10440662277933637822934189)
            ·
              refine ⟨3915248354225114183600321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10440662277933637822934189 3915248354225114183600321)
              ·
                refine ⟨2936436265668835637700241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3915248354225114183600321 2936436265668835637700241)
                ·
                  refine ⟨2202327199251626728275181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2936436265668835637700241 2202327199251626728275181)
                  ·
                    refine ⟨825872699719360023103193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2202327199251626728275181 825872699719360023103193)
                    ·
                      rfl

theorem cell22_2412572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 3, 2, 2, 3].length) (baseStart_2412572 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2412572 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2412572 prefixEnd_2412572 := by exact prefixLift 2412572
  have htrace : WordTrace (prefixWord ++ tailWord_2412572) baseStart_2412572 baseEnd_2412572 := by
    simpa [prefixWord, tailWord_2412572, baseEnd_2412572] using wordTrace_append hprefix tailTrace_2412572
  have hstable : (prefixWord ++ tailWord_2412572).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2412572).length < 2 ^ (prefixWord ++ tailWord_2412572).sum := by decide
  have hdescent : baseEnd_2412572 < baseStart_2412572 := by decide
  rcases family_descends (prefixWord ++ tailWord_2412572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2412634 : List Nat := [3, 1, 1, 2, 1, 1, 7, 2, 1, 3]
def baseStart_2412634 : Nat := 118140960795 + 2412634 * 2 ^ 59
def prefixEnd_2412634 : Nat := 4983230072969 + 3 ^ 40 * 2412634 * 2
def baseEnd_2412634 : Nat := 825893923586412528053003

theorem tailTrace_2412634 : CollatzResearch.WordTrace tailWord_2412634 prefixEnd_2412634 825893923586412528053003 := by
  unfold tailWord_2412634
  simp only [CollatzResearch.WordTrace]
  refine ⟨21998997785361634481931239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58663994094297691951816637 21998997785361634481931239)
  ·
    refine ⟨32998496678042451722896859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21998997785361634481931239 32998496678042451722896859)
    ·
      refine ⟨49497745017063677584345289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32998496678042451722896859 49497745017063677584345289)
      ·
        refine ⟨37123308762797758188258967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49497745017063677584345289 37123308762797758188258967)
        ·
          refine ⟨55684963144196637282388451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37123308762797758188258967 55684963144196637282388451)
          ·
            refine ⟨83527444716294955923582677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55684963144196637282388451 83527444716294955923582677)
            ·
              refine ⟨1957674485538163029458969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 83527444716294955923582677 1957674485538163029458969)
              ·
                refine ⟨1468255864153622272094227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1957674485538163029458969 1468255864153622272094227)
                ·
                  refine ⟨2202383796230433408141341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1468255864153622272094227 2202383796230433408141341)
                  ·
                    refine ⟨825893923586412528053003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2202383796230433408141341 825893923586412528053003)
                    ·
                      rfl

theorem cell22_2412634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 7, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 7, 2, 1, 3].length) (baseStart_2412634 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2412634 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2412634 prefixEnd_2412634 := by exact prefixLift 2412634
  have htrace : WordTrace (prefixWord ++ tailWord_2412634) baseStart_2412634 baseEnd_2412634 := by
    simpa [prefixWord, tailWord_2412634, baseEnd_2412634] using wordTrace_append hprefix tailTrace_2412634
  have hstable : (prefixWord ++ tailWord_2412634).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2412634).length < 2 ^ (prefixWord ++ tailWord_2412634).sum := by decide
  have hdescent : baseEnd_2412634 < baseStart_2412634 := by decide
  rcases family_descends (prefixWord ++ tailWord_2412634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2412690 : List Nat := [3, 2, 3, 1, 1, 1, 1, 2, 3, 5]
def baseStart_2412690 : Nat := 118140960795 + 2412690 * 2 ^ 59
def prefixEnd_2412690 : Nat := 4983230072969 + 3 ^ 40 * 2412690 * 2
def baseEnd_2412690 : Nat := 825913093530847048652831

theorem tailTrace_2412690 : CollatzResearch.WordTrace tailWord_2412690 prefixEnd_2412690 825913093530847048652831 := by
  unfold tailWord_2412690
  simp only [CollatzResearch.WordTrace]
  refine ⟨21999508407310914872940881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58665355752829106327842349 21999508407310914872940881)
  ·
    refine ⟨16499631305483186154705661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21999508407310914872940881 16499631305483186154705661)
    ·
      refine ⟨6187361739556194808014623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16499631305483186154705661 6187361739556194808014623)
      ·
        refine ⟨9281042609334292212021935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6187361739556194808014623 9281042609334292212021935)
        ·
          refine ⟨13921563914001438318032903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9281042609334292212021935 13921563914001438318032903)
          ·
            refine ⟨20882345871002157477049355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13921563914001438318032903 20882345871002157477049355)
            ·
              refine ⟨31323518806503236215574033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20882345871002157477049355 31323518806503236215574033)
              ·
                refine ⟨23492639104877427161680525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31323518806503236215574033 23492639104877427161680525)
                ·
                  refine ⟨8809739664329035185630197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23492639104877427161680525 8809739664329035185630197)
                  ·
                    refine ⟨825913093530847048652831, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8809739664329035185630197 825913093530847048652831)
                    ·
                      rfl

theorem cell22_2412690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 1, 2, 3, 5].length) (baseStart_2412690 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2412690 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2412690 prefixEnd_2412690 := by exact prefixLift 2412690
  have htrace : WordTrace (prefixWord ++ tailWord_2412690) baseStart_2412690 baseEnd_2412690 := by
    simpa [prefixWord, tailWord_2412690, baseEnd_2412690] using wordTrace_append hprefix tailTrace_2412690
  have hstable : (prefixWord ++ tailWord_2412690).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2412690).length < 2 ^ (prefixWord ++ tailWord_2412690).sum := by decide
  have hdescent : baseEnd_2412690 < baseStart_2412690 := by decide
  rcases family_descends (prefixWord ++ tailWord_2412690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2412735 : List Nat := [1, 1, 2, 2, 2, 2, 1, 1, 7, 3]
def baseStart_2412735 : Nat := 118140960795 + 2412735 * 2 ^ 59
def prefixEnd_2412735 : Nat := 4983230072969 + 3 ^ 40 * 2412735 * 2
def baseEnd_2412735 : Nat := 825928497950481931277693

theorem tailTrace_2412735 : CollatzResearch.WordTrace tailWord_2412735 prefixEnd_2412735 825928497950481931277693 := by
  unfold tailWord_2412735
  simp only [CollatzResearch.WordTrace]
  refine ⟨87999674914080632177151659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58666449942720421451434439 87999674914080632177151659)
  ·
    refine ⟨131999512371120948265727489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87999674914080632177151659 131999512371120948265727489)
    ·
      refine ⟨98999634278340711199295617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 131999512371120948265727489 98999634278340711199295617)
      ·
        refine ⟨74249725708755533399471713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 98999634278340711199295617 74249725708755533399471713)
        ·
          refine ⟨55687294281566650049603785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 74249725708755533399471713 55687294281566650049603785)
          ·
            refine ⟨41765470711174987537202839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55687294281566650049603785 41765470711174987537202839)
            ·
              refine ⟨62648206066762481305804259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41765470711174987537202839 62648206066762481305804259)
              ·
                refine ⟨93972309100143721958706389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 62648206066762481305804259 93972309100143721958706389)
                ·
                  refine ⟨2202475994534618483407181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 93972309100143721958706389 2202475994534618483407181)
                  ·
                    refine ⟨825928497950481931277693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2202475994534618483407181 825928497950481931277693)
                    ·
                      rfl

theorem cell22_2412735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 1, 7, 3].length) (baseStart_2412735 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2412735 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2412735 prefixEnd_2412735 := by exact prefixLift 2412735
  have htrace : WordTrace (prefixWord ++ tailWord_2412735) baseStart_2412735 baseEnd_2412735 := by
    simpa [prefixWord, tailWord_2412735, baseEnd_2412735] using wordTrace_append hprefix tailTrace_2412735
  have hstable : (prefixWord ++ tailWord_2412735).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2412735).length < 2 ^ (prefixWord ++ tailWord_2412735).sum := by decide
  have hdescent : baseEnd_2412735 < baseStart_2412735 := by decide
  rcases family_descends (prefixWord ++ tailWord_2412735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2412737 : List Nat := [1, 2, 6, 1, 2, 1, 9]
def baseStart_2412737 : Nat := 118140960795 + 2412737 * 2 ^ 59
def prefixEnd_2412737 : Nat := 4983230072969 + 3 ^ 40 * 2412737 * 2
def baseEnd_2412737 : Nat := 30589969725605725656581

theorem tailTrace_2412737 : CollatzResearch.WordTrace tailWord_2412737 prefixEnd_2412737 30589969725605725656581 := by
  unfold tailWord_2412737
  simp only [CollatzResearch.WordTrace]
  refine ⟨87999747860073386518724465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58666498573382257679149643 87999747860073386518724465)
  ·
    refine ⟨65999810895055039889043349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87999747860073386518724465 65999810895055039889043349)
    ·
      refine ⟨3093741135705704994798907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 65999810895055039889043349 3093741135705704994798907)
      ·
        refine ⟨4640611703558557492198361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3093741135705704994798907 4640611703558557492198361)
        ·
          refine ⟨3480458777668918119148771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4640611703558557492198361 3480458777668918119148771)
          ·
            refine ⟨5220688166503377178723157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3480458777668918119148771 5220688166503377178723157)
            ·
              refine ⟨30589969725605725656581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 5220688166503377178723157 30589969725605725656581)
              ·
                rfl

theorem cell22_2412737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 1, 9].length) (baseStart_2412737 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2412737 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2412737 prefixEnd_2412737 := by exact prefixLift 2412737
  have htrace : WordTrace (prefixWord ++ tailWord_2412737) baseStart_2412737 baseEnd_2412737 := by
    simpa [prefixWord, tailWord_2412737, baseEnd_2412737] using wordTrace_append hprefix tailTrace_2412737
  have hstable : (prefixWord ++ tailWord_2412737).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2412737).length < 2 ^ (prefixWord ++ tailWord_2412737).sum := by decide
  have hdescent : baseEnd_2412737 < baseStart_2412737 := by decide
  rcases family_descends (prefixWord ++ tailWord_2412737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2412758 : List Nat := [5, 2, 1, 2, 1, 2, 3, 1, 2, 3]
def baseStart_2412758 : Nat := 118140960795 + 2412758 * 2 ^ 59
def prefixEnd_2412758 : Nat := 4983230072969 + 3 ^ 40 * 2412758 * 2
def baseEnd_2412758 : Nat := 825936371320517537952623

theorem tailTrace_2412758 : CollatzResearch.WordTrace tailWord_2412758 prefixEnd_2412758 825936371320517537952623 := by
  unfold tailWord_2412758
  simp only [CollatzResearch.WordTrace]
  refine ⟨5500032112062331694077433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 58667009195331538070159285 5500032112062331694077433)
  ·
    refine ⟨4125024084046748770558075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5500032112062331694077433 4125024084046748770558075)
    ·
      refine ⟨6187536126070123155837113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4125024084046748770558075 6187536126070123155837113)
      ·
        refine ⟨4640652094552592366877835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6187536126070123155837113 4640652094552592366877835)
        ·
          refine ⟨6960978141828888550316753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4640652094552592366877835 6960978141828888550316753)
          ·
            refine ⟨5220733606371666412737565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6960978141828888550316753 5220733606371666412737565)
            ·
              refine ⟨1957775102389374904776587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5220733606371666412737565 1957775102389374904776587)
              ·
                refine ⟨2936662653584062357164881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1957775102389374904776587 2936662653584062357164881)
                ·
                  refine ⟨2202496990188046767873661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2936662653584062357164881 2202496990188046767873661)
                  ·
                    refine ⟨825936371320517537952623, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2202496990188046767873661 825936371320517537952623)
                    ·
                      rfl

theorem cell22_2412758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 2, 3, 1, 2, 3].length) (baseStart_2412758 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2412758 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2412758 prefixEnd_2412758 := by exact prefixLift 2412758
  have htrace : WordTrace (prefixWord ++ tailWord_2412758) baseStart_2412758 baseEnd_2412758 := by
    simpa [prefixWord, tailWord_2412758, baseEnd_2412758] using wordTrace_append hprefix tailTrace_2412758
  have hstable : (prefixWord ++ tailWord_2412758).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2412758).length < 2 ^ (prefixWord ++ tailWord_2412758).sum := by decide
  have hdescent : baseEnd_2412758 < baseStart_2412758 := by decide
  rcases family_descends (prefixWord ++ tailWord_2412758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2412771 : List Nat := [1, 1, 1, 8, 2, 1, 2, 6]
def baseStart_2412771 : Nat := 118140960795 + 2412771 * 2 ^ 59
def prefixEnd_2412771 : Nat := 4983230072969 + 3 ^ 40 * 2412771 * 2
def baseEnd_2412771 : Nat := 91771202387354426375287

theorem tailTrace_2412771 : CollatzResearch.WordTrace tailWord_2412771 prefixEnd_2412771 91771202387354426375287 := by
  unfold tailWord_2412771
  simp only [CollatzResearch.WordTrace]
  refine ⟨88000987941950210325462167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58667325294633473550308111 88000987941950210325462167)
  ·
    refine ⟨132001481912925315488193251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88000987941950210325462167 132001481912925315488193251)
    ·
      refine ⟨198002222869387973232289877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132001481912925315488193251 198002222869387973232289877)
      ·
        refine ⟨2320338549250640311315897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 198002222869387973232289877 2320338549250640311315897)
        ·
          refine ⟨1740253911937980233486923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2320338549250640311315897 1740253911937980233486923)
          ·
            refine ⟨2610380867906970350230385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1740253911937980233486923 2610380867906970350230385)
            ·
              refine ⟨1957785650930227762672789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2610380867906970350230385 1957785650930227762672789)
              ·
                refine ⟨91771202387354426375287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1957785650930227762672789 91771202387354426375287)
                ·
                  rfl

theorem cell22_2412771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 2, 1, 2, 6].length) (baseStart_2412771 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2412771 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2412771 prefixEnd_2412771 := by exact prefixLift 2412771
  have htrace : WordTrace (prefixWord ++ tailWord_2412771) baseStart_2412771 baseEnd_2412771 := by
    simpa [prefixWord, tailWord_2412771, baseEnd_2412771] using wordTrace_append hprefix tailTrace_2412771
  have hstable : (prefixWord ++ tailWord_2412771).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2412771).length < 2 ^ (prefixWord ++ tailWord_2412771).sum := by decide
  have hdescent : baseEnd_2412771 < baseStart_2412771 := by decide
  rcases family_descends (prefixWord ++ tailWord_2412771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2412786 : List Nat := [3, 2, 1, 3, 2, 1, 3, 3, 1, 3]
def baseStart_2412786 : Nat := 118140960795 + 2412786 * 2 ^ 59
def prefixEnd_2412786 : Nat := 4983230072969 + 3 ^ 40 * 2412786 * 2
def baseEnd_2412786 : Nat := 825945956292734798252537

theorem tailTrace_2412786 : CollatzResearch.WordTrace tailWord_2412786 prefixEnd_2412786 825945956292734798252537 := by
  unfold tailWord_2412786
  simp only [CollatzResearch.WordTrace]
  refine ⟨22000383759223966971814553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58667690024597245258172141 22000383759223966971814553)
  ·
    refine ⟨16500287819417975228860915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22000383759223966971814553 16500287819417975228860915)
    ·
      refine ⟨24750431729126962843291373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16500287819417975228860915 24750431729126962843291373)
      ·
        refine ⟨9281411898422611066234265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24750431729126962843291373 9281411898422611066234265)
        ·
          refine ⟨6961058923816958299675699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9281411898422611066234265 6961058923816958299675699)
          ·
            refine ⟨10441588385725437449513549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6961058923816958299675699 10441588385725437449513549)
            ·
              refine ⟨3915595644647039043567581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10441588385725437449513549 3915595644647039043567581)
              ·
                refine ⟨1468348366742639641337843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3915595644647039043567581 1468348366742639641337843)
                ·
                  refine ⟨2202522550113959462006765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1468348366742639641337843 2202522550113959462006765)
                  ·
                    refine ⟨825945956292734798252537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2202522550113959462006765 825945956292734798252537)
                    ·
                      rfl

theorem cell22_2412786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 3, 3, 1, 3].length) (baseStart_2412786 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2412786 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2412786 prefixEnd_2412786 := by exact prefixLift 2412786
  have htrace : WordTrace (prefixWord ++ tailWord_2412786) baseStart_2412786 baseEnd_2412786 := by
    simpa [prefixWord, tailWord_2412786, baseEnd_2412786] using wordTrace_append hprefix tailTrace_2412786
  have hstable : (prefixWord ++ tailWord_2412786).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2412786).length < 2 ^ (prefixWord ++ tailWord_2412786).sum := by decide
  have hdescent : baseEnd_2412786 < baseStart_2412786 := by decide
  rcases family_descends (prefixWord ++ tailWord_2412786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2412829 : List Nat := [1, 4, 2, 3, 2, 1, 1, 1, 3, 4]
def baseStart_2412829 : Nat := 118140960795 + 2412829 * 2 ^ 59
def prefixEnd_2412829 : Nat := 4983230072969 + 3 ^ 40 * 2412829 * 2
def baseEnd_2412829 : Nat := 825960676071497019427405

theorem tailTrace_2412829 : CollatzResearch.WordTrace tailWord_2412829 prefixEnd_2412829 825960676071497019427405 := by
  unfold tailWord_2412829
  simp only [CollatzResearch.WordTrace]
  refine ⟨88003103375740086231073541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58668735583826724154049027 88003103375740086231073541)
  ·
    refine ⟨16500581882951266168326289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 88003103375740086231073541 16500581882951266168326289)
    ·
      refine ⟨12375436412213449626244717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16500581882951266168326289 12375436412213449626244717)
      ·
        refine ⟨4640788654580043609841769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12375436412213449626244717 4640788654580043609841769)
        ·
          refine ⟨3480591490935032707381327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4640788654580043609841769 3480591490935032707381327)
          ·
            refine ⟨5220887236402549061071991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3480591490935032707381327 5220887236402549061071991)
            ·
              refine ⟨7831330854603823591607987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5220887236402549061071991 7831330854603823591607987)
              ·
                refine ⟨11746996281905735387411981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7831330854603823591607987 11746996281905735387411981)
                ·
                  refine ⟨4405123605714650770279493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11746996281905735387411981 4405123605714650770279493)
                  ·
                    refine ⟨825960676071497019427405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4405123605714650770279493 825960676071497019427405)
                    ·
                      rfl

theorem cell22_2412829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 1, 1, 1, 3, 4].length) (baseStart_2412829 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2412829 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2412829 prefixEnd_2412829 := by exact prefixLift 2412829
  have htrace : WordTrace (prefixWord ++ tailWord_2412829) baseStart_2412829 baseEnd_2412829 := by
    simpa [prefixWord, tailWord_2412829, baseEnd_2412829] using wordTrace_append hprefix tailTrace_2412829
  have hstable : (prefixWord ++ tailWord_2412829).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2412829).length < 2 ^ (prefixWord ++ tailWord_2412829).sum := by decide
  have hdescent : baseEnd_2412829 < baseStart_2412829 := by decide
  rcases family_descends (prefixWord ++ tailWord_2412829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2412915 : List Nat := [1, 1, 1, 2, 2, 1, 2, 2, 3, 7]
def baseStart_2412915 : Nat := 118140960795 + 2412915 * 2 ^ 59
def prefixEnd_2412915 : Nat := 4983230072969 + 3 ^ 40 * 2412915 * 2
def baseEnd_2412915 : Nat := 825990115629021461777141

theorem tailTrace_2412915 : CollatzResearch.WordTrace tailWord_2412915 prefixEnd_2412915 825990115629021461777141 := by
  unfold tailWord_2412915
  simp only [CollatzResearch.WordTrace]
  refine ⟨88006240053428522918704199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58670826702285681945802799 88006240053428522918704199)
  ·
    refine ⟨132009360080142784378056299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88006240053428522918704199 132009360080142784378056299)
    ·
      refine ⟨198014040120214176567084449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132009360080142784378056299 198014040120214176567084449)
      ·
        refine ⟨148510530090160632425313337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 198014040120214176567084449 148510530090160632425313337)
        ·
          refine ⟨111382897567620474318985003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 148510530090160632425313337 111382897567620474318985003)
          ·
            refine ⟨167074346351430711478477505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 111382897567620474318985003 167074346351430711478477505)
            ·
              refine ⟨125305759763573033608858129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 167074346351430711478477505 125305759763573033608858129)
              ·
                refine ⟨93979319822679775206643597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 125305759763573033608858129 93979319822679775206643597)
                ·
                  refine ⟨35242244933504915702491349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 93979319822679775206643597 35242244933504915702491349)
                  ·
                    refine ⟨825990115629021461777141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 35242244933504915702491349 825990115629021461777141)
                    ·
                      rfl

theorem cell22_2412915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 2, 3, 7].length) (baseStart_2412915 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2412915 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2412915 prefixEnd_2412915 := by exact prefixLift 2412915
  have htrace : WordTrace (prefixWord ++ tailWord_2412915) baseStart_2412915 baseEnd_2412915 := by
    simpa [prefixWord, tailWord_2412915, baseEnd_2412915] using wordTrace_append hprefix tailTrace_2412915
  have hstable : (prefixWord ++ tailWord_2412915).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2412915).length < 2 ^ (prefixWord ++ tailWord_2412915).sum := by decide
  have hdescent : baseEnd_2412915 < baseStart_2412915 := by decide
  rcases family_descends (prefixWord ++ tailWord_2412915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2412932 : List Nat := [2, 3, 2, 1, 1, 2, 1, 3, 2, 5]
def baseStart_2412932 : Nat := 118140960795 + 2412932 * 2 ^ 59
def prefixEnd_2412932 : Nat := 4983230072969 + 3 ^ 40 * 2412932 * 2
def baseEnd_2412932 : Nat := 825995935076439084102089

theorem tailTrace_2412932 : CollatzResearch.WordTrace tailWord_2412932 prefixEnd_2412932 825995935076439084102089 := by
  unfold tailWord_2412932
  simp only [CollatzResearch.WordTrace]
  refine ⟨44003430047183467411036525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58671240062911289881382033 44003430047183467411036525)
  ·
    refine ⟨16501286267693800279138697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44003430047183467411036525 16501286267693800279138697)
    ·
      refine ⟨12375964700770350209354023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16501286267693800279138697 12375964700770350209354023)
      ·
        refine ⟨18563947051155525314031035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12375964700770350209354023 18563947051155525314031035)
        ·
          refine ⟨27845920576733287971046553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18563947051155525314031035 27845920576733287971046553)
          ·
            refine ⟨20884440432549965978284915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27845920576733287971046553 20884440432549965978284915)
            ·
              refine ⟨31326660648824948967427373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20884440432549965978284915 31326660648824948967427373)
              ·
                refine ⟨11747497743309355862785265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31326660648824948967427373 11747497743309355862785265)
                ·
                  refine ⟨8810623307482016897088949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11747497743309355862785265 8810623307482016897088949)
                  ·
                    refine ⟨825995935076439084102089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8810623307482016897088949 825995935076439084102089)
                    ·
                      rfl

theorem cell22_2412932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 1, 3, 2, 5].length) (baseStart_2412932 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2412932 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2412932 prefixEnd_2412932 := by exact prefixLift 2412932
  have htrace : WordTrace (prefixWord ++ tailWord_2412932) baseStart_2412932 baseEnd_2412932 := by
    simpa [prefixWord, tailWord_2412932, baseEnd_2412932] using wordTrace_append hprefix tailTrace_2412932
  have hstable : (prefixWord ++ tailWord_2412932).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2412932).length < 2 ^ (prefixWord ++ tailWord_2412932).sum := by decide
  have hdescent : baseEnd_2412932 < baseStart_2412932 := by decide
  rcases family_descends (prefixWord ++ tailWord_2412932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2412964 : List Nat := [2, 3, 1, 2, 1, 1, 4, 3, 1, 4]
def baseStart_2412964 : Nat := 118140960795 + 2412964 * 2 ^ 59
def prefixEnd_2412964 : Nat := 4983230072969 + 3 ^ 40 * 2412964 * 2
def baseEnd_2412964 : Nat := 826006889330401667301991

theorem tailTrace_2412964 : CollatzResearch.WordTrace tailWord_2412964 prefixEnd_2412964 826006889330401667301991 := by
  unfold tailWord_2412964
  simp only [CollatzResearch.WordTrace]
  refine ⟨44004013615125502143618973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58672018153500669524825297 44004013615125502143618973)
  ·
    refine ⟨16501505105672063303857115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44004013615125502143618973 16501505105672063303857115)
    ·
      refine ⟨24752257658508094955785673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16501505105672063303857115 24752257658508094955785673)
      ·
        refine ⟨18564193243881071216839255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24752257658508094955785673 18564193243881071216839255)
        ·
          refine ⟨27846289865821606825258883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18564193243881071216839255 27846289865821606825258883)
          ·
            refine ⟨41769434798732410237888325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27846289865821606825258883 41769434798732410237888325)
            ·
              refine ⟨7831769024762326919604061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 41769434798732410237888325 7831769024762326919604061)
              ·
                refine ⟨2936913384285872594851523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7831769024762326919604061 2936913384285872594851523)
                ·
                  refine ⟨4405370076428808892277285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2936913384285872594851523 4405370076428808892277285)
                  ·
                    refine ⟨826006889330401667301991, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4405370076428808892277285 826006889330401667301991)
                    ·
                      rfl

theorem cell22_2412964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 4, 3, 1, 4].length) (baseStart_2412964 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2412964 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2412964 prefixEnd_2412964 := by exact prefixLift 2412964
  have htrace : WordTrace (prefixWord ++ tailWord_2412964) baseStart_2412964 baseEnd_2412964 := by
    simpa [prefixWord, tailWord_2412964, baseEnd_2412964] using wordTrace_append hprefix tailTrace_2412964
  have hstable : (prefixWord ++ tailWord_2412964).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2412964).length < 2 ^ (prefixWord ++ tailWord_2412964).sum := by decide
  have hdescent : baseEnd_2412964 < baseStart_2412964 := by decide
  rcases family_descends (prefixWord ++ tailWord_2412964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2412992 : List Nat := [2, 1, 1, 2, 3, 1, 1, 1, 6, 4]
def baseStart_2412992 : Nat := 118140960795 + 2412992 * 2 ^ 59
def prefixEnd_2412992 : Nat := 4983230072969 + 3 ^ 40 * 2412992 * 2
def baseEnd_2412992 : Nat := 826016474302618927601905

theorem tailTrace_2412992 : CollatzResearch.WordTrace tailWord_2412992 prefixEnd_2412992 826016474302618927601905 := by
  unfold tailWord_2412992
  simp only [CollatzResearch.WordTrace]
  refine ⟨44004524237074782534628615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58672698982766376712838153 44004524237074782534628615)
  ·
    refine ⟨66006786355612173801942923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44004524237074782534628615 66006786355612173801942923)
    ·
      refine ⟨99010179533418260702914385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66006786355612173801942923 99010179533418260702914385)
      ·
        refine ⟨74257634650063695527185789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 99010179533418260702914385 74257634650063695527185789)
        ·
          refine ⟨27846612993773885822694671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 74257634650063695527185789 27846612993773885822694671)
          ·
            refine ⟨41769919490660828734042007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27846612993773885822694671 41769919490660828734042007)
            ·
              refine ⟨62654879235991243101063011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41769919490660828734042007 62654879235991243101063011)
              ·
                refine ⟨93982318853986864651594517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 62654879235991243101063011 93982318853986864651594517)
                ·
                  refine ⟨4405421196280634280543493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 93982318853986864651594517 4405421196280634280543493)
                  ·
                    refine ⟨826016474302618927601905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4405421196280634280543493 826016474302618927601905)
                    ·
                      rfl

theorem cell22_2412992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 1, 6, 4].length) (baseStart_2412992 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2412992 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2412992 prefixEnd_2412992 := by exact prefixLift 2412992
  have htrace : WordTrace (prefixWord ++ tailWord_2412992) baseStart_2412992 baseEnd_2412992 := by
    simpa [prefixWord, tailWord_2412992, baseEnd_2412992] using wordTrace_append hprefix tailTrace_2412992
  have hstable : (prefixWord ++ tailWord_2412992).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2412992).length < 2 ^ (prefixWord ++ tailWord_2412992).sum := by decide
  have hdescent : baseEnd_2412992 < baseStart_2412992 := by decide
  rcases family_descends (prefixWord ++ tailWord_2412992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2413039 : List Nat := [1, 1, 2, 1, 4, 1, 1, 5, 3, 3]
def baseStart_2413039 : Nat := 118140960795 + 2413039 * 2 ^ 59
def prefixEnd_2413039 : Nat := 4983230072969 + 3 ^ 40 * 2413039 * 2
def baseEnd_2413039 : Nat := 826032563363126471676761

theorem tailTrace_2413039 : CollatzResearch.WordTrace tailWord_2413039 prefixEnd_2413039 826032563363126471676761 := by
  unfold tailWord_2413039
  simp only [CollatzResearch.WordTrace]
  refine ⟨88010762704979292096218171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58673841803319528064145447 88010762704979292096218171)
  ·
    refine ⟨132016144057468938144327257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88010762704979292096218171 132016144057468938144327257)
    ·
      refine ⟨99012108043101703608245443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 132016144057468938144327257 99012108043101703608245443)
      ·
        refine ⟨148518162064652555412368165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99012108043101703608245443 148518162064652555412368165)
        ·
          refine ⟨27847155387122354139819031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 148518162064652555412368165 27847155387122354139819031)
          ·
            refine ⟨41770733080683531209728547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27847155387122354139819031 41770733080683531209728547)
            ·
              refine ⟨62656099621025296814592821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41770733080683531209728547 62656099621025296814592821)
              ·
                refine ⟨5874009339471121576368077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 62656099621025296814592821 5874009339471121576368077)
                ·
                  refine ⟨2202753502301670591138029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5874009339471121576368077 2202753502301670591138029)
                  ·
                    refine ⟨826032563363126471676761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2202753502301670591138029 826032563363126471676761)
                    ·
                      rfl

theorem cell22_2413039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 5, 3, 3].length) (baseStart_2413039 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2413039 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2413039 prefixEnd_2413039 := by exact prefixLift 2413039
  have htrace : WordTrace (prefixWord ++ tailWord_2413039) baseStart_2413039 baseEnd_2413039 := by
    simpa [prefixWord, tailWord_2413039, baseEnd_2413039] using wordTrace_append hprefix tailTrace_2413039
  have hstable : (prefixWord ++ tailWord_2413039).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2413039).length < 2 ^ (prefixWord ++ tailWord_2413039).sum := by decide
  have hdescent : baseEnd_2413039 < baseStart_2413039 := by decide
  rcases family_descends (prefixWord ++ tailWord_2413039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2413052 : List Nat := [2, 2, 2, 1, 2, 1, 1, 2, 9]
def baseStart_2413052 : Nat := 118140960795 + 2413052 * 2 ^ 59
def prefixEnd_2413052 : Nat := 4983230072969 + 3 ^ 40 * 2413052 * 2
def baseEnd_2413052 : Nat := 275345671176266257033907

theorem tailTrace_2413052 : CollatzResearch.WordTrace tailWord_2413052 prefixEnd_2413052 275345671176266257033907 := by
  unfold tailWord_2413052
  simp only [CollatzResearch.WordTrace]
  refine ⟨44005618426966097658220705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58674157902621463544294273 44005618426966097658220705)
  ·
    refine ⟨33004213820224573243665529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44005618426966097658220705 33004213820224573243665529)
    ·
      refine ⟨24753160365168429932749147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33004213820224573243665529 24753160365168429932749147)
      ·
        refine ⟨37129740547752644899123721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24753160365168429932749147 37129740547752644899123721)
        ·
          refine ⟨27847305410814483674342791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37129740547752644899123721 27847305410814483674342791)
          ·
            refine ⟨41770958116221725511514187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27847305410814483674342791 41770958116221725511514187)
            ·
              refine ⟨62656437174332588267271281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41770958116221725511514187 62656437174332588267271281)
              ·
                refine ⟨46992327880749441200453461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 62656437174332588267271281 46992327880749441200453461)
                ·
                  refine ⟨275345671176266257033907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 46992327880749441200453461 275345671176266257033907)
                  ·
                    rfl

theorem cell22_2413052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 2, 9].length) (baseStart_2413052 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2413052 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2413052 prefixEnd_2413052 := by exact prefixLift 2413052
  have htrace : WordTrace (prefixWord ++ tailWord_2413052) baseStart_2413052 baseEnd_2413052 := by
    simpa [prefixWord, tailWord_2413052, baseEnd_2413052] using wordTrace_append hprefix tailTrace_2413052
  have hstable : (prefixWord ++ tailWord_2413052).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2413052).length < 2 ^ (prefixWord ++ tailWord_2413052).sum := by decide
  have hdescent : baseEnd_2413052 < baseStart_2413052 := by decide
  rcases family_descends (prefixWord ++ tailWord_2413052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2413058 : List Nat := [3, 4, 1, 2, 2, 1, 3, 6]
def baseStart_2413058 : Nat := 118140960795 + 2413058 * 2 ^ 59
def prefixEnd_2413058 : Nat := 4983230072969 + 3 ^ 40 * 2413058 * 2
def baseEnd_2413058 : Nat := 91782118605712972827967

theorem tailTrace_2413058 : CollatzResearch.WordTrace tailWord_2413058 prefixEnd_2413058 91782118605712972827967 := by
  unfold tailWord_2413058
  simp only [CollatzResearch.WordTrace]
  refine ⟨22002863922977614585289957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58674303794606972227439885 22002863922977614585289957)
  ·
    refine ⟨4125536985558302734741867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 22002863922977614585289957 4125536985558302734741867)
    ·
      refine ⟨6188305478337454102112801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4125536985558302734741867 6188305478337454102112801)
      ·
        refine ⟨4641229108753090576584601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6188305478337454102112801 4641229108753090576584601)
        ·
          refine ⟨3480921831564817932438451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4641229108753090576584601 3480921831564817932438451)
          ·
            refine ⟨5221382747347226898657677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3480921831564817932438451 5221382747347226898657677)
            ·
              refine ⟨1958018530255210086996629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5221382747347226898657677 1958018530255210086996629)
              ·
                refine ⟨91782118605712972827967, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1958018530255210086996629 91782118605712972827967)
                ·
                  rfl

theorem cell22_2413058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 1, 3, 6].length) (baseStart_2413058 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2413058 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2413058 prefixEnd_2413058 := by exact prefixLift 2413058
  have htrace : WordTrace (prefixWord ++ tailWord_2413058) baseStart_2413058 baseEnd_2413058 := by
    simpa [prefixWord, tailWord_2413058, baseEnd_2413058] using wordTrace_append hprefix tailTrace_2413058
  have hstable : (prefixWord ++ tailWord_2413058).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2413058).length < 2 ^ (prefixWord ++ tailWord_2413058).sum := by decide
  have hdescent : baseEnd_2413058 < baseStart_2413058 := by decide
  rcases family_descends (prefixWord ++ tailWord_2413058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2413084 : List Nat := [2, 2, 3, 1, 2, 2, 1, 2, 2, 5]
def baseStart_2413084 : Nat := 118140960795 + 2413084 * 2 ^ 59
def prefixEnd_2413084 : Nat := 4983230072969 + 3 ^ 40 * 2413084 * 2
def baseEnd_2413084 : Nat := 826047967782761354301623

theorem tailTrace_2413084 : CollatzResearch.WordTrace tailWord_2413084 prefixEnd_2413084 826047967782761354301623 := by
  unfold tailWord_2413084
  simp only [CollatzResearch.WordTrace]
  refine ⟨44006201994908132390803153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58674935993210843187737537 44006201994908132390803153)
  ·
    refine ⟨33004651496181099293102365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44006201994908132390803153 33004651496181099293102365)
    ·
      refine ⟨12376744311067912234913387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33004651496181099293102365 12376744311067912234913387)
      ·
        refine ⟨18565116466601868352370081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12376744311067912234913387 18565116466601868352370081)
        ·
          refine ⟨13923837349951401264277561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18565116466601868352370081 13923837349951401264277561)
          ·
            refine ⟨10442878012463550948208171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13923837349951401264277561 10442878012463550948208171)
            ·
              refine ⟨15664317018695326422312257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10442878012463550948208171 15664317018695326422312257)
              ·
                refine ⟨11748237764021494816734193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15664317018695326422312257 11748237764021494816734193)
                ·
                  refine ⟨8811178323016121112550645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11748237764021494816734193 8811178323016121112550645)
                  ·
                    refine ⟨826047967782761354301623, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8811178323016121112550645 826047967782761354301623)
                    ·
                      rfl

theorem cell22_2413084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 1, 2, 2, 5].length) (baseStart_2413084 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2413084 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2413084 prefixEnd_2413084 := by exact prefixLift 2413084
  have htrace : WordTrace (prefixWord ++ tailWord_2413084) baseStart_2413084 baseEnd_2413084 := by
    simpa [prefixWord, tailWord_2413084, baseEnd_2413084] using wordTrace_append hprefix tailTrace_2413084
  have hstable : (prefixWord ++ tailWord_2413084).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2413084).length < 2 ^ (prefixWord ++ tailWord_2413084).sum := by decide
  have hdescent : baseEnd_2413084 < baseStart_2413084 := by decide
  rcases family_descends (prefixWord ++ tailWord_2413084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2413114 : List Nat := [3, 1, 1, 1, 3, 3, 2, 2, 6]
def baseStart_2413114 : Nat := 118140960795 + 2413114 * 2 ^ 59
def prefixEnd_2413114 : Nat := 4983230072969 + 3 ^ 40 * 2413114 * 2
def baseEnd_2413114 : Nat := 275352745798617092017177

theorem tailTrace_2413114 : CollatzResearch.WordTrace tailWord_2413114 prefixEnd_2413114 275352745798617092017177 := by
  unfold tailWord_2413114
  simp only [CollatzResearch.WordTrace]
  refine ⟨22003374544926894976299599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58675665453138386603465597 22003374544926894976299599)
  ·
    refine ⟨33005061817390342464449399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22003374544926894976299599 33005061817390342464449399)
    ·
      refine ⟨49507592726085513696674099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33005061817390342464449399 49507592726085513696674099)
      ·
        refine ⟨74261389089128270545011149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49507592726085513696674099 74261389089128270545011149)
        ·
          refine ⟨27848020908423101454379181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 74261389089128270545011149 27848020908423101454379181)
          ·
            refine ⟨10443007840658663045392193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27848020908423101454379181 10443007840658663045392193)
            ·
              refine ⟨7832255880493997284044145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10443007840658663045392193 7832255880493997284044145)
              ·
                refine ⟨5874191910370497963033109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7832255880493997284044145 5874191910370497963033109)
                ·
                  refine ⟨275352745798617092017177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5874191910370497963033109 275352745798617092017177)
                  ·
                    rfl

theorem cell22_2413114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 2, 2, 6].length) (baseStart_2413114 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2413114 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2413114 prefixEnd_2413114 := by exact prefixLift 2413114
  have htrace : WordTrace (prefixWord ++ tailWord_2413114) baseStart_2413114 baseEnd_2413114 := by
    simpa [prefixWord, tailWord_2413114, baseEnd_2413114] using wordTrace_append hprefix tailTrace_2413114
  have hstable : (prefixWord ++ tailWord_2413114).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2413114).length < 2 ^ (prefixWord ++ tailWord_2413114).sum := by decide
  have hdescent : baseEnd_2413114 < baseStart_2413114 := by decide
  rcases family_descends (prefixWord ++ tailWord_2413114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2413116 : List Nat := [2, 2, 2, 2, 3, 1, 1, 4, 1, 4]
def baseStart_2413116 : Nat := 118140960795 + 2413116 * 2 ^ 59
def prefixEnd_2413116 : Nat := 4983230072969 + 3 ^ 40 * 2413116 * 2
def baseEnd_2413116 : Nat := 826058922036723937501525

theorem tailTrace_2413116 : CollatzResearch.WordTrace tailWord_2413116 prefixEnd_2413116 826058922036723937501525 := by
  unfold tailWord_2413116
  simp only [CollatzResearch.WordTrace]
  refine ⟨44006785562850167123385601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58675714083800222831180801 44006785562850167123385601)
  ·
    refine ⟨33005089172137625342539201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44006785562850167123385601 33005089172137625342539201)
    ·
      refine ⟨24753816879103219006904401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33005089172137625342539201 24753816879103219006904401)
      ·
        refine ⟨18565362659327414255178301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24753816879103219006904401 18565362659327414255178301)
        ·
          refine ⟨6962010997247780345691863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18565362659327414255178301 6962010997247780345691863)
          ·
            refine ⟨10443016495871670518537795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6962010997247780345691863 10443016495871670518537795)
            ·
              refine ⟨15664524743807505777806693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10443016495871670518537795 15664524743807505777806693)
              ·
                refine ⟨2937098389463907333338755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15664524743807505777806693 2937098389463907333338755)
                ·
                  refine ⟨4405647584195861000008133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2937098389463907333338755 4405647584195861000008133)
                  ·
                    refine ⟨826058922036723937501525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4405647584195861000008133 826058922036723937501525)
                    ·
                      rfl

theorem cell22_2413116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 1, 4, 1, 4].length) (baseStart_2413116 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2413116 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2413116 prefixEnd_2413116 := by exact prefixLift 2413116
  have htrace : WordTrace (prefixWord ++ tailWord_2413116) baseStart_2413116 baseEnd_2413116 := by
    simpa [prefixWord, tailWord_2413116, baseEnd_2413116] using wordTrace_append hprefix tailTrace_2413116
  have hstable : (prefixWord ++ tailWord_2413116).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2413116).length < 2 ^ (prefixWord ++ tailWord_2413116).sum := by decide
  have hdescent : baseEnd_2413116 < baseStart_2413116 := by decide
  rcases family_descends (prefixWord ++ tailWord_2413116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2413131 : List Nat := [1, 1, 1, 1, 3, 1, 7, 3, 4]
def baseStart_2413131 : Nat := 118140960795 + 2413131 * 2 ^ 59
def prefixEnd_2413131 : Nat := 4983230072969 + 3 ^ 40 * 2413131 * 2
def baseEnd_2413131 : Nat := 275354685614422966125493

theorem tailTrace_2413131 : CollatzResearch.WordTrace tailWord_2413131 prefixEnd_2413131 275354685614422966125493 := by
  unfold tailWord_2413131
  simp only [CollatzResearch.WordTrace]
  refine ⟨88014118220645991808567247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58676078813763994539044831 88014118220645991808567247)
  ·
    refine ⟨132021177330968987712850871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88014118220645991808567247 132021177330968987712850871)
    ·
      refine ⟨198031765996453481569276307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132021177330968987712850871 198031765996453481569276307)
      ·
        refine ⟨297047648994680222353914461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 198031765996453481569276307 297047648994680222353914461)
        ·
          refine ⟨111392868373005083382717923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 297047648994680222353914461 111392868373005083382717923)
          ·
            refine ⟨167089302559507625074076885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 111392868373005083382717923 167089302559507625074076885)
            ·
              refine ⟨3916155528738459962673677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 167089302559507625074076885 3916155528738459962673677)
              ·
                refine ⟨1468558323276922486002629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3916155528738459962673677 1468558323276922486002629)
                ·
                  refine ⟨275354685614422966125493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1468558323276922486002629 275354685614422966125493)
                  ·
                    rfl

theorem cell22_2413131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 7, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 7, 3, 4].length) (baseStart_2413131 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2413131 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2413131 prefixEnd_2413131 := by exact prefixLift 2413131
  have htrace : WordTrace (prefixWord ++ tailWord_2413131) baseStart_2413131 baseEnd_2413131 := by
    simpa [prefixWord, tailWord_2413131, baseEnd_2413131] using wordTrace_append hprefix tailTrace_2413131
  have hstable : (prefixWord ++ tailWord_2413131).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2413131).length < 2 ^ (prefixWord ++ tailWord_2413131).sum := by decide
  have hdescent : baseEnd_2413131 < baseStart_2413131 := by decide
  rcases family_descends (prefixWord ++ tailWord_2413131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2413133 : List Nat := [1, 6, 1, 1, 2, 1, 2, 3, 1, 4]
def baseStart_2413133 : Nat := 118140960795 + 2413133 * 2 ^ 59
def prefixEnd_2413133 : Nat := 4983230072969 + 3 ^ 40 * 2413133 * 2
def baseEnd_2413133 : Nat := 826064741484141559826473

theorem tailTrace_2413133 : CollatzResearch.WordTrace tailWord_2413133 prefixEnd_2413133 826064741484141559826473 := by
  unfold tailWord_2413133
  simp only [CollatzResearch.WordTrace]
  refine ⟨88014191166638746150140053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58676127444425830766760035 88014191166638746150140053)
  ·
    refine ⟨4125665210936191225787815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 88014191166638746150140053 4125665210936191225787815)
    ·
      refine ⟨6188497816404286838681723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4125665210936191225787815 6188497816404286838681723)
      ·
        refine ⟨9282746724606430258022585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6188497816404286838681723 9282746724606430258022585)
        ·
          refine ⟨6962060043454822693516939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9282746724606430258022585 6962060043454822693516939)
          ·
            refine ⟨10443090065182234040275409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6962060043454822693516939 10443090065182234040275409)
            ·
              refine ⟨7832317548886675530206557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10443090065182234040275409 7832317548886675530206557)
              ·
                refine ⟨2937119080832503323827459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7832317548886675530206557 2937119080832503323827459)
                ·
                  refine ⟨4405678621248754985741189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2937119080832503323827459 4405678621248754985741189)
                  ·
                    refine ⟨826064741484141559826473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4405678621248754985741189 826064741484141559826473)
                    ·
                      rfl

theorem cell22_2413133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 2, 3, 1, 4].length) (baseStart_2413133 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2413133 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2413133 prefixEnd_2413133 := by exact prefixLift 2413133
  have htrace : WordTrace (prefixWord ++ tailWord_2413133) baseStart_2413133 baseEnd_2413133 := by
    simpa [prefixWord, tailWord_2413133, baseEnd_2413133] using wordTrace_append hprefix tailTrace_2413133
  have hstable : (prefixWord ++ tailWord_2413133).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2413133).length < 2 ^ (prefixWord ++ tailWord_2413133).sum := by decide
  have hdescent : baseEnd_2413133 < baseStart_2413133 := by decide
  rcases family_descends (prefixWord ++ tailWord_2413133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2413144 : List Nat := [2, 1, 2, 2, 1, 2, 3, 1, 4, 4]
def baseStart_2413144 : Nat := 118140960795 + 2413144 * 2 ^ 59
def prefixEnd_2413144 : Nat := 4983230072969 + 3 ^ 40 * 2413144 * 2
def baseEnd_2413144 : Nat := 826068507008941197801439

theorem tailTrace_2413144 : CollatzResearch.WordTrace tailWord_2413144 prefixEnd_2413144 826068507008941197801439 := by
  unfold tailWord_2413144
  simp only [CollatzResearch.WordTrace]
  refine ⟨44007296184799447514395243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58676394913065930019193657 44007296184799447514395243)
  ·
    refine ⟨66010944277199171271592865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44007296184799447514395243 66010944277199171271592865)
    ·
      refine ⟨49508208207899378453694649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66010944277199171271592865 49508208207899378453694649)
      ·
        refine ⟨37131156155924533840270987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49508208207899378453694649 37131156155924533840270987)
        ·
          refine ⟨55696734233886800760406481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37131156155924533840270987 55696734233886800760406481)
          ·
            refine ⟨41772550675415100570304861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55696734233886800760406481 41772550675415100570304861)
            ·
              refine ⟨15664706503280662713864323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 41772550675415100570304861 15664706503280662713864323)
              ·
                refine ⟨23497059754920994070796485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15664706503280662713864323 23497059754920994070796485)
                ·
                  refine ⟨4405698704047686388274341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23497059754920994070796485 4405698704047686388274341)
                  ·
                    refine ⟨826068507008941197801439, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4405698704047686388274341 826068507008941197801439)
                    ·
                      rfl

theorem cell22_2413144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 3, 1, 4, 4].length) (baseStart_2413144 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2413144 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2413144 prefixEnd_2413144 := by exact prefixLift 2413144
  have htrace : WordTrace (prefixWord ++ tailWord_2413144) baseStart_2413144 baseEnd_2413144 := by
    simpa [prefixWord, tailWord_2413144, baseEnd_2413144] using wordTrace_append hprefix tailTrace_2413144
  have hstable : (prefixWord ++ tailWord_2413144).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2413144).length < 2 ^ (prefixWord ++ tailWord_2413144).sum := by decide
  have hdescent : baseEnd_2413144 < baseStart_2413144 := by decide
  rcases family_descends (prefixWord ++ tailWord_2413144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2413148 : List Nat := [2, 2, 4, 1, 3, 2, 1, 1, 6]
def baseStart_2413148 : Nat := 118140960795 + 2413148 * 2 ^ 59
def prefixEnd_2413148 : Nat := 4983230072969 + 3 ^ 40 * 2413148 * 2
def baseEnd_2413148 : Nat := 275356625430228840233809

theorem tailTrace_2413148 : CollatzResearch.WordTrace tailWord_2413148 prefixEnd_2413148 275356625430228840233809 := by
  unfold tailWord_2413148
  simp only [CollatzResearch.WordTrace]
  refine ⟨44007369130792201855968049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58676492174389602474624065 44007369130792201855968049)
  ·
    refine ⟨33005526848094151391976037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44007369130792201855968049 33005526848094151391976037)
    ·
      refine ⟨6188536284017653385995507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 33005526848094151391976037 6188536284017653385995507)
      ·
        refine ⟨9282804426026480078993261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6188536284017653385995507 9282804426026480078993261)
        ·
          refine ⟨3481051659759930029622473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9282804426026480078993261 3481051659759930029622473)
          ·
            refine ⟨2610788744819947522216855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3481051659759930029622473 2610788744819947522216855)
            ·
              refine ⟨3916183117229921283325283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2610788744819947522216855 3916183117229921283325283)
              ·
                refine ⟨5874274675844881924987925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3916183117229921283325283 5874274675844881924987925)
                ·
                  refine ⟨275356625430228840233809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5874274675844881924987925 275356625430228840233809)
                  ·
                    rfl

theorem cell22_2413148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 2, 1, 1, 6].length) (baseStart_2413148 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2413148 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2413148 prefixEnd_2413148 := by exact prefixLift 2413148
  have htrace : WordTrace (prefixWord ++ tailWord_2413148) baseStart_2413148 baseEnd_2413148 := by
    simpa [prefixWord, tailWord_2413148, baseEnd_2413148] using wordTrace_append hprefix tailTrace_2413148
  have hstable : (prefixWord ++ tailWord_2413148).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2413148).length < 2 ^ (prefixWord ++ tailWord_2413148).sum := by decide
  have hdescent : baseEnd_2413148 < baseStart_2413148 := by decide
  rcases family_descends (prefixWord ++ tailWord_2413148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2413210 : List Nat := [3, 1, 1, 6, 2, 1, 1, 7]
def baseStart_2413210 : Nat := 118140960795 + 2413210 * 2 ^ 59
def prefixEnd_2413210 : Nat := 4983230072969 + 3 ^ 40 * 2413210 * 2
def baseEnd_2413210 : Nat := 91787900017526558405693

theorem tailTrace_2413210 : CollatzResearch.WordTrace tailWord_2413210 prefixEnd_2413210 91787900017526558405693 := by
  unfold tailWord_2413210
  simp only [CollatzResearch.WordTrace]
  refine ⟨22004249896839947075173271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58677999724906525533795389 22004249896839947075173271)
  ·
    refine ⟨33006374845259920612759907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22004249896839947075173271 33006374845259920612759907)
    ·
      refine ⟨49509562267889880919139861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33006374845259920612759907 49509562267889880919139861)
      ·
        refine ⟨2320760731307338168084681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 49509562267889880919139861 2320760731307338168084681)
        ·
          refine ⟨1740570548480503626063511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2320760731307338168084681 1740570548480503626063511)
          ·
            refine ⟨2610855822720755439095267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1740570548480503626063511 2610855822720755439095267)
            ·
              refine ⟨3916283734081133158642901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2610855822720755439095267 3916283734081133158642901)
              ·
                refine ⟨91787900017526558405693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3916283734081133158642901 91787900017526558405693)
                ·
                  rfl

theorem cell22_2413210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 2, 1, 1, 7].length) (baseStart_2413210 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2413210 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2413210 prefixEnd_2413210 := by exact prefixLift 2413210
  have htrace : WordTrace (prefixWord ++ tailWord_2413210) baseStart_2413210 baseEnd_2413210 := by
    simpa [prefixWord, tailWord_2413210, baseEnd_2413210] using wordTrace_append hprefix tailTrace_2413210
  have hstable : (prefixWord ++ tailWord_2413210).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2413210).length < 2 ^ (prefixWord ++ tailWord_2413210).sum := by decide
  have hdescent : baseEnd_2413210 < baseStart_2413210 := by decide
  rcases family_descends (prefixWord ++ tailWord_2413210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2413296 : List Nat := [2, 1, 1, 1, 3, 1, 4, 3, 2, 4]
def baseStart_2413296 : Nat := 118140960795 + 2413296 * 2 ^ 59
def prefixEnd_2413296 : Nat := 4983230072969 + 3 ^ 40 * 2413296 * 2
def baseEnd_2413296 : Nat := 826120539715263468000973

theorem tailTrace_2413296 : CollatzResearch.WordTrace tailWord_2413296 prefixEnd_2413296 826120539715263468000973 := by
  unfold tailWord_2413296
  simp only [CollatzResearch.WordTrace]
  refine ⟨44010068132524112494161871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58680090843365483325549161 44010068132524112494161871)
  ·
    refine ⟨66015102198786168741242807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44010068132524112494161871 66015102198786168741242807)
    ·
      refine ⟨99022653298179253111864211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66015102198786168741242807 99022653298179253111864211)
      ·
        refine ⟨148533979947268879667796317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99022653298179253111864211 148533979947268879667796317)
        ·
          refine ⟨55700242480225829875423619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 148533979947268879667796317 55700242480225829875423619)
          ·
            refine ⟨83550363720338744813135429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55700242480225829875423619 83550363720338744813135429)
            ·
              refine ⟨15665693197563514652462893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 83550363720338744813135429 15665693197563514652462893)
              ·
                refine ⟨5874634949086317994673585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15665693197563514652462893 5874634949086317994673585)
                ·
                  refine ⟨4405976211814738496005189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5874634949086317994673585 4405976211814738496005189)
                  ·
                    refine ⟨826120539715263468000973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4405976211814738496005189 826120539715263468000973)
                    ·
                      rfl

theorem cell22_2413296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 4, 3, 2, 4].length) (baseStart_2413296 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2413296 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2413296 prefixEnd_2413296 := by exact prefixLift 2413296
  have htrace : WordTrace (prefixWord ++ tailWord_2413296) baseStart_2413296 baseEnd_2413296 := by
    simpa [prefixWord, tailWord_2413296, baseEnd_2413296] using wordTrace_append hprefix tailTrace_2413296
  have hstable : (prefixWord ++ tailWord_2413296).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2413296).length < 2 ^ (prefixWord ++ tailWord_2413296).sum := by decide
  have hdescent : baseEnd_2413296 < baseStart_2413296 := by decide
  rcases family_descends (prefixWord ++ tailWord_2413296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2413298 : List Nat := [3, 2, 1, 3, 1, 2, 1, 2, 4, 3]
def baseStart_2413298 : Nat := 118140960795 + 2413298 * 2 ^ 59
def prefixEnd_2413298 : Nat := 4983230072969 + 3 ^ 40 * 2413298 * 2
def baseEnd_2413298 : Nat := 826121224356136129450967

theorem tailTrace_2413298 : CollatzResearch.WordTrace tailWord_2413298 prefixEnd_2413298 826121224356136129450967 := by
  unfold tailWord_2413298
  simp only [CollatzResearch.WordTrace]
  refine ⟨22005052302760244832474137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58680139474027319553264365 22005052302760244832474137)
  ·
    refine ⟨16503789227070183624355603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22005052302760244832474137 16503789227070183624355603)
    ·
      refine ⟨24755683840605275436533405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16503789227070183624355603 24755683840605275436533405)
      ·
        refine ⟨9283381440226978288700027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24755683840605275436533405 9283381440226978288700027)
        ·
          refine ⟨13925072160340467433050041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9283381440226978288700027 13925072160340467433050041)
          ·
            refine ⟨10443804120255350574787531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13925072160340467433050041 10443804120255350574787531)
            ·
              refine ⟨15665706180383025862181297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10443804120255350574787531 15665706180383025862181297)
              ·
                refine ⟨11749279635287269396635973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15665706180383025862181297 11749279635287269396635973)
                ·
                  refine ⟨2202989931616363011869245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11749279635287269396635973 2202989931616363011869245)
                  ·
                    refine ⟨826121224356136129450967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2202989931616363011869245 826121224356136129450967)
                    ·
                      rfl

theorem cell22_2413298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 1, 2, 4, 3].length) (baseStart_2413298 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2413298 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2413298 prefixEnd_2413298 := by exact prefixLift 2413298
  have htrace : WordTrace (prefixWord ++ tailWord_2413298) baseStart_2413298 baseEnd_2413298 := by
    simpa [prefixWord, tailWord_2413298, baseEnd_2413298] using wordTrace_append hprefix tailTrace_2413298
  have hstable : (prefixWord ++ tailWord_2413298).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2413298).length < 2 ^ (prefixWord ++ tailWord_2413298).sum := by decide
  have hdescent : baseEnd_2413298 < baseStart_2413298 := by decide
  rcases family_descends (prefixWord ++ tailWord_2413298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2413388 : List Nat := [2, 2, 1, 3, 3, 2, 1, 1, 2, 5]
def baseStart_2413388 : Nat := 118140960795 + 2413388 * 2 ^ 59
def prefixEnd_2413388 : Nat := 4983230072969 + 3 ^ 40 * 2413388 * 2
def baseEnd_2413388 : Nat := 826152033195405894700691

theorem tailTrace_2413388 : CollatzResearch.WordTrace tailWord_2413388 prefixEnd_2413388 826152033195405894700691 := by
  unfold tailWord_2413388
  simp only [CollatzResearch.WordTrace]
  refine ⟨44011745890357462350336409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58682327853809949800448545 44011745890357462350336409)
  ·
    refine ⟨33008809417768096762752307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44011745890357462350336409 33008809417768096762752307)
    ·
      refine ⟨49513214126652145144128461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33008809417768096762752307 49513214126652145144128461)
      ·
        refine ⟨18567455297494554429048173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 49513214126652145144128461 18567455297494554429048173)
        ·
          refine ⟨6962795736560457910893065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18567455297494554429048173 6962795736560457910893065)
          ·
            refine ⟨5222096802420343433169799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6962795736560457910893065 5222096802420343433169799)
            ·
              refine ⟨7833145203630515149754699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5222096802420343433169799 7833145203630515149754699)
              ·
                refine ⟨11749717805445772724632049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7833145203630515149754699 11749717805445772724632049)
                ·
                  refine ⟨8812288354084329543474037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11749717805445772724632049 8812288354084329543474037)
                  ·
                    refine ⟨826152033195405894700691, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8812288354084329543474037 826152033195405894700691)
                    ·
                      rfl

theorem cell22_2413388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 2, 1, 1, 2, 5].length) (baseStart_2413388 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2413388 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2413388 prefixEnd_2413388 := by exact prefixLift 2413388
  have htrace : WordTrace (prefixWord ++ tailWord_2413388) baseStart_2413388 baseEnd_2413388 := by
    simpa [prefixWord, tailWord_2413388, baseEnd_2413388] using wordTrace_append hprefix tailTrace_2413388
  have hstable : (prefixWord ++ tailWord_2413388).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2413388).length < 2 ^ (prefixWord ++ tailWord_2413388).sum := by decide
  have hdescent : baseEnd_2413388 < baseStart_2413388 := by decide
  rcases family_descends (prefixWord ++ tailWord_2413388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2413401 : List Nat := [1, 2, 1, 2, 2, 4, 1, 1, 8]
def baseStart_2413401 : Nat := 118140960795 + 2413401 * 2 ^ 59
def prefixEnd_2413401 : Nat := 4983230072969 + 3 ^ 40 * 2413401 * 2
def baseEnd_2413401 : Nat := 275385494453692731375217

theorem tailTrace_2413401 : CollatzResearch.WordTrace tailWord_2413401 prefixEnd_2413401 275385494453692731375217 := by
  unfold tailWord_2413401
  simp only [CollatzResearch.WordTrace]
  refine ⟨88023965929667827920896057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58682643953111885280597371 88023965929667827920896057)
  ·
    refine ⟨66017974447250870940672043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88023965929667827920896057 66017974447250870940672043)
    ·
      refine ⟨99026961670876306411008065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66017974447250870940672043 99026961670876306411008065)
      ·
        refine ⟨74270221253157229808256049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 99026961670876306411008065 74270221253157229808256049)
        ·
          refine ⟨55702665939867922356192037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 74270221253157229808256049 55702665939867922356192037)
          ·
            refine ⟨10444249863725235441786007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 55702665939867922356192037 10444249863725235441786007)
            ·
              refine ⟨15666374795587853162679011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10444249863725235441786007 15666374795587853162679011)
              ·
                refine ⟨23499562193381779744018517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15666374795587853162679011 23499562193381779744018517)
                ·
                  refine ⟨275385494453692731375217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 23499562193381779744018517 275385494453692731375217)
                  ·
                    rfl

theorem cell22_2413401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 1, 1, 8].length) (baseStart_2413401 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2413401 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2413401 prefixEnd_2413401 := by exact prefixLift 2413401
  have htrace : WordTrace (prefixWord ++ tailWord_2413401) baseStart_2413401 baseEnd_2413401 := by
    simpa [prefixWord, tailWord_2413401, baseEnd_2413401] using wordTrace_append hprefix tailTrace_2413401
  have hstable : (prefixWord ++ tailWord_2413401).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2413401).length < 2 ^ (prefixWord ++ tailWord_2413401).sum := by decide
  have hdescent : baseEnd_2413401 < baseStart_2413401 := by decide
  rcases family_descends (prefixWord ++ tailWord_2413401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2413448 : List Nat := [2, 1, 3, 3, 2, 1, 1, 2, 1, 6]
def baseStart_2413448 : Nat := 118140960795 + 2413448 * 2 ^ 59
def prefixEnd_2413448 : Nat := 4983230072969 + 3 ^ 40 * 2413448 * 2
def baseEnd_2413448 : Nat := 826172572421585738200507

theorem tailTrace_2413448 : CollatzResearch.WordTrace tailWord_2413448 prefixEnd_2413448 826172572421585738200507 := by
  unfold tailWord_2413448
  simp only [CollatzResearch.WordTrace]
  refine ⟨44012840080248777473928499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58683786773665036631904665 44012840080248777473928499)
  ·
    refine ⟨66019260120373166210892749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44012840080248777473928499 66019260120373166210892749)
    ·
      refine ⟨24757222545139937329084781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 66019260120373166210892749 24757222545139937329084781)
      ·
        refine ⟨9283958454427476498406793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24757222545139937329084781 9283958454427476498406793)
        ·
          refine ⟨6962968840820607373805095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9283958454427476498406793 6962968840820607373805095)
          ·
            refine ⟨10444453261230911060707643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6962968840820607373805095 10444453261230911060707643)
            ·
              refine ⟨15666679891846366591061465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10444453261230911060707643 15666679891846366591061465)
              ·
                refine ⟨11750009918884774943296099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15666679891846366591061465 11750009918884774943296099)
                ·
                  refine ⟨17625014878327162414944149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11750009918884774943296099 17625014878327162414944149)
                  ·
                    refine ⟨826172572421585738200507, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17625014878327162414944149 826172572421585738200507)
                    ·
                      rfl

theorem cell22_2413448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 1, 2, 1, 6].length) (baseStart_2413448 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2413448 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2413448 prefixEnd_2413448 := by exact prefixLift 2413448
  have htrace : WordTrace (prefixWord ++ tailWord_2413448) baseStart_2413448 baseEnd_2413448 := by
    simpa [prefixWord, tailWord_2413448, baseEnd_2413448] using wordTrace_append hprefix tailTrace_2413448
  have hstable : (prefixWord ++ tailWord_2413448).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2413448).length < 2 ^ (prefixWord ++ tailWord_2413448).sum := by decide
  have hdescent : baseEnd_2413448 < baseStart_2413448 := by decide
  rcases family_descends (prefixWord ++ tailWord_2413448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2413450 : List Nat := [3, 1, 2, 4, 1, 1, 3, 1, 1, 5]
def baseStart_2413450 : Nat := 118140960795 + 2413450 * 2 ^ 59
def prefixEnd_2413450 : Nat := 4983230072969 + 3 ^ 40 * 2413450 * 2
def baseEnd_2413450 : Nat := 826173257062458399650501

theorem tailTrace_2413450 : CollatzResearch.WordTrace tailWord_2413450 prefixEnd_2413450 826173257062458399650501 := by
  unfold tailWord_2413450
  simp only [CollatzResearch.WordTrace]
  refine ⟨22006438276622577322357451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58683835404326872859619869 22006438276622577322357451)
  ·
    refine ⟨33009657414933865983536177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22006438276622577322357451 33009657414933865983536177)
    ·
      refine ⟨24757243061200399487652133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33009657414933865983536177 24757243061200399487652133)
      ·
        refine ⟨4641983073975074903934775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 24757243061200399487652133 4641983073975074903934775)
        ·
          refine ⟨6962974610962612355902163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4641983073975074903934775 6962974610962612355902163)
          ·
            refine ⟨10444461916443918533853245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6962974610962612355902163 10444461916443918533853245)
            ·
              refine ⟨3916673218666469450194967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10444461916443918533853245 3916673218666469450194967)
              ·
                refine ⟨5875009827999704175292451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3916673218666469450194967 5875009827999704175292451)
                ·
                  refine ⟨8812514741999556262938677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5875009827999704175292451 8812514741999556262938677)
                  ·
                    refine ⟨826173257062458399650501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8812514741999556262938677 826173257062458399650501)
                    ·
                      rfl

theorem cell22_2413450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 3, 1, 1, 5].length) (baseStart_2413450 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2413450 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2413450 prefixEnd_2413450 := by exact prefixLift 2413450
  have htrace : WordTrace (prefixWord ++ tailWord_2413450) baseStart_2413450 baseEnd_2413450 := by
    simpa [prefixWord, tailWord_2413450, baseEnd_2413450] using wordTrace_append hprefix tailTrace_2413450
  have hstable : (prefixWord ++ tailWord_2413450).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2413450).length < 2 ^ (prefixWord ++ tailWord_2413450).sum := by decide
  have hdescent : baseEnd_2413450 < baseStart_2413450 := by decide
  rcases family_descends (prefixWord ++ tailWord_2413450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2413493 : List Nat := [1, 3, 3, 2, 1, 1, 2, 1, 2, 6]
def baseStart_2413493 : Nat := 118140960795 + 2413493 * 2 ^ 59
def prefixEnd_2413493 : Nat := 4983230072969 + 3 ^ 40 * 2413493 * 2
def baseEnd_2413493 : Nat := 826187976841220620825369

theorem tailTrace_2413493 : CollatzResearch.WordTrace tailWord_2413493 prefixEnd_2413493 826187976841220620825369 := by
  unfold tailWord_2413493
  simp only [CollatzResearch.WordTrace]
  refine ⟨88027321445334527633245133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58684880963556351755496755 88027321445334527633245133)
  ·
    refine ⟨33010245542000447862466925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 88027321445334527633245133 33010245542000447862466925)
    ·
      refine ⟨12378842078250167948425097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33010245542000447862466925 12378842078250167948425097)
      ·
        refine ⟨9284131558687625961318823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12378842078250167948425097 9284131558687625961318823)
        ·
          refine ⟨13926197338031438941978235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9284131558687625961318823 13926197338031438941978235)
          ·
            refine ⟨20889296007047158412967353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13926197338031438941978235 20889296007047158412967353)
            ·
              refine ⟨15666972005285368809725515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20889296007047158412967353 15666972005285368809725515)
              ·
                refine ⟨23500458007928053214588273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15666972005285368809725515 23500458007928053214588273)
                ·
                  refine ⟨17625343505946039910941205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23500458007928053214588273 17625343505946039910941205)
                  ·
                    refine ⟨826187976841220620825369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17625343505946039910941205 826187976841220620825369)
                    ·
                      rfl

theorem cell22_2413493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 2, 1, 2, 6].length) (baseStart_2413493 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2413493 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2413493 prefixEnd_2413493 := by exact prefixLift 2413493
  have htrace : WordTrace (prefixWord ++ tailWord_2413493) baseStart_2413493 baseEnd_2413493 := by
    simpa [prefixWord, tailWord_2413493, baseEnd_2413493] using wordTrace_append hprefix tailTrace_2413493
  have hstable : (prefixWord ++ tailWord_2413493).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2413493).length < 2 ^ (prefixWord ++ tailWord_2413493).sum := by decide
  have hdescent : baseEnd_2413493 < baseStart_2413493 := by decide
  rcases family_descends (prefixWord ++ tailWord_2413493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2413495 : List Nat := [1, 1, 3, 1, 3, 1, 5, 1, 3, 3]
def baseStart_2413495 : Nat := 118140960795 + 2413495 * 2 ^ 59
def prefixEnd_2413495 : Nat := 4983230072969 + 3 ^ 40 * 2413495 * 2
def baseEnd_2413495 : Nat := 826188661482093282275363

theorem tailTrace_2413495 : CollatzResearch.WordTrace tailWord_2413495 prefixEnd_2413495 826188661482093282275363 := by
  unfold tailWord_2413495
  simp only [CollatzResearch.WordTrace]
  refine ⟨88027394391327281974817939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58684929594218187983211959 88027394391327281974817939)
  ·
    refine ⟨132041091586990922962226909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88027394391327281974817939 132041091586990922962226909)
    ·
      refine ⟨49515409345121596110835091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 132041091586990922962226909 49515409345121596110835091)
      ·
        refine ⟨74273114017682394166252637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49515409345121596110835091 74273114017682394166252637)
        ·
          refine ⟨27852417756630897812344739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 74273114017682394166252637 27852417756630897812344739)
          ·
            refine ⟨41778626634946346718517109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27852417756630897812344739 41778626634946346718517109)
            ·
              refine ⟨3916746247026220004860979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 41778626634946346718517109 3916746247026220004860979)
              ·
                refine ⟨5875119370539330007291469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3916746247026220004860979 5875119370539330007291469)
                ·
                  refine ⟨2203169763952248752734301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5875119370539330007291469 2203169763952248752734301)
                  ·
                    refine ⟨826188661482093282275363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2203169763952248752734301 826188661482093282275363)
                    ·
                      rfl

theorem cell22_2413495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 5, 1, 3, 3].length) (baseStart_2413495 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2413495 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2413495 prefixEnd_2413495 := by exact prefixLift 2413495
  have htrace : WordTrace (prefixWord ++ tailWord_2413495) baseStart_2413495 baseEnd_2413495 := by
    simpa [prefixWord, tailWord_2413495, baseEnd_2413495] using wordTrace_append hprefix tailTrace_2413495
  have hstable : (prefixWord ++ tailWord_2413495).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2413495).length < 2 ^ (prefixWord ++ tailWord_2413495).sum := by decide
  have hdescent : baseEnd_2413495 < baseStart_2413495 := by decide
  rcases family_descends (prefixWord ++ tailWord_2413495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2413501 : List Nat := [1, 4, 1, 2, 5, 1, 2, 1, 2, 3]
def baseStart_2413501 : Nat := 118140960795 + 2413501 * 2 ^ 59
def prefixEnd_2413501 : Nat := 4983230072969 + 3 ^ 40 * 2413501 * 2
def baseEnd_2413501 : Nat := 826190715404711266625345

theorem tailTrace_2413501 : CollatzResearch.WordTrace tailWord_2413501 prefixEnd_2413501 826190715404711266625345 := by
  unfold tailWord_2413501
  simp only [CollatzResearch.WordTrace]
  refine ⟨88027613229305544999536357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58685075486203696666357571 88027613229305544999536357)
  ·
    refine ⟨16505177480494789687413067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 88027613229305544999536357 16505177480494789687413067)
    ·
      refine ⟨24757766220742184531119601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16505177480494789687413067 24757766220742184531119601)
      ·
        refine ⟨18568324665556638398339701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24757766220742184531119601 18568324665556638398339701)
        ·
          refine ⟨1740780437395934849844347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 18568324665556638398339701 1740780437395934849844347)
          ·
            refine ⟨2611170656093902274766521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1740780437395934849844347 2611170656093902274766521)
            ·
              refine ⟨1958377992070426706074891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2611170656093902274766521 1958377992070426706074891)
              ·
                refine ⟨2937566988105640059112337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1958377992070426706074891 2937566988105640059112337)
                ·
                  refine ⟨2203175241079230044334253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2937566988105640059112337 2203175241079230044334253)
                  ·
                    refine ⟨826190715404711266625345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2203175241079230044334253 826190715404711266625345)
                    ·
                      rfl

theorem cell22_2413501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 5, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 5, 1, 2, 1, 2, 3].length) (baseStart_2413501 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2413501 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2413501 prefixEnd_2413501 := by exact prefixLift 2413501
  have htrace : WordTrace (prefixWord ++ tailWord_2413501) baseStart_2413501 baseEnd_2413501 := by
    simpa [prefixWord, tailWord_2413501, baseEnd_2413501] using wordTrace_append hprefix tailTrace_2413501
  have hstable : (prefixWord ++ tailWord_2413501).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2413501).length < 2 ^ (prefixWord ++ tailWord_2413501).sum := by decide
  have hdescent : baseEnd_2413501 < baseStart_2413501 := by decide
  rcases family_descends (prefixWord ++ tailWord_2413501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2413546 : List Nat := [3, 1, 3, 1, 2, 4, 2, 2, 1, 3]
def baseStart_2413546 : Nat := 118140960795 + 2413546 * 2 ^ 59
def prefixEnd_2413546 : Nat := 4983230072969 + 3 ^ 40 * 2413546 * 2
def baseEnd_2413546 : Nat := 826206119824346149250207

theorem tailTrace_2413546 : CollatzResearch.WordTrace tailWord_2413546 prefixEnd_2413546 826206119824346149250207 := by
  unfold tailWord_2413546
  simp only [CollatzResearch.WordTrace]
  refine ⟨22007313628535629421231123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58686169676095011789949661 22007313628535629421231123)
  ·
    refine ⟨33010970442803444131846685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22007313628535629421231123 33010970442803444131846685)
    ·
      refine ⟨12379113916051291549442507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33010970442803444131846685 12379113916051291549442507)
      ·
        refine ⟨18568670874076937324163761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12379113916051291549442507 18568670874076937324163761)
        ·
          refine ⟨13926503155557702993122821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18568670874076937324163761 13926503155557702993122821)
          ·
            refine ⟨2611219341667069311210529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13926503155557702993122821 2611219341667069311210529)
            ·
              refine ⟨1958414506250301983407897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2611219341667069311210529 1958414506250301983407897)
              ·
                refine ⟨1468810879687726487555923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1958414506250301983407897 1468810879687726487555923)
                ·
                  refine ⟨2203216319531589731333885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1468810879687726487555923 2203216319531589731333885)
                  ·
                    refine ⟨826206119824346149250207, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2203216319531589731333885 826206119824346149250207)
                    ·
                      rfl

theorem cell22_2413546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 4, 2, 2, 1, 3].length) (baseStart_2413546 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2413546 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2413546 prefixEnd_2413546 := by exact prefixLift 2413546
  have htrace : WordTrace (prefixWord ++ tailWord_2413546) baseStart_2413546 baseEnd_2413546 := by
    simpa [prefixWord, tailWord_2413546, baseEnd_2413546] using wordTrace_append hprefix tailTrace_2413546
  have hstable : (prefixWord ++ tailWord_2413546).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2413546).length < 2 ^ (prefixWord ++ tailWord_2413546).sum := by decide
  have hdescent : baseEnd_2413546 < baseStart_2413546 := by decide
  rcases family_descends (prefixWord ++ tailWord_2413546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2413583 : List Nat := [1, 1, 2, 1, 1, 1, 2, 1, 8, 4]
def baseStart_2413583 : Nat := 118140960795 + 2413583 * 2 ^ 59
def prefixEnd_2413583 : Nat := 4983230072969 + 3 ^ 40 * 2413583 * 2
def baseEnd_2413583 : Nat := 826218785680490386075093

theorem tailTrace_2413583 : CollatzResearch.WordTrace tailWord_2413583 prefixEnd_2413583 826218785680490386075093 := by
  unfold tailWord_2413583
  simp only [CollatzResearch.WordTrace]
  refine ⟨88030604015008473004021403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58687069343338982002680935 88030604015008473004021403)
  ·
    refine ⟨132045906022512709506032105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88030604015008473004021403 132045906022512709506032105)
    ·
      refine ⟨99034429516884532129524079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 132045906022512709506032105 99034429516884532129524079)
      ·
        refine ⟨148551644275326798194286119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99034429516884532129524079 148551644275326798194286119)
        ·
          refine ⟨222827466412990197291429179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 148551644275326798194286119 222827466412990197291429179)
          ·
            refine ⟨334241199619485295937143769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 222827466412990197291429179 334241199619485295937143769)
            ·
              refine ⟨250680899714613971952857827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 334241199619485295937143769 250680899714613971952857827)
              ·
                refine ⟨376021349571920957929286741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 250680899714613971952857827 376021349571920957929286741)
                ·
                  refine ⟨4406500190295948725733829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 376021349571920957929286741 4406500190295948725733829)
                  ·
                    refine ⟨826218785680490386075093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4406500190295948725733829 826218785680490386075093)
                    ·
                      rfl

theorem cell22_2413583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 1, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 1, 8, 4].length) (baseStart_2413583 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2413583 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2413583 prefixEnd_2413583 := by exact prefixLift 2413583
  have htrace : WordTrace (prefixWord ++ tailWord_2413583) baseStart_2413583 baseEnd_2413583 := by
    simpa [prefixWord, tailWord_2413583, baseEnd_2413583] using wordTrace_append hprefix tailTrace_2413583
  have hstable : (prefixWord ++ tailWord_2413583).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2413583).length < 2 ^ (prefixWord ++ tailWord_2413583).sum := by decide
  have hdescent : baseEnd_2413583 < baseStart_2413583 := by decide
  rcases family_descends (prefixWord ++ tailWord_2413583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2413589 : List Nat := [1, 3, 2, 1, 4, 3, 2, 1, 1, 4]
def baseStart_2413589 : Nat := 118140960795 + 2413589 * 2 ^ 59
def prefixEnd_2413589 : Nat := 4983230072969 + 3 ^ 40 * 2413589 * 2
def baseEnd_2413589 : Nat := 826220839603108370425075

theorem tailTrace_2413589 : CollatzResearch.WordTrace tailWord_2413589 prefixEnd_2413589 826220839603108370425075 := by
  unfold tailWord_2413589
  simp only [CollatzResearch.WordTrace]
  refine ⟨88030822852986736028739821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58687215235324490685826547 88030822852986736028739821)
  ·
    refine ⟨33011558569870026010777433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 88030822852986736028739821 33011558569870026010777433)
    ·
      refine ⟨24758668927402519508083075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33011558569870026010777433 24758668927402519508083075)
      ·
        refine ⟨37138003391103779262124613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24758668927402519508083075 37138003391103779262124613)
        ·
          refine ⟨6963375635831958611648365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 37138003391103779262124613 6963375635831958611648365)
          ·
            refine ⟨2611265863436984479368137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6963375635831958611648365 2611265863436984479368137)
            ·
              refine ⟨1958449397577738359526103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2611265863436984479368137 1958449397577738359526103)
              ·
                refine ⟨2937674096366607539289155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1958449397577738359526103 2937674096366607539289155)
                ·
                  refine ⟨4406511144549911308933733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2937674096366607539289155 4406511144549911308933733)
                  ·
                    refine ⟨826220839603108370425075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4406511144549911308933733 826220839603108370425075)
                    ·
                      rfl

theorem cell22_2413589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 3, 2, 1, 1, 4].length) (baseStart_2413589 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2413589 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2413589 prefixEnd_2413589 := by exact prefixLift 2413589
  have htrace : WordTrace (prefixWord ++ tailWord_2413589) baseStart_2413589 baseEnd_2413589 := by
    simpa [prefixWord, tailWord_2413589, baseEnd_2413589] using wordTrace_append hprefix tailTrace_2413589
  have hstable : (prefixWord ++ tailWord_2413589).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2413589).length < 2 ^ (prefixWord ++ tailWord_2413589).sum := by decide
  have hdescent : baseEnd_2413589 < baseStart_2413589 := by decide
  rcases family_descends (prefixWord ++ tailWord_2413589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2413602 : List Nat := [3, 3, 1, 1, 1, 4, 1, 1, 4, 3]
def baseStart_2413602 : Nat := 118140960795 + 2413602 * 2 ^ 59
def prefixEnd_2413602 : Nat := 4983230072969 + 3 ^ 40 * 2413602 * 2
def baseEnd_2413602 : Nat := 826225289768780669850035

theorem tailTrace_2413602 : CollatzResearch.WordTrace tailWord_2413602 prefixEnd_2413602 826225289768780669850035 := by
  unfold tailWord_2413602
  simp only [CollatzResearch.WordTrace]
  refine ⟨22007824250484909812240765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58687531334626426165975373 22007824250484909812240765)
  ·
    refine ⟨8252934093931841179590287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22007824250484909812240765 8252934093931841179590287)
    ·
      refine ⟨12379401140897761769385431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8252934093931841179590287 12379401140897761769385431)
      ·
        refine ⟨18569101711346642654078147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12379401140897761769385431 18569101711346642654078147)
        ·
          refine ⟨27853652567019963981117221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18569101711346642654078147 27853652567019963981117221)
          ·
            refine ⟨5222559856316243246459479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27853652567019963981117221 5222559856316243246459479)
            ·
              refine ⟨7833839784474364869689219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5222559856316243246459479 7833839784474364869689219)
              ·
                refine ⟨11750759676711547304533829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7833839784474364869689219 11750759676711547304533829)
                ·
                  refine ⟨2203267439383415119600093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11750759676711547304533829 2203267439383415119600093)
                  ·
                    refine ⟨826225289768780669850035, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2203267439383415119600093 826225289768780669850035)
                    ·
                      rfl

theorem cell22_2413602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 4, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 4, 1, 1, 4, 3].length) (baseStart_2413602 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2413602 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2413602 prefixEnd_2413602 := by exact prefixLift 2413602
  have htrace : WordTrace (prefixWord ++ tailWord_2413602) baseStart_2413602 baseEnd_2413602 := by
    simpa [prefixWord, tailWord_2413602, baseEnd_2413602] using wordTrace_append hprefix tailTrace_2413602
  have hstable : (prefixWord ++ tailWord_2413602).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2413602).length < 2 ^ (prefixWord ++ tailWord_2413602).sum := by decide
  have hdescent : baseEnd_2413602 < baseStart_2413602 := by decide
  rcases family_descends (prefixWord ++ tailWord_2413602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2413660 : List Nat := [2, 2, 4, 1, 1, 1, 1, 3, 7]
def baseStart_2413660 : Nat := 118140960795 + 2413660 * 2 ^ 59
def prefixEnd_2413660 : Nat := 4983230072969 + 3 ^ 40 * 2413660 * 2
def baseEnd_2413660 : Nat := 275415048118029283966619

theorem tailTrace_2413660 : CollatzResearch.WordTrace tailWord_2413660 prefixEnd_2413660 275415048118029283966619 := by
  unfold tailWord_2413660
  simp only [CollatzResearch.WordTrace]
  refine ⟨44016706217864757577287217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58688941623819676769716289 44016706217864757577287217)
  ·
    refine ⟨33012529663398568182965413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44016706217864757577287217 33012529663398568182965413)
    ·
      refine ⟨6189849311887231534306015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 33012529663398568182965413 6189849311887231534306015)
      ·
        refine ⟨9284773967830847301459023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6189849311887231534306015 9284773967830847301459023)
        ·
          refine ⟨13927160951746270952188535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9284773967830847301459023 13927160951746270952188535)
          ·
            refine ⟨20890741427619406428282803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13927160951746270952188535 20890741427619406428282803)
            ·
              refine ⟨31336112141429109642424205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20890741427619406428282803 31336112141429109642424205)
              ·
                refine ⟨11751042053035916115909077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31336112141429109642424205 11751042053035916115909077)
                ·
                  refine ⟨275415048118029283966619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11751042053035916115909077 275415048118029283966619)
                  ·
                    rfl

theorem cell22_2413660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 1, 3, 7].length) (baseStart_2413660 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2413660 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2413660 prefixEnd_2413660 := by exact prefixLift 2413660
  have htrace : WordTrace (prefixWord ++ tailWord_2413660) baseStart_2413660 baseEnd_2413660 := by
    simpa [prefixWord, tailWord_2413660, baseEnd_2413660] using wordTrace_append hprefix tailTrace_2413660
  have hstable : (prefixWord ++ tailWord_2413660).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2413660).length < 2 ^ (prefixWord ++ tailWord_2413660).sum := by decide
  have hdescent : baseEnd_2413660 < baseStart_2413660 := by decide
  rcases family_descends (prefixWord ++ tailWord_2413660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2413677 : List Nat := [1, 5, 1, 1, 2, 3, 1, 3, 5]
def baseStart_2413677 : Nat := 118140960795 + 2413677 * 2 ^ 59
def prefixEnd_2413677 : Nat := 4983230072969 + 3 ^ 40 * 2413677 * 2
def baseEnd_2413677 : Nat := 275416987933835158074935

theorem tailTrace_2413677 : CollatzResearch.WordTrace tailWord_2413677 prefixEnd_2413677 275416987933835158074935 := by
  unfold tailWord_2413677
  simp only [CollatzResearch.WordTrace]
  refine ⟨88034032476667927057943285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58689354984445284705295523 88034032476667927057943285)
  ·
    refine ⟨8253190544687618161682183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 88034032476667927057943285 8253190544687618161682183)
    ·
      refine ⟨12379785817031427242523275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8253190544687618161682183 12379785817031427242523275)
      ·
        refine ⟨18569678725547140863784913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12379785817031427242523275 18569678725547140863784913)
        ·
          refine ⟨13927259044160355647838685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18569678725547140863784913 13927259044160355647838685)
          ·
            refine ⟨5222722141560133367939507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13927259044160355647838685 5222722141560133367939507)
            ·
              refine ⟨7834083212340200051909261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5222722141560133367939507 7834083212340200051909261)
              ·
                refine ⟨2937781204627575019465973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7834083212340200051909261 2937781204627575019465973)
                ·
                  refine ⟨275416987933835158074935, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2937781204627575019465973 275416987933835158074935)
                  ·
                    rfl

theorem cell22_2413677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 3, 1, 3, 5].length) (baseStart_2413677 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2413677 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2413677 prefixEnd_2413677 := by exact prefixLift 2413677
  have htrace : WordTrace (prefixWord ++ tailWord_2413677) baseStart_2413677 baseEnd_2413677 := by
    simpa [prefixWord, tailWord_2413677, baseEnd_2413677] using wordTrace_append hprefix tailTrace_2413677
  have hstable : (prefixWord ++ tailWord_2413677).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2413677).length < 2 ^ (prefixWord ++ tailWord_2413677).sum := by decide
  have hdescent : baseEnd_2413677 < baseStart_2413677 := by decide
  rcases family_descends (prefixWord ++ tailWord_2413677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2413859 : List Nat := [1, 1, 1, 4, 2, 3, 3, 2, 1, 4]
def baseStart_2413859 : Nat := 118140960795 + 2413859 * 2 ^ 59
def prefixEnd_2413859 : Nat := 4983230072969 + 3 ^ 40 * 2413859 * 2
def baseEnd_2413859 : Nat := 826313266120917666174247

theorem tailTrace_2413859 : CollatzResearch.WordTrace tailWord_2413859 prefixEnd_2413859 826313266120917666174247 := by
  unfold tailWord_2413859
  simp only [CollatzResearch.WordTrace]
  refine ⟨88040670562008572141068631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58693780374672381427379087 88040670562008572141068631)
  ·
    refine ⟨132061005843012858211602947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88040670562008572141068631 132061005843012858211602947)
    ·
      refine ⟨198091508764519287317404421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132061005843012858211602947 198091508764519287317404421)
      ·
        refine ⟨37142157893347366372013329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 198091508764519287317404421 37142157893347366372013329)
        ·
          refine ⟨27856618420010524779009997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37142157893347366372013329 27856618420010524779009997)
          ·
            refine ⟨10446231907503946792128749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27856618420010524779009997 10446231907503946792128749)
            ·
              refine ⟨3917336965313980047048281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10446231907503946792128749 3917336965313980047048281)
              ·
                refine ⟨2938002723985485035286211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3917336965313980047048281 2938002723985485035286211)
                ·
                  refine ⟨4407004085978227552929317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2938002723985485035286211 4407004085978227552929317)
                  ·
                    refine ⟨826313266120917666174247, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4407004085978227552929317 826313266120917666174247)
                    ·
                      rfl

theorem cell22_2413859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 3, 2, 1, 4].length) (baseStart_2413859 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2413859 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2413859 prefixEnd_2413859 := by exact prefixLift 2413859
  have htrace : WordTrace (prefixWord ++ tailWord_2413859) baseStart_2413859 baseEnd_2413859 := by
    simpa [prefixWord, tailWord_2413859, baseEnd_2413859] using wordTrace_append hprefix tailTrace_2413859
  have hstable : (prefixWord ++ tailWord_2413859).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2413859).length < 2 ^ (prefixWord ++ tailWord_2413859).sum := by decide
  have hdescent : baseEnd_2413859 < baseStart_2413859 := by decide
  rcases family_descends (prefixWord ++ tailWord_2413859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2413872 : List Nat := [2, 1, 1, 1, 2, 2, 5, 2, 1, 5]
def baseStart_2413872 : Nat := 118140960795 + 2413872 * 2 ^ 59
def prefixEnd_2413872 : Nat := 4983230072969 + 3 ^ 40 * 2413872 * 2
def baseEnd_2413872 : Nat := 826317716286589965599207

theorem tailTrace_2413872 : CollatzResearch.WordTrace tailWord_2413872 prefixEnd_2413872 826317716286589965599207 := by
  unfold tailWord_2413872
  simp only [CollatzResearch.WordTrace]
  refine ⟨44020572355480737680645935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58694096473974316907527913 44020572355480737680645935)
  ·
    refine ⟨66030858533221106520968903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44020572355480737680645935 66030858533221106520968903)
    ·
      refine ⟨99046287799831659781453355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66030858533221106520968903 99046287799831659781453355)
      ·
        refine ⟨148569431699747489672180033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99046287799831659781453355 148569431699747489672180033)
        ·
          refine ⟨111427073774810617254135025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 148569431699747489672180033 111427073774810617254135025)
          ·
            refine ⟨83570305331107962940601269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 111427073774810617254135025 83570305331107962940601269)
            ·
              refine ⟨7834716124791371525681369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 83570305331107962940601269 7834716124791371525681369)
              ·
                refine ⟨5876037093593528644261027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7834716124791371525681369 5876037093593528644261027)
                ·
                  refine ⟨8814055640390292966391541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5876037093593528644261027 8814055640390292966391541)
                  ·
                    refine ⟨826317716286589965599207, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8814055640390292966391541 826317716286589965599207)
                    ·
                      rfl

theorem cell22_2413872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 5, 2, 1, 5].length) (baseStart_2413872 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2413872 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2413872 prefixEnd_2413872 := by exact prefixLift 2413872
  have htrace : WordTrace (prefixWord ++ tailWord_2413872) baseStart_2413872 baseEnd_2413872 := by
    simpa [prefixWord, tailWord_2413872, baseEnd_2413872] using wordTrace_append hprefix tailTrace_2413872
  have hstable : (prefixWord ++ tailWord_2413872).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2413872).length < 2 ^ (prefixWord ++ tailWord_2413872).sum := by decide
  have hdescent : baseEnd_2413872 < baseStart_2413872 := by decide
  rcases family_descends (prefixWord ++ tailWord_2413872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2413947 : List Nat := [1, 1, 1, 1, 1, 6, 3, 1, 7]
def baseStart_2413947 : Nat := 118140960795 + 2413947 * 2 ^ 59
def prefixEnd_2413947 : Nat := 4983230072969 + 3 ^ 40 * 2413947 * 2
def baseEnd_2413947 : Nat := 275447796773104923324659

theorem tailTrace_2413947 : CollatzResearch.WordTrace tailWord_2413947 prefixEnd_2413947 275447796773104923324659 := by
  unfold tailWord_2413947
  simp only [CollatzResearch.WordTrace]
  refine ⟨88043880185689763170272095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58695920123793175446848063 88043880185689763170272095)
  ·
    refine ⟨132065820278534644755408143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88043880185689763170272095 132065820278534644755408143)
    ·
      refine ⟨198098730417801967133112215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132065820278534644755408143 198098730417801967133112215)
      ·
        refine ⟨297148095626702950699668323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 198098730417801967133112215 297148095626702950699668323)
        ·
          refine ⟨445722143440054426049502485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 297148095626702950699668323 445722143440054426049502485)
          ·
            refine ⟨20893225473752551221070429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 445722143440054426049502485 20893225473752551221070429)
            ·
              refine ⟨7834959552657206707901411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20893225473752551221070429 7834959552657206707901411)
              ·
                refine ⟨11752439328985810061852117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7834959552657206707901411 11752439328985810061852117)
                ·
                  refine ⟨275447796773104923324659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11752439328985810061852117 275447796773104923324659)
                  ·
                    rfl

theorem cell22_2413947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 3, 1, 7].length) (baseStart_2413947 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2413947 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2413947 prefixEnd_2413947 := by exact prefixLift 2413947
  have htrace : WordTrace (prefixWord ++ tailWord_2413947) baseStart_2413947 baseEnd_2413947 := by
    simpa [prefixWord, tailWord_2413947, baseEnd_2413947] using wordTrace_append hprefix tailTrace_2413947
  have hstable : (prefixWord ++ tailWord_2413947).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2413947).length < 2 ^ (prefixWord ++ tailWord_2413947).sum := by decide
  have hdescent : baseEnd_2413947 < baseStart_2413947 := by decide
  rcases family_descends (prefixWord ++ tailWord_2413947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2413970 : List Nat := [3, 2, 3, 3, 2, 1, 2, 6]
def baseStart_2413970 : Nat := 118140960795 + 2413970 * 2 ^ 59
def prefixEnd_2413970 : Nat := 4983230072969 + 3 ^ 40 * 2413970 * 2
def baseEnd_2413970 : Nat := 91816807076594486294323

theorem tailTrace_2413970 : CollatzResearch.WordTrace tailWord_2413970 prefixEnd_2413970 91816807076594486294323 := by
  unfold tailWord_2413970
  simp only [CollatzResearch.WordTrace]
  refine ⟨22011179766151609524589841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58696479376404292065572909 22011179766151609524589841)
  ·
    refine ⟨16508384824613707143442381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22011179766151609524589841 16508384824613707143442381)
    ·
      refine ⟨6190644309230140178790893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16508384824613707143442381 6190644309230140178790893)
      ·
        refine ⟨2321491615961302567046585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6190644309230140178790893 2321491615961302567046585)
        ·
          refine ⟨1741118711970976925284939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2321491615961302567046585 1741118711970976925284939)
          ·
            refine ⟨2611678067956465387927409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1741118711970976925284939 2611678067956465387927409)
            ·
              refine ⟨1958758550967349040945557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2611678067956465387927409 1958758550967349040945557)
              ·
                refine ⟨91816807076594486294323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1958758550967349040945557 91816807076594486294323)
                ·
                  rfl

theorem cell22_2413970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 2, 1, 2, 6].length) (baseStart_2413970 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2413970 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2413970 prefixEnd_2413970 := by exact prefixLift 2413970
  have htrace : WordTrace (prefixWord ++ tailWord_2413970) baseStart_2413970 baseEnd_2413970 := by
    simpa [prefixWord, tailWord_2413970, baseEnd_2413970] using wordTrace_append hprefix tailTrace_2413970
  have hstable : (prefixWord ++ tailWord_2413970).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2413970).length < 2 ^ (prefixWord ++ tailWord_2413970).sum := by decide
  have hdescent : baseEnd_2413970 < baseStart_2413970 := by decide
  rcases family_descends (prefixWord ++ tailWord_2413970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2414024 : List Nat := [2, 1, 3, 1, 3, 1, 2, 3, 1, 5]
def baseStart_2414024 : Nat := 118140960795 + 2414024 * 2 ^ 59
def prefixEnd_2414024 : Nat := 4983230072969 + 3 ^ 40 * 2414024 * 2
def baseEnd_2414024 : Nat := 826369748992912235798741

theorem tailTrace_2414024 : CollatzResearch.WordTrace tailWord_2414024 prefixEnd_2414024 826369748992912235798741 := by
  unfold tailWord_2414024
  simp only [CollatzResearch.WordTrace]
  refine ⟨44023344303205402660412563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58697792404273870213883417 44023344303205402660412563)
  ·
    refine ⟨66035016454808103990618845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44023344303205402660412563 66035016454808103990618845)
    ·
      refine ⟨24763131170553038996482067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 66035016454808103990618845 24763131170553038996482067)
      ·
        refine ⟨37144696755829558494723101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24763131170553038996482067 37144696755829558494723101)
        ·
          refine ⟨13929261283436084435521163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37144696755829558494723101 13929261283436084435521163)
          ·
            refine ⟨20893891925154126653281745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13929261283436084435521163 20893891925154126653281745)
            ·
              refine ⟨15670418943865594989961309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20893891925154126653281745 15670418943865594989961309)
              ·
                refine ⟨5876407103949598121235491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15670418943865594989961309 5876407103949598121235491)
                ·
                  refine ⟨8814610655924397181853237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5876407103949598121235491 8814610655924397181853237)
                  ·
                    refine ⟨826369748992912235798741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8814610655924397181853237 826369748992912235798741)
                    ·
                      rfl

theorem cell22_2414024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 2, 3, 1, 5].length) (baseStart_2414024 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2414024 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2414024 prefixEnd_2414024 := by exact prefixLift 2414024
  have htrace : WordTrace (prefixWord ++ tailWord_2414024) baseStart_2414024 baseEnd_2414024 := by
    simpa [prefixWord, tailWord_2414024, baseEnd_2414024] using wordTrace_append hprefix tailTrace_2414024
  have hstable : (prefixWord ++ tailWord_2414024).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2414024).length < 2 ^ (prefixWord ++ tailWord_2414024).sum := by decide
  have hdescent : baseEnd_2414024 < baseStart_2414024 := by decide
  rcases family_descends (prefixWord ++ tailWord_2414024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2414028 : List Nat := [2, 2, 1, 4, 2, 3, 1, 2, 1, 4]
def baseStart_2414028 : Nat := 118140960795 + 2414028 * 2 ^ 59
def prefixEnd_2414028 : Nat := 4983230072969 + 3 ^ 40 * 2414028 * 2
def baseEnd_2414028 : Nat := 826371118274657558698729

theorem tailTrace_2414028 : CollatzResearch.WordTrace tailWord_2414028 prefixEnd_2414028 826371118274657558698729 := by
  unfold tailWord_2414028
  simp only [CollatzResearch.WordTrace]
  refine ⟨44023417249198157001985369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58697889665597542669313825 44023417249198157001985369)
  ·
    refine ⟨33017562936898617751489027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44023417249198157001985369 33017562936898617751489027)
    ·
      refine ⟨49526344405347926627233541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33017562936898617751489027 49526344405347926627233541)
      ·
        refine ⟨9286189576002736242606289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 49526344405347926627233541 9286189576002736242606289)
        ·
          refine ⟨6964642182002052181954717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9286189576002736242606289 6964642182002052181954717)
          ·
            refine ⟨2611740818250769568233019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6964642182002052181954717 2611740818250769568233019)
            ·
              refine ⟨3917611227376154352349529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2611740818250769568233019 3917611227376154352349529)
              ·
                refine ⟨2938208420532115764262147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3917611227376154352349529 2938208420532115764262147)
                ·
                  refine ⟨4407312630798173646393221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2938208420532115764262147 4407312630798173646393221)
                  ·
                    refine ⟨826371118274657558698729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4407312630798173646393221 826371118274657558698729)
                    ·
                      rfl

theorem cell22_2414028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 3, 1, 2, 1, 4].length) (baseStart_2414028 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2414028 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2414028 prefixEnd_2414028 := by exact prefixLift 2414028
  have htrace : WordTrace (prefixWord ++ tailWord_2414028) baseStart_2414028 baseEnd_2414028 := by
    simpa [prefixWord, tailWord_2414028, baseEnd_2414028] using wordTrace_append hprefix tailTrace_2414028
  have hstable : (prefixWord ++ tailWord_2414028).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2414028).length < 2 ^ (prefixWord ++ tailWord_2414028).sum := by decide
  have hdescent : baseEnd_2414028 < baseStart_2414028 := by decide
  rcases family_descends (prefixWord ++ tailWord_2414028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2414120 : List Nat := [2, 1, 5, 2, 2, 1, 2, 1, 3, 3]
def baseStart_2414120 : Nat := 118140960795 + 2414120 * 2 ^ 59
def prefixEnd_2414120 : Nat := 4983230072969 + 3 ^ 40 * 2414120 * 2
def baseEnd_2414120 : Nat := 826402611754799985398447

theorem tailTrace_2414120 : CollatzResearch.WordTrace tailWord_2414120 prefixEnd_2414120 826402611754799985398447 := by
  unfold tailWord_2414120
  simp only [CollatzResearch.WordTrace]
  refine ⟨44025095007031506858159907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58700126676042009144213209 44025095007031506858159907)
  ·
    refine ⟨66037642510547260287239861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44025095007031506858159907 66037642510547260287239861)
    ·
      refine ⟨6191028985363805651928737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 66037642510547260287239861 6191028985363805651928737)
      ·
        refine ⟨4643271739022854238946553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6191028985363805651928737 4643271739022854238946553)
        ·
          refine ⟨3482453804267140679209915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4643271739022854238946553 3482453804267140679209915)
          ·
            refine ⟨5223680706400711018814873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3482453804267140679209915 5223680706400711018814873)
            ·
              refine ⟨3917760529800533264111155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5223680706400711018814873 3917760529800533264111155)
              ·
                refine ⟨5876640794700799896166733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3917760529800533264111155 5876640794700799896166733)
                ·
                  refine ⟨2203740298012799961062525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5876640794700799896166733 2203740298012799961062525)
                  ·
                    refine ⟨826402611754799985398447, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2203740298012799961062525 826402611754799985398447)
                    ·
                      rfl

theorem cell22_2414120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 1, 2, 1, 3, 3].length) (baseStart_2414120 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2414120 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2414120 prefixEnd_2414120 := by exact prefixLift 2414120
  have htrace : WordTrace (prefixWord ++ tailWord_2414120) baseStart_2414120 baseEnd_2414120 := by
    simpa [prefixWord, tailWord_2414120, baseEnd_2414120] using wordTrace_append hprefix tailTrace_2414120
  have hstable : (prefixWord ++ tailWord_2414120).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2414120).length < 2 ^ (prefixWord ++ tailWord_2414120).sum := by decide
  have hdescent : baseEnd_2414120 < baseStart_2414120 := by decide
  rcases family_descends (prefixWord ++ tailWord_2414120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2414133 : List Nat := [1, 3, 3, 1, 1, 4, 3, 1, 5]
def baseStart_2414133 : Nat := 118140960795 + 2414133 * 2 ^ 59
def prefixEnd_2414133 : Nat := 4983230072969 + 3 ^ 40 * 2414133 * 2
def baseEnd_2414133 : Nat := 275469020640157428274469

theorem tailTrace_2414133 : CollatzResearch.WordTrace tailWord_2414133 prefixEnd_2414133 275469020640157428274469 := by
  unfold tailWord_2414133
  simp only [CollatzResearch.WordTrace]
  refine ⟨88050664163015916936543053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58700442775343944624362035 88050664163015916936543053)
  ·
    refine ⟨33018999061130968851203645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 88050664163015916936543053 33018999061130968851203645)
    ·
      refine ⟨12382124647924113319201367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33018999061130968851203645 12382124647924113319201367)
      ·
        refine ⟨18573186971886169978802051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12382124647924113319201367 18573186971886169978802051)
        ·
          refine ⟨27859780457829254968203077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18573186971886169978802051 27859780457829254968203077)
          ·
            refine ⟨5223708835842985306538077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27859780457829254968203077 5223708835842985306538077)
            ·
              refine ⟨1958890813441119489951779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5223708835842985306538077 1958890813441119489951779)
              ·
                refine ⟨2938336220161679234927669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1958890813441119489951779 2938336220161679234927669)
                ·
                  refine ⟨275469020640157428274469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2938336220161679234927669 275469020640157428274469)
                  ·
                    rfl

theorem cell22_2414133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 4, 3, 1, 5].length) (baseStart_2414133 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2414133 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2414133 prefixEnd_2414133 := by exact prefixLift 2414133
  have htrace : WordTrace (prefixWord ++ tailWord_2414133) baseStart_2414133 baseEnd_2414133 := by
    simpa [prefixWord, tailWord_2414133, baseEnd_2414133] using wordTrace_append hprefix tailTrace_2414133
  have hstable : (prefixWord ++ tailWord_2414133).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2414133).length < 2 ^ (prefixWord ++ tailWord_2414133).sum := by decide
  have hdescent : baseEnd_2414133 < baseStart_2414133 := by decide
  rcases family_descends (prefixWord ++ tailWord_2414133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2414159 : List Nat := [1, 1, 2, 1, 1, 2, 3, 3, 3, 5]
def baseStart_2414159 : Nat := 118140960795 + 2414159 * 2 ^ 59
def prefixEnd_2414159 : Nat := 4983230072969 + 3 ^ 40 * 2414159 * 2
def baseEnd_2414159 : Nat := 826415962251816883673327

theorem tailTrace_2414159 : CollatzResearch.WordTrace tailWord_2414159 prefixEnd_2414159 826415962251816883673327 := by
  unfold tailWord_2414159
  simp only [CollatzResearch.WordTrace]
  refine ⟨88051612460921723376989531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58701074973947815584659687 88051612460921723376989531)
  ·
    refine ⟨132077418691382585065484297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88051612460921723376989531 132077418691382585065484297)
    ·
      refine ⟨99058064018536938799113223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 132077418691382585065484297 99058064018536938799113223)
      ·
        refine ⟨148587096027805408198669835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99058064018536938799113223 148587096027805408198669835)
        ·
          refine ⟨222880644041708112298004753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 148587096027805408198669835 222880644041708112298004753)
          ·
            refine ⟨167160483031281084223503565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 222880644041708112298004753 167160483031281084223503565)
            ·
              refine ⟨62685181136730406583813837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 167160483031281084223503565 62685181136730406583813837)
              ·
                refine ⟨23506942926273902468930189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 62685181136730406583813837 23506942926273902468930189)
                ·
                  refine ⟨8815103597352713425848821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23506942926273902468930189 8815103597352713425848821)
                  ·
                    refine ⟨826415962251816883673327, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8815103597352713425848821 826415962251816883673327)
                    ·
                      rfl

theorem cell22_2414159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 3, 3, 5].length) (baseStart_2414159 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2414159 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2414159 prefixEnd_2414159 := by exact prefixLift 2414159
  have htrace : WordTrace (prefixWord ++ tailWord_2414159) baseStart_2414159 baseEnd_2414159 := by
    simpa [prefixWord, tailWord_2414159, baseEnd_2414159] using wordTrace_append hprefix tailTrace_2414159
  have hstable : (prefixWord ++ tailWord_2414159).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2414159).length < 2 ^ (prefixWord ++ tailWord_2414159).sum := by decide
  have hdescent : baseEnd_2414159 < baseStart_2414159 := by decide
  rcases family_descends (prefixWord ++ tailWord_2414159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2414285 : List Nat := [1, 6, 2, 1, 1, 2, 1, 1, 7]
def baseStart_2414285 : Nat := 118140960795 + 2414285 * 2 ^ 59
def prefixEnd_2414285 : Nat := 4983230072969 + 3 ^ 40 * 2414285 * 2
def baseEnd_2414285 : Nat := 275486364875598185007647

theorem tailTrace_2414285 : CollatzResearch.WordTrace tailWord_2414285 prefixEnd_2414285 275486364875598185007647 := by
  unfold tailWord_2414285
  simp only [CollatzResearch.WordTrace]
  refine ⟨88056208058465246896076309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58704138705643497930717539 88056208058465246896076309)
  ·
    refine ⟨4127634752740558448253577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 88056208058465246896076309 4127634752740558448253577)
    ·
      refine ⟨3095726064555418836190183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4127634752740558448253577 3095726064555418836190183)
      ·
        refine ⟨4643589096833128254285275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3095726064555418836190183 4643589096833128254285275)
        ·
          refine ⟨6965383645249692381427913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4643589096833128254285275 6965383645249692381427913)
          ·
            refine ⟨5224037733937269286070935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6965383645249692381427913 5224037733937269286070935)
            ·
              refine ⟨7836056600905903929106403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5224037733937269286070935 7836056600905903929106403)
              ·
                refine ⟨11754084901358855893659605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7836056600905903929106403 11754084901358855893659605)
                ·
                  refine ⟨275486364875598185007647, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11754084901358855893659605 275486364875598185007647)
                  ·
                    rfl

theorem cell22_2414285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 2, 1, 1, 7].length) (baseStart_2414285 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2414285 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2414285 prefixEnd_2414285 := by exact prefixLift 2414285
  have htrace : WordTrace (prefixWord ++ tailWord_2414285) baseStart_2414285 baseEnd_2414285 := by
    simpa [prefixWord, tailWord_2414285, baseEnd_2414285] using wordTrace_append hprefix tailTrace_2414285
  have hstable : (prefixWord ++ tailWord_2414285).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2414285).length < 2 ^ (prefixWord ++ tailWord_2414285).sum := by decide
  have hdescent : baseEnd_2414285 < baseStart_2414285 := by decide
  rcases family_descends (prefixWord ++ tailWord_2414285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2414362 : List Nat := [3, 1, 1, 3, 2, 2, 4, 1, 2, 3]
def baseStart_2414362 : Nat := 118140960795 + 2414362 * 2 ^ 59
def prefixEnd_2414362 : Nat := 4983230072969 + 3 ^ 40 * 2414362 * 2
def baseEnd_2414362 : Nat := 826485453300392020847705

theorem tailTrace_2414362 : CollatzResearch.WordTrace tailWord_2414362 prefixEnd_2414362 826485453300392020847705 := by
  unfold tailWord_2414362
  simp only [CollatzResearch.WordTrace]
  refine ⟨22014754119796572261657335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58706010986124192697752893 22014754119796572261657335)
  ·
    refine ⟨33022131179694858392486003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22014754119796572261657335 33022131179694858392486003)
    ·
      refine ⟨49533196769542287588729005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33022131179694858392486003 49533196769542287588729005)
      ·
        refine ⟨18574948788578357845773377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 49533196769542287588729005 18574948788578357845773377)
        ·
          refine ⟨13931211591433768384330033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18574948788578357845773377 13931211591433768384330033)
          ·
            refine ⟨10448408693575326288247525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13931211591433768384330033 10448408693575326288247525)
            ·
              refine ⟨1959076630045373679046411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10448408693575326288247525 1959076630045373679046411)
              ·
                refine ⟨2938614945068060518569617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1959076630045373679046411 2938614945068060518569617)
                ·
                  refine ⟨2203961208801045388927213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2938614945068060518569617 2203961208801045388927213)
                  ·
                    refine ⟨826485453300392020847705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2203961208801045388927213 826485453300392020847705)
                    ·
                      rfl

theorem cell22_2414362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 4, 1, 2, 3].length) (baseStart_2414362 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2414362 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2414362 prefixEnd_2414362 := by exact prefixLift 2414362
  have htrace : WordTrace (prefixWord ++ tailWord_2414362) baseStart_2414362 baseEnd_2414362 := by
    simpa [prefixWord, tailWord_2414362, baseEnd_2414362] using wordTrace_append hprefix tailTrace_2414362
  have hstable : (prefixWord ++ tailWord_2414362).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2414362).length < 2 ^ (prefixWord ++ tailWord_2414362).sum := by decide
  have hdescent : baseEnd_2414362 < baseStart_2414362 := by decide
  rcases family_descends (prefixWord ++ tailWord_2414362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2414366 : List Nat := [4, 3, 2, 2, 1, 2, 1, 2, 1, 4]
def baseStart_2414366 : Nat := 118140960795 + 2414366 * 2 ^ 59
def prefixEnd_2414366 : Nat := 4983230072969 + 3 ^ 40 * 2414366 * 2
def baseEnd_2414366 : Nat := 826486822582137343747693

theorem tailTrace_2414366 : CollatzResearch.WordTrace tailWord_2414366 prefixEnd_2414366 826486822582137343747693 := by
  unfold tailWord_2414366
  simp only [CollatzResearch.WordTrace]
  refine ⟨11007395296396474716221869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 58706108247447865153183301 11007395296396474716221869)
  ·
    refine ⟨4127773236148678018583201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11007395296396474716221869 4127773236148678018583201)
    ·
      refine ⟨3095829927111508513937401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4127773236148678018583201 3095829927111508513937401)
      ·
        refine ⟨2321872445333631385453051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3095829927111508513937401 2321872445333631385453051)
        ·
          refine ⟨3482808668000447078179577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2321872445333631385453051 3482808668000447078179577)
          ·
            refine ⟨2612106501000335308634683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3482808668000447078179577 2612106501000335308634683)
            ·
              refine ⟨3918159751500502962952025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2612106501000335308634683 3918159751500502962952025)
              ·
                refine ⟨2938619813625377222214019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3918159751500502962952025 2938619813625377222214019)
                ·
                  refine ⟨4407929720438065833321029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2938619813625377222214019 4407929720438065833321029)
                  ·
                    refine ⟨826486822582137343747693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4407929720438065833321029 826486822582137343747693)
                    ·
                      rfl

theorem cell22_2414366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 2, 1, 2, 1, 4].length) (baseStart_2414366 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2414366 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2414366 prefixEnd_2414366 := by exact prefixLift 2414366
  have htrace : WordTrace (prefixWord ++ tailWord_2414366) baseStart_2414366 baseEnd_2414366 := by
    simpa [prefixWord, tailWord_2414366, baseEnd_2414366] using wordTrace_append hprefix tailTrace_2414366
  have hstable : (prefixWord ++ tailWord_2414366).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2414366).length < 2 ^ (prefixWord ++ tailWord_2414366).sum := by decide
  have hdescent : baseEnd_2414366 < baseStart_2414366 := by decide
  rcases family_descends (prefixWord ++ tailWord_2414366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2414403 : List Nat := [1, 1, 1, 3, 1, 5, 1, 4, 5]
def baseStart_2414403 : Nat := 118140960795 + 2414403 * 2 ^ 59
def prefixEnd_2414403 : Nat := 4983230072969 + 3 ^ 40 * 2414403 * 2
def baseEnd_2414403 : Nat := 275499829479427193524193

theorem tailTrace_2414403 : CollatzResearch.WordTrace tailWord_2414403 prefixEnd_2414403 275499829479427193524193 := by
  unfold tailWord_2414403
  simp only [CollatzResearch.WordTrace]
  refine ⟨88060511872037753048871863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58707007914691835365914575 88060511872037753048871863)
  ·
    refine ⟨132090767808056629573307795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88060511872037753048871863 132090767808056629573307795)
    ·
      refine ⟨198136151712084944359961693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132090767808056629573307795 198136151712084944359961693)
      ·
        refine ⟨74301056892031854134985635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 198136151712084944359961693 74301056892031854134985635)
        ·
          refine ⟨111451585338047781202478453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74301056892031854134985635 111451585338047781202478453)
          ·
            refine ⟨10448586125441979487732355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 111451585338047781202478453 10448586125441979487732355)
            ·
              refine ⟨15672879188162969231598533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10448586125441979487732355 15672879188162969231598533)
              ·
                refine ⟨2938664847780556730924725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15672879188162969231598533 2938664847780556730924725)
                ·
                  refine ⟨275499829479427193524193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2938664847780556730924725 275499829479427193524193)
                  ·
                    rfl

theorem cell22_2414403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 1, 4, 5].length) (baseStart_2414403 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2414403 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2414403 prefixEnd_2414403 := by exact prefixLift 2414403
  have htrace : WordTrace (prefixWord ++ tailWord_2414403) baseStart_2414403 baseEnd_2414403 := by
    simpa [prefixWord, tailWord_2414403, baseEnd_2414403] using wordTrace_append hprefix tailTrace_2414403
  have hstable : (prefixWord ++ tailWord_2414403).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2414403).length < 2 ^ (prefixWord ++ tailWord_2414403).sum := by decide
  have hdescent : baseEnd_2414403 < baseStart_2414403 := by decide
  rcases family_descends (prefixWord ++ tailWord_2414403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2414418 : List Nat := [3, 2, 2, 1, 1, 3, 1, 1, 1, 7]
def baseStart_2414418 : Nat := 118140960795 + 2414418 * 2 ^ 59
def prefixEnd_2414418 : Nat := 4983230072969 + 3 ^ 40 * 2414418 * 2
def baseEnd_2414418 : Nat := 826504623244826541447533

theorem tailTrace_2414418 : CollatzResearch.WordTrace tailWord_2414418 prefixEnd_2414418 826504623244826541447533 := by
  unfold tailWord_2414418
  simp only [CollatzResearch.WordTrace]
  refine ⟨22015264741745852652666977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58707372644655607073778605 22015264741745852652666977)
  ·
    refine ⟨16511448556309389489500233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22015264741745852652666977 16511448556309389489500233)
    ·
      refine ⟨12383586417232042117125175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16511448556309389489500233 12383586417232042117125175)
      ·
        refine ⟨18575379625848063175687763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12383586417232042117125175 18575379625848063175687763)
        ·
          refine ⟨27863069438772094763531645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18575379625848063175687763 27863069438772094763531645)
          ·
            refine ⟨10448651039539535536324367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27863069438772094763531645 10448651039539535536324367)
            ·
              refine ⟨15672976559309303304486551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10448651039539535536324367 15672976559309303304486551)
              ·
                refine ⟨23509464838963954956729827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15672976559309303304486551 23509464838963954956729827)
                ·
                  refine ⟨35264197258445932435094741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23509464838963954956729827 35264197258445932435094741)
                  ·
                    refine ⟨826504623244826541447533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 35264197258445932435094741 826504623244826541447533)
                    ·
                      rfl

theorem cell22_2414418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 1, 1, 1, 7].length) (baseStart_2414418 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2414418 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2414418 prefixEnd_2414418 := by exact prefixLift 2414418
  have htrace : WordTrace (prefixWord ++ tailWord_2414418) baseStart_2414418 baseEnd_2414418 := by
    simpa [prefixWord, tailWord_2414418, baseEnd_2414418] using wordTrace_append hprefix tailTrace_2414418
  have hstable : (prefixWord ++ tailWord_2414418).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2414418).length < 2 ^ (prefixWord ++ tailWord_2414418).sum := by decide
  have hdescent : baseEnd_2414418 < baseStart_2414418 := by decide
  rcases family_descends (prefixWord ++ tailWord_2414418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2414420 : List Nat := [2, 4, 1, 1, 3, 1, 2, 3, 5]
def baseStart_2414420 : Nat := 118140960795 + 2414420 * 2 ^ 59
def prefixEnd_2414420 : Nat := 4983230072969 + 3 ^ 40 * 2414420 * 2
def baseEnd_2414420 : Nat := 275501769295233067632509

theorem tailTrace_2414420 : CollatzResearch.WordTrace tailWord_2414420 prefixEnd_2414420 275501769295233067632509 := by
  unfold tailWord_2414420
  simp only [CollatzResearch.WordTrace]
  refine ⟨44030565956488082476120357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58707421275317443301493809 44030565956488082476120357)
  ·
    refine ⟨8255731116841515464272567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 44030565956488082476120357 8255731116841515464272567)
    ·
      refine ⟨12383596675262273196408851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8255731116841515464272567 12383596675262273196408851)
      ·
        refine ⟨18575395012893409794613277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12383596675262273196408851 18575395012893409794613277)
        ·
          refine ⟨6965773129835028672979979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18575395012893409794613277 6965773129835028672979979)
          ·
            refine ⟨10448659694752543009469969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6965773129835028672979979 10448659694752543009469969)
            ·
              refine ⟨7836494771064407257102477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10448659694752543009469969 7836494771064407257102477)
              ·
                refine ⟨2938685539149152721413429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7836494771064407257102477 2938685539149152721413429)
                ·
                  refine ⟨275501769295233067632509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2938685539149152721413429 275501769295233067632509)
                  ·
                    rfl

theorem cell22_2414420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 2, 3, 5].length) (baseStart_2414420 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2414420 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2414420 prefixEnd_2414420 := by exact prefixLift 2414420
  have htrace : WordTrace (prefixWord ++ tailWord_2414420) baseStart_2414420 baseEnd_2414420 := by
    simpa [prefixWord, tailWord_2414420, baseEnd_2414420] using wordTrace_append hprefix tailTrace_2414420
  have hstable : (prefixWord ++ tailWord_2414420).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2414420).length < 2 ^ (prefixWord ++ tailWord_2414420).sum := by decide
  have hdescent : baseEnd_2414420 < baseStart_2414420 := by decide
  rcases family_descends (prefixWord ++ tailWord_2414420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2414433 : List Nat := [1, 2, 3, 1, 1, 1, 3, 3, 3, 4]
def baseStart_2414433 : Nat := 118140960795 + 2414433 * 2 ^ 59
def prefixEnd_2414433 : Nat := 4983230072969 + 3 ^ 40 * 2414433 * 2
def baseEnd_2414433 : Nat := 826509758051371502322487

theorem tailTrace_2414433 : CollatzResearch.WordTrace tailWord_2414433 prefixEnd_2414433 826509758051371502322487 := by
  unfold tailWord_2414433
  simp only [CollatzResearch.WordTrace]
  refine ⟨88061606061929068172463953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58707737374619378781642635 88061606061929068172463953)
  ·
    refine ⟨66046204546446801129347965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88061606061929068172463953 66046204546446801129347965)
    ·
      refine ⟨24767326704917550423505487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 66046204546446801129347965 24767326704917550423505487)
      ·
        refine ⟨37150990057376325635258231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24767326704917550423505487 37150990057376325635258231)
        ·
          refine ⟨55726485086064488452887347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37150990057376325635258231 55726485086064488452887347)
          ·
            refine ⟨83589727629096732679331021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55726485086064488452887347 83589727629096732679331021)
            ·
              refine ⟨31346147860911274754749133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 83589727629096732679331021 31346147860911274754749133)
              ·
                refine ⟨11754805447841728033030925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31346147860911274754749133 11754805447841728033030925)
                ·
                  refine ⟨4408052042940648012386597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11754805447841728033030925 4408052042940648012386597)
                  ·
                    refine ⟨826509758051371502322487, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4408052042940648012386597 826509758051371502322487)
                    ·
                      rfl

theorem cell22_2414433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 3, 3, 3, 4].length) (baseStart_2414433 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2414433 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2414433 prefixEnd_2414433 := by exact prefixLift 2414433
  have htrace : WordTrace (prefixWord ++ tailWord_2414433) baseStart_2414433 baseEnd_2414433 := by
    simpa [prefixWord, tailWord_2414433, baseEnd_2414433] using wordTrace_append hprefix tailTrace_2414433
  have hstable : (prefixWord ++ tailWord_2414433).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2414433).length < 2 ^ (prefixWord ++ tailWord_2414433).sum := by decide
  have hdescent : baseEnd_2414433 < baseStart_2414433 := by decide
  rcases family_descends (prefixWord ++ tailWord_2414433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2414454 : List Nat := [5, 1, 1, 3, 2, 2, 1, 2, 5]
def baseStart_2414454 : Nat := 118140960795 + 2414454 * 2 ^ 59
def prefixEnd_2414454 : Nat := 4983230072969 + 3 ^ 40 * 2414454 * 2
def baseEnd_2414454 : Nat := 275505648926844815849141

theorem tailTrace_2414454 : CollatzResearch.WordTrace tailWord_2414454 prefixEnd_2414454 275505648926844815849141 := by
  unfold tailWord_2414454
  simp only [CollatzResearch.WordTrace]
  refine ⟨5503898249678311797436151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 58708247996568659172652277 5503898249678311797436151)
  ·
    refine ⟨8255847374517467696154227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5503898249678311797436151 8255847374517467696154227)
    ·
      refine ⟨12383771061776201544231341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8255847374517467696154227 12383771061776201544231341)
      ·
        refine ⟨4643914148166075579086753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12383771061776201544231341 4643914148166075579086753)
        ·
          refine ⟨3482935611124556684315065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4643914148166075579086753 3482935611124556684315065)
          ·
            refine ⟨2612201708343417513236299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3482935611124556684315065 2612201708343417513236299)
            ·
              refine ⟨3918302562515126269854449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2612201708343417513236299 3918302562515126269854449)
              ·
                refine ⟨2938726921886344702390837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3918302562515126269854449 2938726921886344702390837)
                ·
                  refine ⟨275505648926844815849141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2938726921886344702390837 275505648926844815849141)
                  ·
                    rfl

theorem cell22_2414454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 2, 1, 2, 5].length) (baseStart_2414454 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2414454 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2414454 prefixEnd_2414454 := by exact prefixLift 2414454
  have htrace : WordTrace (prefixWord ++ tailWord_2414454) baseStart_2414454 baseEnd_2414454 := by
    simpa [prefixWord, tailWord_2414454, baseEnd_2414454] using wordTrace_append hprefix tailTrace_2414454
  have hstable : (prefixWord ++ tailWord_2414454).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2414454).length < 2 ^ (prefixWord ++ tailWord_2414454).sum := by decide
  have hdescent : baseEnd_2414454 < baseStart_2414454 := by decide
  rcases family_descends (prefixWord ++ tailWord_2414454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2414516 : List Nat := [2, 5, 2, 1, 3, 1, 1, 1, 6]
def baseStart_2414516 : Nat := 118140960795 + 2414516 * 2 ^ 59
def prefixEnd_2414516 : Nat := 4983230072969 + 3 ^ 40 * 2414516 * 2
def baseEnd_2414516 : Nat := 275512723549195650832411

theorem tailTrace_2414516 : CollatzResearch.WordTrace tailWord_2414516 prefixEnd_2414516 275512723549195650832411 := by
  unfold tailWord_2414516
  simp only [CollatzResearch.WordTrace]
  refine ⟨44032316660314186673867701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58709755547085582231823601 44032316660314186673867701)
  ·
    refine ⟨4128029686904455000675097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 44032316660314186673867701 4128029686904455000675097)
    ·
      refine ⟨3096022265178341250506323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4128029686904455000675097 3096022265178341250506323)
      ·
        refine ⟨4644033397767511875759485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3096022265178341250506323 4644033397767511875759485)
        ·
          refine ⟨1741512524162816953409807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4644033397767511875759485 1741512524162816953409807)
          ·
            refine ⟨2612268786244225430114711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1741512524162816953409807 2612268786244225430114711)
            ·
              refine ⟨3918403179366338145172067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2612268786244225430114711 3918403179366338145172067)
              ·
                refine ⟨5877604769049507217758101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3918403179366338145172067 5877604769049507217758101)
                ·
                  refine ⟨275512723549195650832411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5877604769049507217758101 275512723549195650832411)
                  ·
                    rfl

theorem cell22_2414516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 3, 1, 1, 1, 6].length) (baseStart_2414516 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2414516 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2414516 prefixEnd_2414516 := by exact prefixLift 2414516
  have htrace : WordTrace (prefixWord ++ tailWord_2414516) baseStart_2414516 baseEnd_2414516 := by
    simpa [prefixWord, tailWord_2414516, baseEnd_2414516] using wordTrace_append hprefix tailTrace_2414516
  have hstable : (prefixWord ++ tailWord_2414516).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2414516).length < 2 ^ (prefixWord ++ tailWord_2414516).sum := by decide
  have hdescent : baseEnd_2414516 < baseStart_2414516 := by decide
  rcases family_descends (prefixWord ++ tailWord_2414516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2414570 : List Nat := [3, 1, 3, 1, 2, 1, 2, 2, 2, 5]
def baseStart_2414570 : Nat := 118140960795 + 2414570 * 2 ^ 59
def prefixEnd_2414570 : Nat := 4983230072969 + 3 ^ 40 * 2414570 * 2
def baseEnd_2414570 : Nat := 826556655951148811647067

theorem tailTrace_2414570 : CollatzResearch.WordTrace tailWord_2414570 prefixEnd_2414570 826556655951148811647067 := by
  unfold tailWord_2414570
  simp only [CollatzResearch.WordTrace]
  refine ⟨22016650715608185142550291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58711068574955160380134109 22016650715608185142550291)
  ·
    refine ⟨33024976073412277713825437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22016650715608185142550291 33024976073412277713825437)
    ·
      refine ⟨12384366027529604142684539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33024976073412277713825437 12384366027529604142684539)
      ·
        refine ⟨18576549041294406214026809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12384366027529604142684539 18576549041294406214026809)
        ·
          refine ⟨13932411780970804660520107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18576549041294406214026809 13932411780970804660520107)
          ·
            refine ⟨20898617671456206990780161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13932411780970804660520107 20898617671456206990780161)
            ·
              refine ⟨15673963253592155243085121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20898617671456206990780161 15673963253592155243085121)
              ·
                refine ⟨11755472440194116432313841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15673963253592155243085121 11755472440194116432313841)
                ·
                  refine ⟨8816604330145587324235381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11755472440194116432313841 8816604330145587324235381)
                  ·
                    refine ⟨826556655951148811647067, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8816604330145587324235381 826556655951148811647067)
                    ·
                      rfl

theorem cell22_2414570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 2, 2, 2, 5].length) (baseStart_2414570 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2414570 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2414570 prefixEnd_2414570 := by exact prefixLift 2414570
  have htrace : WordTrace (prefixWord ++ tailWord_2414570) baseStart_2414570 baseEnd_2414570 := by
    simpa [prefixWord, tailWord_2414570, baseEnd_2414570] using wordTrace_append hprefix tailTrace_2414570
  have hstable : (prefixWord ++ tailWord_2414570).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2414570).length < 2 ^ (prefixWord ++ tailWord_2414570).sum := by decide
  have hdescent : baseEnd_2414570 < baseStart_2414570 := by decide
  rcases family_descends (prefixWord ++ tailWord_2414570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2414583 : List Nat := [1, 1, 3, 1, 1, 1, 1, 1, 12]
def baseStart_2414583 : Nat := 118140960795 + 2414583 * 2 ^ 59
def prefixEnd_2414583 : Nat := 4983230072969 + 3 ^ 40 * 2414583 * 2
def baseEnd_2414583 : Nat := 275520368705607037024009

theorem tailTrace_2414583 : CollatzResearch.WordTrace tailWord_2414583 prefixEnd_2414583 275520368705607037024009 := by
  unfold tailWord_2414583
  simp only [CollatzResearch.WordTrace]
  refine ⟨88067077011385643790424403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58711384674257095860282935 88067077011385643790424403)
  ·
    refine ⟨132100615517078465685636605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88067077011385643790424403 132100615517078465685636605)
    ·
      refine ⟨49537730818904424632113727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 132100615517078465685636605 49537730818904424632113727)
      ·
        refine ⟨74306596228356636948170591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49537730818904424632113727 74306596228356636948170591)
        ·
          refine ⟨111459894342534955422255887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74306596228356636948170591 111459894342534955422255887)
          ·
            refine ⟨167189841513802433133383831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 111459894342534955422255887 167189841513802433133383831)
            ·
              refine ⟨250784762270703649700075747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 167189841513802433133383831 250784762270703649700075747)
              ·
                refine ⟨376177143406055474550113621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 250784762270703649700075747 376177143406055474550113621)
                ·
                  refine ⟨275520368705607037024009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 12 376177143406055474550113621 275520368705607037024009)
                  ·
                    rfl

theorem cell22_2414583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 1, 12].length) (baseStart_2414583 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2414583 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2414583 prefixEnd_2414583 := by exact prefixLift 2414583
  have htrace : WordTrace (prefixWord ++ tailWord_2414583) baseStart_2414583 baseEnd_2414583 := by
    simpa [prefixWord, tailWord_2414583, baseEnd_2414583] using wordTrace_append hprefix tailTrace_2414583
  have hstable : (prefixWord ++ tailWord_2414583).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2414583).length < 2 ^ (prefixWord ++ tailWord_2414583).sum := by decide
  have hdescent : baseEnd_2414583 < baseStart_2414583 := by decide
  rcases family_descends (prefixWord ++ tailWord_2414583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2414585 : List Nat := [1, 2, 1, 3, 1, 4, 1, 2, 3, 4]
def baseStart_2414585 : Nat := 118140960795 + 2414585 * 2 ^ 59
def prefixEnd_2414585 : Nat := 4983230072969 + 3 ^ 40 * 2414585 * 2
def baseEnd_2414585 : Nat := 826561790757693772522021

theorem tailTrace_2414585 : CollatzResearch.WordTrace tailWord_2414585 prefixEnd_2414585 826561790757693772522021 := by
  unfold tailWord_2414585
  simp only [CollatzResearch.WordTrace]
  refine ⟨88067149957378398131997209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58711433304918932087998139 88067149957378398131997209)
  ·
    refine ⟨66050362468033798598997907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88067149957378398131997209 66050362468033798598997907)
    ·
      refine ⟨99075543702050697898496861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66050362468033798598997907 99075543702050697898496861)
      ·
        refine ⟨37153328888269011711936323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 99075543702050697898496861 37153328888269011711936323)
        ·
          refine ⟨55729993332403517567904485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37153328888269011711936323 55729993332403517567904485)
          ·
            refine ⟨10449373749825659543982091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 55729993332403517567904485 10449373749825659543982091)
            ·
              refine ⟨15674060624738489315973137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10449373749825659543982091 15674060624738489315973137)
              ·
                refine ⟨11755545468553866986979853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15674060624738489315973137 11755545468553866986979853)
                ·
                  refine ⟨4408329550707700120117445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11755545468553866986979853 4408329550707700120117445)
                  ·
                    refine ⟨826561790757693772522021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4408329550707700120117445 826561790757693772522021)
                    ·
                      rfl

theorem cell22_2414585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 1, 2, 3, 4].length) (baseStart_2414585 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2414585 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2414585 prefixEnd_2414585 := by exact prefixLift 2414585
  have htrace : WordTrace (prefixWord ++ tailWord_2414585) baseStart_2414585 baseEnd_2414585 := by
    simpa [prefixWord, tailWord_2414585, baseEnd_2414585] using wordTrace_append hprefix tailTrace_2414585
  have hstable : (prefixWord ++ tailWord_2414585).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2414585).length < 2 ^ (prefixWord ++ tailWord_2414585).sum := by decide
  have hdescent : baseEnd_2414585 < baseStart_2414585 := by decide
  rcases family_descends (prefixWord ++ tailWord_2414585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2414600 : List Nat := [2, 1, 3, 2, 1, 2, 3, 2, 6]
def baseStart_2414600 : Nat := 118140960795 + 2414600 * 2 ^ 59
def prefixEnd_2414600 : Nat := 4983230072969 + 3 ^ 40 * 2414600 * 2
def baseEnd_2414600 : Nat := 275522308521412911132325

theorem tailTrace_2414600 : CollatzResearch.WordTrace tailWord_2414600 prefixEnd_2414600 275522308521412911132325 := by
  unfold tailWord_2414600
  simp only [CollatzResearch.WordTrace]
  refine ⟨44033848526162027846896627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58711798034882703795862169 44033848526162027846896627)
  ·
    refine ⟨66050772789243041770344941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44033848526162027846896627 66050772789243041770344941)
    ·
      refine ⟨24769039795966140663879353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 66050772789243041770344941 24769039795966140663879353)
      ·
        refine ⟨18576779846974605497909515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24769039795966140663879353 18576779846974605497909515)
        ·
          refine ⟨27865169770461908246864273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18576779846974605497909515 27865169770461908246864273)
          ·
            refine ⟨20898877327846431185148205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27865169770461908246864273 20898877327846431185148205)
            ·
              refine ⟨7837078997942411694430577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20898877327846431185148205 7837078997942411694430577)
              ·
                refine ⟨5877809248456808770822933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7837078997942411694430577 5877809248456808770822933)
                ·
                  refine ⟨275522308521412911132325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5877809248456808770822933 275522308521412911132325)
                  ·
                    rfl

theorem cell22_2414600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 3, 2, 6].length) (baseStart_2414600 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2414600 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2414600 prefixEnd_2414600 := by exact prefixLift 2414600
  have htrace : WordTrace (prefixWord ++ tailWord_2414600) baseStart_2414600 baseEnd_2414600 := by
    simpa [prefixWord, tailWord_2414600, baseEnd_2414600] using wordTrace_append hprefix tailTrace_2414600
  have hstable : (prefixWord ++ tailWord_2414600).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2414600).length < 2 ^ (prefixWord ++ tailWord_2414600).sum := by decide
  have hdescent : baseEnd_2414600 < baseStart_2414600 := by decide
  rcases family_descends (prefixWord ++ tailWord_2414600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2414634 : List Nat := [3, 1, 4, 1, 2, 1, 2, 4, 4]
def baseStart_2414634 : Nat := 118140960795 + 2414634 * 2 ^ 59
def prefixEnd_2414634 : Nat := 4983230072969 + 3 ^ 40 * 2414634 * 2
def baseEnd_2414634 : Nat := 275526188153024659348957

theorem tailTrace_2414634 : CollatzResearch.WordTrace tailWord_2414634 prefixEnd_2414634 275526188153024659348957 := by
  unfold tailWord_2414634
  simp only [CollatzResearch.WordTrace]
  refine ⟨22017234283550219875132739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58712624756133919667020637 22017234283550219875132739)
  ·
    refine ⟨33025851425325329812699109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22017234283550219875132739 33025851425325329812699109)
    ·
      refine ⟨6192347142248499339881083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 33025851425325329812699109 6192347142248499339881083)
      ·
        refine ⟨9288520713372749009821625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6192347142248499339881083 9288520713372749009821625)
        ·
          refine ⟨6966390535029561757366219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9288520713372749009821625 6966390535029561757366219)
          ·
            refine ⟨10449585802544342636049329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6966390535029561757366219 10449585802544342636049329)
            ·
              refine ⟨7837189351908256977036997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10449585802544342636049329 7837189351908256977036997)
              ·
                refine ⟨1469473003482798183194437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7837189351908256977036997 1469473003482798183194437)
                ·
                  refine ⟨275526188153024659348957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1469473003482798183194437 275526188153024659348957)
                  ·
                    rfl

theorem cell22_2414634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 2, 4, 4].length) (baseStart_2414634 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2414634 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2414634 prefixEnd_2414634 := by exact prefixLift 2414634
  have htrace : WordTrace (prefixWord ++ tailWord_2414634) baseStart_2414634 baseEnd_2414634 := by
    simpa [prefixWord, tailWord_2414634, baseEnd_2414634] using wordTrace_append hprefix tailTrace_2414634
  have hstable : (prefixWord ++ tailWord_2414634).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2414634).length < 2 ^ (prefixWord ++ tailWord_2414634).sum := by decide
  have hdescent : baseEnd_2414634 < baseStart_2414634 := by decide
  rcases family_descends (prefixWord ++ tailWord_2414634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2414649 : List Nat := [1, 2, 1, 5, 3, 2, 1, 1, 1, 5]
def baseStart_2414649 : Nat := 118140960795 + 2414649 * 2 ^ 59
def prefixEnd_2414649 : Nat := 4983230072969 + 3 ^ 40 * 2414649 * 2
def baseEnd_2414649 : Nat := 826583699265618938921825

theorem tailTrace_2414649 : CollatzResearch.WordTrace tailWord_2414649 prefixEnd_2414649 826583699265618938921825 := by
  unfold tailWord_2414649
  simp only [CollatzResearch.WordTrace]
  refine ⟨88069484229146537062327001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58712989486097691374884667 88069484229146537062327001)
  ·
    refine ⟨66052113171859902796745251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88069484229146537062327001 66052113171859902796745251)
    ·
      refine ⟨99078169757789854195117877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66052113171859902796745251 99078169757789854195117877)
      ·
        refine ⟨9288578414792798830792301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 99078169757789854195117877 9288578414792798830792301)
        ·
          refine ⟨3483216905547299561547113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9288578414792798830792301 3483216905547299561547113)
          ·
            refine ⟨2612412679160474671160335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3483216905547299561547113 2612412679160474671160335)
            ·
              refine ⟨3918619018740712006740503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2612412679160474671160335 3918619018740712006740503)
              ·
                refine ⟨5877928528111068010110755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3918619018740712006740503 5877928528111068010110755)
                ·
                  refine ⟨8816892792166602015166133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5877928528111068010110755 8816892792166602015166133)
                  ·
                    refine ⟨826583699265618938921825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8816892792166602015166133 826583699265618938921825)
                    ·
                      rfl

theorem cell22_2414649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 2, 1, 1, 1, 5].length) (baseStart_2414649 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2414649 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2414649 prefixEnd_2414649 := by exact prefixLift 2414649
  have htrace : WordTrace (prefixWord ++ tailWord_2414649) baseStart_2414649 baseEnd_2414649 := by
    simpa [prefixWord, tailWord_2414649, baseEnd_2414649] using wordTrace_append hprefix tailTrace_2414649
  have hstable : (prefixWord ++ tailWord_2414649).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2414649).length < 2 ^ (prefixWord ++ tailWord_2414649).sum := by decide
  have hdescent : baseEnd_2414649 < baseStart_2414649 := by decide
  rcases family_descends (prefixWord ++ tailWord_2414649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2414705 : List Nat := [1, 2, 2, 2, 1, 1, 4, 1, 1, 7]
def baseStart_2414705 : Nat := 118140960795 + 2414705 * 2 ^ 59
def prefixEnd_2414705 : Nat := 4983230072969 + 3 ^ 40 * 2414705 * 2
def baseEnd_2414705 : Nat := 826602869210053459521653

theorem tailTrace_2414705 : CollatzResearch.WordTrace tailWord_2414705 prefixEnd_2414705 826602869210053459521653 := by
  unfold tailWord_2414705
  simp only [CollatzResearch.WordTrace]
  refine ⟨88071526716943658626365569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58714351144629105750910379 88071526716943658626365569)
  ·
    refine ⟨66053645037707743969774177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88071526716943658626365569 66053645037707743969774177)
    ·
      refine ⟨49540233778280807977330633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66053645037707743969774177 49540233778280807977330633)
      ·
        refine ⟨37155175333710605982997975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49540233778280807977330633 37155175333710605982997975)
        ·
          refine ⟨55732763000565908974496963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37155175333710605982997975 55732763000565908974496963)
          ·
            refine ⟨83599144500848863461745445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55732763000565908974496963 83599144500848863461745445)
            ·
              refine ⟨15674839593909161899077271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 83599144500848863461745445 15674839593909161899077271)
              ·
                refine ⟨23512259390863742848615907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15674839593909161899077271 23512259390863742848615907)
                ·
                  refine ⟨35268389086295614272923861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23512259390863742848615907 35268389086295614272923861)
                  ·
                    refine ⟨826602869210053459521653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 35268389086295614272923861 826602869210053459521653)
                    ·
                      rfl

theorem cell22_2414705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 4, 1, 1, 7].length) (baseStart_2414705 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2414705 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2414705 prefixEnd_2414705 := by exact prefixLift 2414705
  have htrace : WordTrace (prefixWord ++ tailWord_2414705) baseStart_2414705 baseEnd_2414705 := by
    simpa [prefixWord, tailWord_2414705, baseEnd_2414705] using wordTrace_append hprefix tailTrace_2414705
  have hstable : (prefixWord ++ tailWord_2414705).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2414705).length < 2 ^ (prefixWord ++ tailWord_2414705).sum := by decide
  have hdescent : baseEnd_2414705 < baseStart_2414705 := by decide
  rcases family_descends (prefixWord ++ tailWord_2414705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2414754 : List Nat := [3, 3, 1, 3, 1, 1, 1, 2, 3, 4]
def baseStart_2414754 : Nat := 118140960795 + 2414754 * 2 ^ 59
def prefixEnd_2414754 : Nat := 4983230072969 + 3 ^ 40 * 2414754 * 2
def baseEnd_2414754 : Nat := 826619642911433665046503

theorem tailTrace_2414754 : CollatzResearch.WordTrace tailWord_2414754 prefixEnd_2414754 826619642911433665046503 := by
  unfold tailWord_2414754
  simp only [CollatzResearch.WordTrace]
  refine ⟨22018328473441534998724829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58715542595844093329932877 22018328473441534998724829)
  ·
    refine ⟨8256873177540575624521811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22018328473441534998724829 8256873177540575624521811)
    ·
      refine ⟨12385309766310863436782717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8256873177540575624521811 12385309766310863436782717)
      ·
        refine ⟨4644491162366573788793519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12385309766310863436782717 4644491162366573788793519)
        ·
          refine ⟨6966736743549860683190279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4644491162366573788793519 6966736743549860683190279)
          ·
            refine ⟨10450105115324791024785419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6966736743549860683190279 10450105115324791024785419)
            ·
              refine ⟨15675157672987186537178129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10450105115324791024785419 15675157672987186537178129)
              ·
                refine ⟨11756368254740389902883597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15675157672987186537178129 11756368254740389902883597)
                ·
                  refine ⟨4408638095527646213581349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11756368254740389902883597 4408638095527646213581349)
                  ·
                    refine ⟨826619642911433665046503, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4408638095527646213581349 826619642911433665046503)
                    ·
                      rfl

theorem cell22_2414754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 1, 2, 3, 4].length) (baseStart_2414754 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2414754 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2414754 prefixEnd_2414754 := by exact prefixLift 2414754
  have htrace : WordTrace (prefixWord ++ tailWord_2414754) baseStart_2414754 baseEnd_2414754 := by
    simpa [prefixWord, tailWord_2414754, baseEnd_2414754] using wordTrace_append hprefix tailTrace_2414754
  have hstable : (prefixWord ++ tailWord_2414754).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2414754).length < 2 ^ (prefixWord ++ tailWord_2414754).sum := by decide
  have hdescent : baseEnd_2414754 < baseStart_2414754 := by decide
  rcases family_descends (prefixWord ++ tailWord_2414754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2414767 : List Nat := [1, 1, 2, 1, 2, 3, 1, 2, 6, 3]
def baseStart_2414767 : Nat := 118140960795 + 2414767 * 2 ^ 59
def prefixEnd_2414767 : Nat := 4983230072969 + 3 ^ 40 * 2414767 * 2
def baseEnd_2414767 : Nat := 826624093077105964471463

theorem tailTrace_2414767 : CollatzResearch.WordTrace tailWord_2414767 prefixEnd_2414767 826624093077105964471463 := by
  unfold tailWord_2414767
  simp only [CollatzResearch.WordTrace]
  refine ⟨88073788042719043215122555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58715858695146028810081703 88073788042719043215122555)
  ·
    refine ⟨132110682064078564822683833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88073788042719043215122555 132110682064078564822683833)
    ·
      refine ⟨99083011548058923617012875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 132110682064078564822683833 99083011548058923617012875)
      ·
        refine ⟨148624517322088385425519313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99083011548058923617012875 148624517322088385425519313)
        ·
          refine ⟨111468387991566289069139485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 148624517322088385425519313 111468387991566289069139485)
          ·
            refine ⟨41800645496837358400927307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 111468387991566289069139485 41800645496837358400927307)
            ·
              refine ⟨62700968245256037601390961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41800645496837358400927307 62700968245256037601390961)
              ·
                refine ⟨47025726183942028201043221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 62700968245256037601390961 47025726183942028201043221)
                ·
                  refine ⟨2204330914872282571923901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 47025726183942028201043221 2204330914872282571923901)
                  ·
                    refine ⟨826624093077105964471463, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2204330914872282571923901 826624093077105964471463)
                    ·
                      rfl

theorem cell22_2414767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 2, 6, 3].length) (baseStart_2414767 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2414767 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2414767 prefixEnd_2414767 := by exact prefixLift 2414767
  have htrace : WordTrace (prefixWord ++ tailWord_2414767) baseStart_2414767 baseEnd_2414767 := by
    simpa [prefixWord, tailWord_2414767, baseEnd_2414767] using wordTrace_append hprefix tailTrace_2414767
  have hstable : (prefixWord ++ tailWord_2414767).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2414767).length < 2 ^ (prefixWord ++ tailWord_2414767).sum := by decide
  have hdescent : baseEnd_2414767 < baseStart_2414767 := by decide
  rcases family_descends (prefixWord ++ tailWord_2414767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2414769 : List Nat := [1, 2, 2, 5, 2, 1, 1, 2, 6]
def baseStart_2414769 : Nat := 118140960795 + 2414769 * 2 ^ 59
def prefixEnd_2414769 : Nat := 4983230072969 + 3 ^ 40 * 2414769 * 2
def baseEnd_2414769 : Nat := 275541592572659541973819

theorem tailTrace_2414769 : CollatzResearch.WordTrace tailWord_2414769 prefixEnd_2414769 275541592572659541973819 := by
  unfold tailWord_2414769
  simp only [CollatzResearch.WordTrace]
  refine ⟨88073860988711797556695361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58715907325807865037796907 88073860988711797556695361)
  ·
    refine ⟨66055395741533848167521521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88073860988711797556695361 66055395741533848167521521)
    ·
      refine ⟨49541546806150386125641141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66055395741533848167521521 49541546806150386125641141)
      ·
        refine ⟨4644520013076598699278857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 49541546806150386125641141 4644520013076598699278857)
        ·
          refine ⟨3483390009807449024459143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4644520013076598699278857 3483390009807449024459143)
          ·
            refine ⟨5225085014711173536688715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3483390009807449024459143 5225085014711173536688715)
            ·
              refine ⟨7837627522066760305033073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5225085014711173536688715 7837627522066760305033073)
              ·
                refine ⟨5878220641550070228774805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7837627522066760305033073 5878220641550070228774805)
                ·
                  refine ⟨275541592572659541973819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5878220641550070228774805 275541592572659541973819)
                  ·
                    rfl

theorem cell22_2414769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 1, 1, 2, 6].length) (baseStart_2414769 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2414769 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2414769 prefixEnd_2414769 := by exact prefixLift 2414769
  have htrace : WordTrace (prefixWord ++ tailWord_2414769) baseStart_2414769 baseEnd_2414769 := by
    simpa [prefixWord, tailWord_2414769, baseEnd_2414769] using wordTrace_append hprefix tailTrace_2414769
  have hstable : (prefixWord ++ tailWord_2414769).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2414769).length < 2 ^ (prefixWord ++ tailWord_2414769).sum := by decide
  have hdescent : baseEnd_2414769 < baseStart_2414769 := by decide
  rcases family_descends (prefixWord ++ tailWord_2414769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2414788 : List Nat := [2, 3, 3, 1, 2, 3, 2, 1, 1, 4]
def baseStart_2414788 : Nat := 118140960795 + 2414788 * 2 ^ 59
def prefixEnd_2414788 : Nat := 4983230072969 + 3 ^ 40 * 2414788 * 2
def baseEnd_2414788 : Nat := 826631281806268909696399

theorem tailTrace_2414788 : CollatzResearch.WordTrace tailWord_2414788 prefixEnd_2414788 826631281806268909696399 := by
  unfold tailWord_2414788
  simp only [CollatzResearch.WordTrace]
  refine ⟨44037276987821481900818509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58716369317095309201091345 44037276987821481900818509)
  ·
    refine ⟨16513978870433055712806941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44037276987821481900818509 16513978870433055712806941)
    ·
      refine ⟨6192742076412395892302603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16513978870433055712806941 6192742076412395892302603)
      ·
        refine ⟨9289113114618593838453905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6192742076412395892302603 9289113114618593838453905)
        ·
          refine ⟨6966834835963945378840429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9289113114618593838453905 6966834835963945378840429)
          ·
            refine ⟨2612563063486479517065161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6966834835963945378840429 2612563063486479517065161)
            ·
              refine ⟨1959422297614859637798871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2612563063486479517065161 1959422297614859637798871)
              ·
                refine ⟨2939133446422289456698307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1959422297614859637798871 2939133446422289456698307)
                ·
                  refine ⟨4408700169633434185047461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2939133446422289456698307 4408700169633434185047461)
                  ·
                    refine ⟨826631281806268909696399, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4408700169633434185047461 826631281806268909696399)
                    ·
                      rfl

theorem cell22_2414788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 3, 2, 1, 1, 4].length) (baseStart_2414788 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2414788 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2414788 prefixEnd_2414788 := by exact prefixLift 2414788
  have htrace : WordTrace (prefixWord ++ tailWord_2414788) baseStart_2414788 baseEnd_2414788 := by
    simpa [prefixWord, tailWord_2414788, baseEnd_2414788] using wordTrace_append hprefix tailTrace_2414788
  have hstable : (prefixWord ++ tailWord_2414788).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2414788).length < 2 ^ (prefixWord ++ tailWord_2414788).sum := by decide
  have hdescent : baseEnd_2414788 < baseStart_2414788 := by decide
  rcases family_descends (prefixWord ++ tailWord_2414788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2414842 : List Nat := [3, 1, 1, 1, 1, 5, 1, 2, 7]
def baseStart_2414842 : Nat := 118140960795 + 2414842 * 2 ^ 59
def prefixEnd_2414842 : Nat := 4983230072969 + 3 ^ 40 * 2414842 * 2
def baseEnd_2414842 : Nat := 275549922369943589615411

theorem tailTrace_2414842 : CollatzResearch.WordTrace tailWord_2414842 prefixEnd_2414842 275549922369943589615411 := by
  unfold tailWord_2414842
  simp only [CollatzResearch.WordTrace]
  refine ⟨22019130879361832756025695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58717682344964887349401853 22019130879361832756025695)
  ·
    refine ⟨33028696319042749134038543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22019130879361832756025695 33028696319042749134038543)
    ·
      refine ⟨49543044478564123701057815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33028696319042749134038543 49543044478564123701057815)
      ·
        refine ⟨74314566717846185551586723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49543044478564123701057815 74314566717846185551586723)
        ·
          refine ⟨111471850076769278327380085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74314566717846185551586723 111471850076769278327380085)
          ·
            refine ⟨10450485944697119843191883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 111471850076769278327380085 10450485944697119843191883)
            ·
              refine ⟨15675728917045679764787825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10450485944697119843191883 15675728917045679764787825)
              ·
                refine ⟨11756796687784259823590869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15675728917045679764787825 11756796687784259823590869)
                ·
                  refine ⟨275549922369943589615411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11756796687784259823590869 275549922369943589615411)
                  ·
                    rfl

theorem cell22_2414842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 1, 2, 7].length) (baseStart_2414842 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2414842 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2414842 prefixEnd_2414842 := by exact prefixLift 2414842
  have htrace : WordTrace (prefixWord ++ tailWord_2414842) baseStart_2414842 baseEnd_2414842 := by
    simpa [prefixWord, tailWord_2414842, baseEnd_2414842] using wordTrace_append hprefix tailTrace_2414842
  have hstable : (prefixWord ++ tailWord_2414842).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2414842).length < 2 ^ (prefixWord ++ tailWord_2414842).sum := by decide
  have hdescent : baseEnd_2414842 < baseStart_2414842 := by decide
  rcases family_descends (prefixWord ++ tailWord_2414842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2414917 : List Nat := [1, 3, 1, 1, 1, 2, 1, 1, 5, 6]
def baseStart_2414917 : Nat := 118140960795 + 2414917 * 2 ^ 59
def prefixEnd_2414917 : Nat := 4983230072969 + 3 ^ 40 * 2414917 * 2
def baseEnd_2414917 : Nat := 826675441142555573221003

theorem tailTrace_2414917 : CollatzResearch.WordTrace tailWord_2414917 prefixEnd_2414917 826675441142555573221003 := by
  unfold tailWord_2414917
  simp only [CollatzResearch.WordTrace]
  refine ⟨88079258992175618833083005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58719505994783745888722003 88079258992175618833083005)
  ·
    refine ⟨33029722122065857062406127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 88079258992175618833083005 33029722122065857062406127)
    ·
      refine ⟨49544583183098785593609191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33029722122065857062406127 49544583183098785593609191)
      ·
        refine ⟨74316874774648178390413787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49544583183098785593609191 74316874774648178390413787)
        ·
          refine ⟨111475312161972267585620681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74316874774648178390413787 111475312161972267585620681)
          ·
            refine ⟨83606484121479200689215511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 111475312161972267585620681 83606484121479200689215511)
            ·
              refine ⟨125409726182218801033823267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 83606484121479200689215511 125409726182218801033823267)
              ·
                refine ⟨188114589273328201550734901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 125409726182218801033823267 188114589273328201550734901)
                ·
                  refine ⟨17635742744374518895381397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 188114589273328201550734901 17635742744374518895381397)
                  ·
                    refine ⟨826675441142555573221003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17635742744374518895381397 826675441142555573221003)
                    ·
                      rfl

theorem cell22_2414917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 1, 5, 6].length) (baseStart_2414917 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2414917 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2414917 prefixEnd_2414917 := by exact prefixLift 2414917
  have htrace : WordTrace (prefixWord ++ tailWord_2414917) baseStart_2414917 baseEnd_2414917 := by
    simpa [prefixWord, tailWord_2414917, baseEnd_2414917] using wordTrace_append hprefix tailTrace_2414917
  have hstable : (prefixWord ++ tailWord_2414917).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2414917).length < 2 ^ (prefixWord ++ tailWord_2414917).sum := by decide
  have hdescent : baseEnd_2414917 < baseStart_2414917 := by decide
  rcases family_descends (prefixWord ++ tailWord_2414917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2414951 : List Nat := [1, 1, 5, 1, 3, 1, 3, 1, 2, 4]
def baseStart_2414951 : Nat := 118140960795 + 2414951 * 2 ^ 59
def prefixEnd_2414951 : Nat := 4983230072969 + 3 ^ 40 * 2414951 * 2
def baseEnd_2414951 : Nat := 826687080037390817870899

theorem tailTrace_2414951 : CollatzResearch.WordTrace tailWord_2414951 prefixEnd_2414951 826687080037390817870899 := by
  unfold tailWord_2414951
  simp only [CollatzResearch.WordTrace]
  refine ⟨88080499074052442639820707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58720332716034961759880471 88080499074052442639820707)
  ·
    refine ⟨132120748611078663959731061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88080499074052442639820707 132120748611078663959731061)
    ·
      refine ⟨12386320182288624746224787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 132120748611078663959731061 12386320182288624746224787)
      ·
        refine ⟨18579480273432937119337181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12386320182288624746224787 18579480273432937119337181)
        ·
          refine ⟨6967305102537351419751443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18579480273432937119337181 6967305102537351419751443)
          ·
            refine ⟨10450957653806027129627165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6967305102537351419751443 10450957653806027129627165)
            ·
              refine ⟨3919109120177260173610187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10450957653806027129627165 3919109120177260173610187)
              ·
                refine ⟨5878663680265890260415281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3919109120177260173610187 5878663680265890260415281)
                ·
                  refine ⟨4408997760199417695311461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5878663680265890260415281 4408997760199417695311461)
                  ·
                    refine ⟨826687080037390817870899, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4408997760199417695311461 826687080037390817870899)
                    ·
                      rfl

theorem cell22_2414951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 3, 1, 2, 4].length) (baseStart_2414951 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2414951 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2414951 prefixEnd_2414951 := by exact prefixLift 2414951
  have htrace : WordTrace (prefixWord ++ tailWord_2414951) baseStart_2414951 baseEnd_2414951 := by
    simpa [prefixWord, tailWord_2414951, baseEnd_2414951] using wordTrace_append hprefix tailTrace_2414951
  have hstable : (prefixWord ++ tailWord_2414951).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2414951).length < 2 ^ (prefixWord ++ tailWord_2414951).sum := by decide
  have hdescent : baseEnd_2414951 < baseStart_2414951 := by decide
  rcases family_descends (prefixWord ++ tailWord_2414951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2415015 : List Nat := [1, 1, 6, 1, 1, 2, 3, 3, 1, 3]
def baseStart_2415015 : Nat := 118140960795 + 2415015 * 2 ^ 59
def prefixEnd_2415015 : Nat := 4983230072969 + 3 ^ 40 * 2415015 * 2
def baseEnd_2415015 : Nat := 826708988545315984270703

theorem tailTrace_2415015 : CollatzResearch.WordTrace tailWord_2415015 prefixEnd_2415015 826708988545315984270703 := by
  unfold tailWord_2415015
  simp only [CollatzResearch.WordTrace]
  refine ⟨88082833345820581570150499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58721888897213721046766999 88082833345820581570150499)
  ·
    refine ⟨132124250018730872355225749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88082833345820581570150499 132124250018730872355225749)
    ·
      refine ⟨6193324219628009641651207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 132124250018730872355225749 6193324219628009641651207)
      ·
        refine ⟨9289986329442014462476811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6193324219628009641651207 9289986329442014462476811)
        ·
          refine ⟨13934979494163021693715217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9289986329442014462476811 13934979494163021693715217)
          ·
            refine ⟨10451234620622266270286413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13934979494163021693715217 10451234620622266270286413)
            ·
              refine ⟨3919212982733349851357405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10451234620622266270286413 3919212982733349851357405)
              ·
                refine ⟨1469704868525006194259027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3919212982733349851357405 1469704868525006194259027)
                ·
                  refine ⟨2204557302787509291388541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1469704868525006194259027 2204557302787509291388541)
                  ·
                    refine ⟨826708988545315984270703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2204557302787509291388541 826708988545315984270703)
                    ·
                      rfl

theorem cell22_2415015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 3, 3, 1, 3].length) (baseStart_2415015 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2415015 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2415015 prefixEnd_2415015 := by exact prefixLift 2415015
  have htrace : WordTrace (prefixWord ++ tailWord_2415015) baseStart_2415015 baseEnd_2415015 := by
    simpa [prefixWord, tailWord_2415015, baseEnd_2415015] using wordTrace_append hprefix tailTrace_2415015
  have hstable : (prefixWord ++ tailWord_2415015).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2415015).length < 2 ^ (prefixWord ++ tailWord_2415015).sum := by decide
  have hdescent : baseEnd_2415015 < baseStart_2415015 := by decide
  rcases family_descends (prefixWord ++ tailWord_2415015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2415071 : List Nat := [1, 1, 2, 3, 3, 3, 1, 2, 1, 5]
def baseStart_2415071 : Nat := 118140960795 + 2415071 * 2 ^ 59
def prefixEnd_2415071 : Nat := 4983230072969 + 3 ^ 40 * 2415071 * 2
def baseEnd_2415071 : Nat := 826728158489750504870531

theorem tailTrace_2415071 : CollatzResearch.WordTrace tailWord_2415071 prefixEnd_2415071 826728158489750504870531 := by
  unfold tailWord_2415071
  simp only [CollatzResearch.WordTrace]
  refine ⟨88084875833617703134189067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58723250555745135422792711 88084875833617703134189067)
  ·
    refine ⟨132127313750426554701283601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88084875833617703134189067 132127313750426554701283601)
    ·
      refine ⟨99095485312819916025962701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 132127313750426554701283601 99095485312819916025962701)
      ·
        refine ⟨37160806992307468509736013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 99095485312819916025962701 37160806992307468509736013)
        ·
          refine ⟨13935302622115300691151005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37160806992307468509736013 13935302622115300691151005)
          ·
            refine ⟨5225738483293237759181627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13935302622115300691151005 5225738483293237759181627)
            ·
              refine ⟨7838607724939856638772441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5225738483293237759181627 7838607724939856638772441)
              ·
                refine ⟨5878955793704892479079331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7838607724939856638772441 5878955793704892479079331)
                ·
                  refine ⟨8818433690557338718618997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5878955793704892479079331 8818433690557338718618997)
                  ·
                    refine ⟨826728158489750504870531, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8818433690557338718618997 826728158489750504870531)
                    ·
                      rfl

theorem cell22_2415071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 3, 1, 2, 1, 5].length) (baseStart_2415071 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2415071 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2415071 prefixEnd_2415071 := by exact prefixLift 2415071
  have htrace : WordTrace (prefixWord ++ tailWord_2415071) baseStart_2415071 baseEnd_2415071 := by
    simpa [prefixWord, tailWord_2415071, baseEnd_2415071] using wordTrace_append hprefix tailTrace_2415071
  have hstable : (prefixWord ++ tailWord_2415071).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2415071).length < 2 ^ (prefixWord ++ tailWord_2415071).sum := by decide
  have hdescent : baseEnd_2415071 < baseStart_2415071 := by decide
  rcases family_descends (prefixWord ++ tailWord_2415071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2415075 : List Nat := [1, 1, 1, 6, 3, 1, 3, 1, 1, 4]
def baseStart_2415075 : Nat := 118140960795 + 2415075 * 2 ^ 59
def prefixEnd_2415075 : Nat := 4983230072969 + 3 ^ 40 * 2415075 * 2
def baseEnd_2415075 : Nat := 826729527771495827770519

theorem tailTrace_2415075 : CollatzResearch.WordTrace tailWord_2415075 prefixEnd_2415075 826729527771495827770519 := by
  unfold tailWord_2415075
  simp only [CollatzResearch.WordTrace]
  refine ⟨88085021725603211817334679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58723347817068807878223119 88085021725603211817334679)
  ·
    refine ⟨132127532588404817726002019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88085021725603211817334679 132127532588404817726002019)
    ·
      refine ⟨198191298882607226589003029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132127532588404817726002019 198191298882607226589003029)
      ·
        refine ⟨9290217135122213746359517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 198191298882607226589003029 9290217135122213746359517)
        ·
          refine ⟨3483831425670830154884819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9290217135122213746359517 3483831425670830154884819)
          ·
            refine ⟨5225747138506245232327229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3483831425670830154884819 5225747138506245232327229)
            ·
              refine ⟨1959655176939841962122711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5225747138506245232327229 1959655176939841962122711)
              ·
                refine ⟨2939482765409762943184067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1959655176939841962122711 2939482765409762943184067)
                ·
                  refine ⟨4409224148114644414776101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2939482765409762943184067 4409224148114644414776101)
                  ·
                    refine ⟨826729527771495827770519, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4409224148114644414776101 826729527771495827770519)
                    ·
                      rfl

theorem cell22_2415075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 1, 3, 1, 1, 4].length) (baseStart_2415075 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2415075 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2415075 prefixEnd_2415075 := by exact prefixLift 2415075
  have htrace : WordTrace (prefixWord ++ tailWord_2415075) baseStart_2415075 baseEnd_2415075 := by
    simpa [prefixWord, tailWord_2415075, baseEnd_2415075] using wordTrace_append hprefix tailTrace_2415075
  have hstable : (prefixWord ++ tailWord_2415075).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2415075).length < 2 ^ (prefixWord ++ tailWord_2415075).sum := by decide
  have hdescent : baseEnd_2415075 < baseStart_2415075 := by decide
  rcases family_descends (prefixWord ++ tailWord_2415075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2415088 : List Nat := [2, 1, 1, 1, 3, 3, 4, 2, 2, 3]
def baseStart_2415088 : Nat := 118140960795 + 2415088 * 2 ^ 59
def prefixEnd_2415088 : Nat := 4983230072969 + 3 ^ 40 * 2415088 * 2
def baseEnd_2415088 : Nat := 826733977937168127195479

theorem tailTrace_2415088 : CollatzResearch.WordTrace tailWord_2415088 prefixEnd_2415088 826733977937168127195479 := by
  unfold tailWord_2415088
  simp only [CollatzResearch.WordTrace]
  refine ⟨44042747937278057518778959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58723663916370743358371945 44042747937278057518778959)
  ·
    refine ⟨66064121905917086278168439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44042747937278057518778959 66064121905917086278168439)
    ·
      refine ⟨99096182858875629417252659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66064121905917086278168439 99096182858875629417252659)
      ·
        refine ⟨148644274288313444125878989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99096182858875629417252659 148644274288313444125878989)
        ·
          refine ⟨55741602858117541547204621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 148644274288313444125878989 55741602858117541547204621)
          ·
            refine ⟨20903101071794078080201733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 55741602858117541547204621 20903101071794078080201733)
            ·
              refine ⟨3919331450961389640037825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20903101071794078080201733 3919331450961389640037825)
              ·
                refine ⟨2939498588221042230028369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3919331450961389640037825 2939498588221042230028369)
                ·
                  refine ⟨2204623941165781672521277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2939498588221042230028369 2204623941165781672521277)
                  ·
                    refine ⟨826733977937168127195479, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2204623941165781672521277 826733977937168127195479)
                    ·
                      rfl

theorem cell22_2415088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 4, 2, 2, 3].length) (baseStart_2415088 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2415088 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2415088 prefixEnd_2415088 := by exact prefixLift 2415088
  have htrace : WordTrace (prefixWord ++ tailWord_2415088) baseStart_2415088 baseEnd_2415088 := by
    simpa [prefixWord, tailWord_2415088, baseEnd_2415088] using wordTrace_append hprefix tailTrace_2415088
  have hstable : (prefixWord ++ tailWord_2415088).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2415088).length < 2 ^ (prefixWord ++ tailWord_2415088).sum := by decide
  have hdescent : baseEnd_2415088 < baseStart_2415088 := by decide
  rcases family_descends (prefixWord ++ tailWord_2415088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2415090 : List Nat := [3, 2, 1, 4, 2, 1, 1, 4, 4]
def baseStart_2415090 : Nat := 118140960795 + 2415090 * 2 ^ 59
def prefixEnd_2415090 : Nat := 4983230072969 + 3 ^ 40 * 2415090 * 2
def baseEnd_2415090 : Nat := 275578220859346929548491

theorem tailTrace_2415090 : CollatzResearch.WordTrace tailWord_2415090 prefixEnd_2415090 275578220859346929548491 := by
  unfold tailWord_2415090
  simp only [CollatzResearch.WordTrace]
  refine ⟨22021392205137217344782681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58723712547032579586087149 22021392205137217344782681)
  ·
    refine ⟨16516044153852913008587011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22021392205137217344782681 16516044153852913008587011)
    ·
      refine ⟨24774066230779369512880517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16516044153852913008587011 24774066230779369512880517)
      ·
        refine ⟨4645137418271131783665097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 24774066230779369512880517 4645137418271131783665097)
        ·
          refine ⟨3483853063703348837748823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4645137418271131783665097 3483853063703348837748823)
          ·
            refine ⟨5225779595555023256623235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3483853063703348837748823 5225779595555023256623235)
            ·
              refine ⟨7838669393332534884934853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5225779595555023256623235 7838669393332534884934853)
              ·
                refine ⟨1469750511249850290925285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7838669393332534884934853 1469750511249850290925285)
                ·
                  refine ⟨275578220859346929548491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1469750511249850290925285 275578220859346929548491)
                  ·
                    rfl

theorem cell22_2415090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 1, 1, 4, 4].length) (baseStart_2415090 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2415090 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2415090 prefixEnd_2415090 := by exact prefixLift 2415090
  have htrace : WordTrace (prefixWord ++ tailWord_2415090) baseStart_2415090 baseEnd_2415090 := by
    simpa [prefixWord, tailWord_2415090, baseEnd_2415090] using wordTrace_append hprefix tailTrace_2415090
  have hstable : (prefixWord ++ tailWord_2415090).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2415090).length < 2 ^ (prefixWord ++ tailWord_2415090).sum := by decide
  have hdescent : baseEnd_2415090 < baseStart_2415090 := by decide
  rcases family_descends (prefixWord ++ tailWord_2415090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2415118 : List Nat := [4, 1, 1, 2, 3, 2, 3, 6]
def baseStart_2415118 : Nat := 118140960795 + 2415118 * 2 ^ 59
def prefixEnd_2415118 : Nat := 4983230072969 + 3 ^ 40 * 2415118 * 2
def baseEnd_2415118 : Nat := 91860471950028672105043

theorem tailTrace_2415118 : CollatzResearch.WordTrace tailWord_2415118 prefixEnd_2415118 91860471950028672105043 := by
  unfold tailWord_2415118
  simp only [CollatzResearch.WordTrace]
  refine ⟨11010823758055928770143751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 58724393376298286774100005 11010823758055928770143751)
  ·
    refine ⟨16516235637083893155215627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11010823758055928770143751 16516235637083893155215627)
    ·
      refine ⟨24774353455625839732823441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16516235637083893155215627 24774353455625839732823441)
      ·
        refine ⟨18580765091719379799617581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24774353455625839732823441 18580765091719379799617581)
        ·
          refine ⟨6967786909394767424856593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18580765091719379799617581 6967786909394767424856593)
          ·
            refine ⟨5225840182046075568642445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6967786909394767424856593 5225840182046075568642445)
            ·
              refine ⟨1959690068267278338240917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5225840182046075568642445 1959690068267278338240917)
              ·
                refine ⟨91860471950028672105043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1959690068267278338240917 91860471950028672105043)
                ·
                  rfl

theorem cell22_2415118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 2, 3, 6].length) (baseStart_2415118 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2415118 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2415118 prefixEnd_2415118 := by exact prefixLift 2415118
  have htrace : WordTrace (prefixWord ++ tailWord_2415118) baseStart_2415118 baseEnd_2415118 := by
    simpa [prefixWord, tailWord_2415118, baseEnd_2415118] using wordTrace_append hprefix tailTrace_2415118
  have hstable : (prefixWord ++ tailWord_2415118).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2415118).length < 2 ^ (prefixWord ++ tailWord_2415118).sum := by decide
  have hdescent : baseEnd_2415118 < baseStart_2415118 := by decide
  rcases family_descends (prefixWord ++ tailWord_2415118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2415129 : List Nat := [1, 2, 1, 2, 1, 1, 2, 3, 9]
def baseStart_2415129 : Nat := 118140960795 + 2415129 * 2 ^ 59
def prefixEnd_2415129 : Nat := 4983230072969 + 3 ^ 40 * 2415129 * 2
def baseEnd_2415129 : Nat := 275582671025019228973451

theorem tailTrace_2415129 : CollatzResearch.WordTrace tailWord_2415129 prefixEnd_2415129 275582671025019228973451 := by
  unfold tailWord_2415129
  simp only [CollatzResearch.WordTrace]
  refine ⟨88086991267407579039800441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58724660844938386026533627 88086991267407579039800441)
  ·
    refine ⟨66065243450555684279850331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88086991267407579039800441 66065243450555684279850331)
    ·
      refine ⟨99097865175833526419775497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66065243450555684279850331 99097865175833526419775497)
      ·
        refine ⟨74323398881875144814831623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 99097865175833526419775497 74323398881875144814831623)
        ·
          refine ⟨111485098322812717222247435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74323398881875144814831623 111485098322812717222247435)
          ·
            refine ⟨167227647484219075833371153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 111485098322812717222247435 167227647484219075833371153)
            ·
              refine ⟨125420735613164306875028365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 167227647484219075833371153 125420735613164306875028365)
              ·
                refine ⟨47032775854936615078135637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 125420735613164306875028365 47032775854936615078135637)
                ·
                  refine ⟨275582671025019228973451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 47032775854936615078135637 275582671025019228973451)
                  ·
                    rfl

theorem cell22_2415129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 3, 9].length) (baseStart_2415129 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2415129 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2415129 prefixEnd_2415129 := by exact prefixLift 2415129
  have htrace : WordTrace (prefixWord ++ tailWord_2415129) baseStart_2415129 baseEnd_2415129 := by
    simpa [prefixWord, tailWord_2415129, baseEnd_2415129] using wordTrace_append hprefix tailTrace_2415129
  have hstable : (prefixWord ++ tailWord_2415129).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2415129).length < 2 ^ (prefixWord ++ tailWord_2415129).sum := by decide
  have hdescent : baseEnd_2415129 < baseStart_2415129 := by decide
  rcases family_descends (prefixWord ++ tailWord_2415129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2415161 : List Nat := [1, 2, 1, 5, 1, 1, 1, 3, 2, 5]
def baseStart_2415161 : Nat := 118140960795 + 2415161 * 2 ^ 59
def prefixEnd_2415161 : Nat := 4983230072969 + 3 ^ 40 * 2415161 * 2
def baseEnd_2415161 : Nat := 826758967329020270120255

theorem tailTrace_2415161 : CollatzResearch.WordTrace tailWord_2415161 prefixEnd_2415161 826758967329020270120255 := by
  unfold tailWord_2415161
  simp only [CollatzResearch.WordTrace]
  refine ⟨88088158403291648504965337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58725438935527765669976891 88088158403291648504965337)
  ·
    refine ⟨66066118802468736378724003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88088158403291648504965337 66066118802468736378724003)
    ·
      refine ⟨99099178203703104568086005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66066118802468736378724003 99099178203703104568086005)
      ·
        refine ⟨9290547956597166053258063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 99099178203703104568086005 9290547956597166053258063)
        ·
          refine ⟨13935821934895749079887095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9290547956597166053258063 13935821934895749079887095)
          ·
            refine ⟨20903732902343623619830643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13935821934895749079887095 20903732902343623619830643)
            ·
              refine ⟨31355599353515435429745965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20903732902343623619830643 31355599353515435429745965)
              ·
                refine ⟨11758349757568288286154737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31355599353515435429745965 11758349757568288286154737)
                ·
                  refine ⟨8818762318176216214616053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11758349757568288286154737 8818762318176216214616053)
                  ·
                    refine ⟨826758967329020270120255, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8818762318176216214616053 826758967329020270120255)
                    ·
                      rfl

theorem cell22_2415161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 1, 3, 2, 5].length) (baseStart_2415161 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2415161 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2415161 prefixEnd_2415161 := by exact prefixLift 2415161
  have htrace : WordTrace (prefixWord ++ tailWord_2415161) baseStart_2415161 baseEnd_2415161 := by
    simpa [prefixWord, tailWord_2415161, baseEnd_2415161] using wordTrace_append hprefix tailTrace_2415161
  have hstable : (prefixWord ++ tailWord_2415161).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2415161).length < 2 ^ (prefixWord ++ tailWord_2415161).sum := by decide
  have hdescent : baseEnd_2415161 < baseStart_2415161 := by decide
  rcases family_descends (prefixWord ++ tailWord_2415161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2415176 : List Nat := [2, 1, 3, 1, 1, 1, 1, 5, 3, 4]
def baseStart_2415176 : Nat := 118140960795 + 2415176 * 2 ^ 59
def prefixEnd_2415176 : Nat := 4983230072969 + 3 ^ 40 * 2415176 * 2
def baseEnd_2415176 : Nat := 826764102135565230995209

theorem tailTrace_2415176 : CollatzResearch.WordTrace tailWord_2415176 prefixEnd_2415176 826764102135565230995209 := by
  unfold tailWord_2415176
  simp only [CollatzResearch.WordTrace]
  refine ⟨44044352749118653033380691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58725803665491537377840921 44044352749118653033380691)
  ·
    refine ⟨66066529123677979550071037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44044352749118653033380691 66066529123677979550071037)
    ·
      refine ⟨24774948421379242331276639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 66066529123677979550071037 24774948421379242331276639)
      ·
        refine ⟨37162422632068863496914959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24774948421379242331276639 37162422632068863496914959)
        ·
          refine ⟨55743633948103295245372439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37162422632068863496914959 55743633948103295245372439)
          ·
            refine ⟨83615450922154942868058659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55743633948103295245372439 83615450922154942868058659)
            ·
              refine ⟨125423176383232414302087989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 83615450922154942868058659 125423176383232414302087989)
              ·
                refine ⟨11758422785928038840820749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 125423176383232414302087989 11758422785928038840820749)
                ·
                  refine ⟨4409408544723014565307781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11758422785928038840820749 4409408544723014565307781)
                  ·
                    refine ⟨826764102135565230995209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4409408544723014565307781 826764102135565230995209)
                    ·
                      rfl

theorem cell22_2415176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 5, 3, 4].length) (baseStart_2415176 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2415176 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2415176 prefixEnd_2415176 := by exact prefixLift 2415176
  have htrace : WordTrace (prefixWord ++ tailWord_2415176) baseStart_2415176 baseEnd_2415176 := by
    simpa [prefixWord, tailWord_2415176, baseEnd_2415176] using wordTrace_append hprefix tailTrace_2415176
  have hstable : (prefixWord ++ tailWord_2415176).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2415176).length < 2 ^ (prefixWord ++ tailWord_2415176).sum := by decide
  have hdescent : baseEnd_2415176 < baseStart_2415176 := by decide
  rcases family_descends (prefixWord ++ tailWord_2415176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2415285 : List Nat := [1, 3, 3, 3, 1, 1, 1, 1, 5, 3]
def baseStart_2415285 : Nat := 118140960795 + 2415285 * 2 ^ 59
def prefixEnd_2415285 : Nat := 4983230072969 + 3 ^ 40 * 2415285 * 2
def baseEnd_2415285 : Nat := 826801415063125280019875

theorem tailTrace_2415285 : CollatzResearch.WordTrace tailWord_2415285 prefixEnd_2415285 826801415063125280019875 := by
  unfold tailWord_2415285
  simp only [CollatzResearch.WordTrace]
  refine ⟨88092681054842417682479309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58728454036561611788319539 88092681054842417682479309)
  ·
    refine ⟨33034755395565906630929741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 88092681054842417682479309 33034755395565906630929741)
    ·
      refine ⟨12388033273337214986598653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33034755395565906630929741 12388033273337214986598653)
      ·
        refine ⟨4645512477501455619974495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12388033273337214986598653 4645512477501455619974495)
        ·
          refine ⟨6968268716252183429961743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4645512477501455619974495 6968268716252183429961743)
          ·
            refine ⟨10452403074378275144942615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6968268716252183429961743 10452403074378275144942615)
            ·
              refine ⟨15678604611567412717413923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10452403074378275144942615 15678604611567412717413923)
              ·
                refine ⟨23517906917351119076120885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15678604611567412717413923 23517906917351119076120885)
                ·
                  refine ⟨2204803773501667413386333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 23517906917351119076120885 2204803773501667413386333)
                  ·
                    refine ⟨826801415063125280019875, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2204803773501667413386333 826801415063125280019875)
                    ·
                      rfl

theorem cell22_2415285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 1, 1, 5, 3].length) (baseStart_2415285 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2415285 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2415285 prefixEnd_2415285 := by exact prefixLift 2415285
  have htrace : WordTrace (prefixWord ++ tailWord_2415285) baseStart_2415285 baseEnd_2415285 := by
    simpa [prefixWord, tailWord_2415285, baseEnd_2415285] using wordTrace_append hprefix tailTrace_2415285
  have hstable : (prefixWord ++ tailWord_2415285).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2415285).length < 2 ^ (prefixWord ++ tailWord_2415285).sum := by decide
  have hdescent : baseEnd_2415285 < baseStart_2415285 := by decide
  rcases family_descends (prefixWord ++ tailWord_2415285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2415343 : List Nat := [1, 1, 2, 1, 5, 2, 2, 2, 6]
def baseStart_2415343 : Nat := 118140960795 + 2415343 * 2 ^ 59
def prefixEnd_2415343 : Nat := 4983230072969 + 3 ^ 40 * 2415343 * 2
def baseEnd_2415343 : Nat := 275607089882810820689899

theorem tailTrace_2415343 : CollatzResearch.WordTrace tailWord_2415343 prefixEnd_2415343 275607089882810820689899 := by
  unfold tailWord_2415343
  simp only [CollatzResearch.WordTrace]
  refine ⟨88094796488632293588090683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58729864325754862392060455 88094796488632293588090683)
  ·
    refine ⟨132142194732948440382136025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88094796488632293588090683 132142194732948440382136025)
    ·
      refine ⟨99106646049711330286602019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 132142194732948440382136025 99106646049711330286602019)
      ·
        refine ⟨148659969074566995429903029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99106646049711330286602019 148659969074566995429903029)
        ·
          refine ⟨13936872100740655821553409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 148659969074566995429903029 13936872100740655821553409)
          ·
            refine ⟨10452654075555491866165057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13936872100740655821553409 10452654075555491866165057)
            ·
              refine ⟨7839490556666618899623793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10452654075555491866165057 7839490556666618899623793)
              ·
                refine ⟨5879617917499964174717845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7839490556666618899623793 5879617917499964174717845)
                ·
                  refine ⟨275607089882810820689899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5879617917499964174717845 275607089882810820689899)
                  ·
                    rfl

theorem cell22_2415343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 2, 2, 6].length) (baseStart_2415343 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2415343 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2415343 prefixEnd_2415343 := by exact prefixLift 2415343
  have htrace : WordTrace (prefixWord ++ tailWord_2415343) baseStart_2415343 baseEnd_2415343 := by
    simpa [prefixWord, tailWord_2415343, baseEnd_2415343] using wordTrace_append hprefix tailTrace_2415343
  have hstable : (prefixWord ++ tailWord_2415343).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2415343).length < 2 ^ (prefixWord ++ tailWord_2415343).sum := by decide
  have hdescent : baseEnd_2415343 < baseStart_2415343 := by decide
  rcases family_descends (prefixWord ++ tailWord_2415343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2415345 : List Nat := [1, 2, 2, 2, 2, 2, 4, 2, 1, 4]
def baseStart_2415345 : Nat := 118140960795 + 2415345 * 2 ^ 59
def prefixEnd_2415345 : Nat := 4983230072969 + 3 ^ 40 * 2415345 * 2
def baseEnd_2415345 : Nat := 826821954289305123519691

theorem tailTrace_2415345 : CollatzResearch.WordTrace tailWord_2415345 prefixEnd_2415345 826821954289305123519691 := by
  unfold tailWord_2415345
  simp only [CollatzResearch.WordTrace]
  refine ⟨88094869434625047929663489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58729912956416698619775659 88094869434625047929663489)
  ·
    refine ⟨66071152075968785947247617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88094869434625047929663489 66071152075968785947247617)
    ·
      refine ⟨49553364056976589460435713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66071152075968785947247617 49553364056976589460435713)
      ·
        refine ⟨37165023042732442095326785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49553364056976589460435713 37165023042732442095326785)
        ·
          refine ⟨27873767282049331571495089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37165023042732442095326785 27873767282049331571495089)
          ·
            refine ⟨20905325461536998678621317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27873767282049331571495089 20905325461536998678621317)
            ·
              refine ⟨3919748524038187252241497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20905325461536998678621317 3919748524038187252241497)
              ·
                refine ⟨2939811393028640439181123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3919748524038187252241497 2939811393028640439181123)
                ·
                  refine ⟨4409717089542960658771685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2939811393028640439181123 4409717089542960658771685)
                  ·
                    refine ⟨826821954289305123519691, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4409717089542960658771685 826821954289305123519691)
                    ·
                      rfl

theorem cell22_2415345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 4, 2, 1, 4].length) (baseStart_2415345 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2415345 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2415345 prefixEnd_2415345 := by exact prefixLift 2415345
  have htrace : WordTrace (prefixWord ++ tailWord_2415345) baseStart_2415345 baseEnd_2415345 := by
    simpa [prefixWord, tailWord_2415345, baseEnd_2415345] using wordTrace_append hprefix tailTrace_2415345
  have hstable : (prefixWord ++ tailWord_2415345).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2415345).length < 2 ^ (prefixWord ++ tailWord_2415345).sum := by decide
  have hdescent : baseEnd_2415345 < baseStart_2415345 := by decide
  rcases family_descends (prefixWord ++ tailWord_2415345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2415362 : List Nat := [3, 4, 1, 1, 1, 2, 2, 3, 1, 4]
def baseStart_2415362 : Nat := 118140960795 + 2415362 * 2 ^ 59
def prefixEnd_2415362 : Nat := 4983230072969 + 3 ^ 40 * 2415362 * 2
def baseEnd_2415362 : Nat := 826827773736722745844639

theorem tailTrace_2415362 : CollatzResearch.WordTrace tailWord_2415362 prefixEnd_2415362 826827773736722745844639 := by
  unfold tailWord_2415362
  simp only [CollatzResearch.WordTrace]
  refine ⟨22023872368890864958258085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58730326317042306555354893 22023872368890864958258085)
  ·
    refine ⟨4129476069167037179673391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 22023872368890864958258085 4129476069167037179673391)
    ·
      refine ⟨6194214103750555769510087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4129476069167037179673391 6194214103750555769510087)
      ·
        refine ⟨9291321155625833654265131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6194214103750555769510087 9291321155625833654265131)
        ·
          refine ⟨13936981733438750481397697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9291321155625833654265131 13936981733438750481397697)
          ·
            refine ⟨10452736300079062861048273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13936981733438750481397697 10452736300079062861048273)
            ·
              refine ⟨7839552225059297145786205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10452736300079062861048273 7839552225059297145786205)
              ·
                refine ⟨2939832084397236429669827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7839552225059297145786205 2939832084397236429669827)
                ·
                  refine ⟨4409748126595854644504741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2939832084397236429669827 4409748126595854644504741)
                  ·
                    refine ⟨826827773736722745844639, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4409748126595854644504741 826827773736722745844639)
                    ·
                      rfl

theorem cell22_2415362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 2, 3, 1, 4].length) (baseStart_2415362 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2415362 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2415362 prefixEnd_2415362 := by exact prefixLift 2415362
  have htrace : WordTrace (prefixWord ++ tailWord_2415362) baseStart_2415362 baseEnd_2415362 := by
    simpa [prefixWord, tailWord_2415362, baseEnd_2415362] using wordTrace_append hprefix tailTrace_2415362
  have hstable : (prefixWord ++ tailWord_2415362).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2415362).length < 2 ^ (prefixWord ++ tailWord_2415362).sum := by decide
  have hdescent : baseEnd_2415362 < baseStart_2415362 := by decide
  rcases family_descends (prefixWord ++ tailWord_2415362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2415375 : List Nat := [1, 1, 2, 1, 1, 1, 6, 4, 2, 3]
def baseStart_2415375 : Nat := 118140960795 + 2415375 * 2 ^ 59
def prefixEnd_2415375 : Nat := 4983230072969 + 3 ^ 40 * 2415375 * 2
def baseEnd_2415375 : Nat := 826832223902395045269599

theorem tailTrace_2415375 : CollatzResearch.WordTrace tailWord_2415375 prefixEnd_2415375 826832223902395045269599 := by
  unfold tailWord_2415375
  simp only [CollatzResearch.WordTrace]
  refine ⟨88095963624516363053255579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58730642416344242035503719 88095963624516363053255579)
  ·
    refine ⟨132143945436774544579883369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88095963624516363053255579 132143945436774544579883369)
    ·
      refine ⟨99107959077580908434912527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 132143945436774544579883369 99107959077580908434912527)
      ·
        refine ⟨148661938616371362652368791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99107959077580908434912527 148661938616371362652368791)
        ·
          refine ⟨222992907924557043978553187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 148661938616371362652368791 222992907924557043978553187)
          ·
            refine ⟨334489361886835565967829781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 222992907924557043978553187 334489361886835565967829781)
            ·
              refine ⟨15679188838445417154742021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 334489361886835565967829781 15679188838445417154742021)
              ·
                refine ⟨2939847907208515716514129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15679188838445417154742021 2939847907208515716514129)
                ·
                  refine ⟨2204885930406386787385597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2939847907208515716514129 2204885930406386787385597)
                  ·
                    refine ⟨826832223902395045269599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2204885930406386787385597 826832223902395045269599)
                    ·
                      rfl

theorem cell22_2415375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 6, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 6, 4, 2, 3].length) (baseStart_2415375 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2415375 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2415375 prefixEnd_2415375 := by exact prefixLift 2415375
  have htrace : WordTrace (prefixWord ++ tailWord_2415375) baseStart_2415375 baseEnd_2415375 := by
    simpa [prefixWord, tailWord_2415375, baseEnd_2415375] using wordTrace_append hprefix tailTrace_2415375
  have hstable : (prefixWord ++ tailWord_2415375).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2415375).length < 2 ^ (prefixWord ++ tailWord_2415375).sum := by decide
  have hdescent : baseEnd_2415375 < baseStart_2415375 := by decide
  rcases family_descends (prefixWord ++ tailWord_2415375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2415388 : List Nat := [2, 2, 3, 1, 1, 3, 1, 9]
def baseStart_2415388 : Nat := 118140960795 + 2415388 * 2 ^ 59
def prefixEnd_2415388 : Nat := 4983230072969 + 3 ^ 40 * 2415388 * 2
def baseEnd_2415388 : Nat := 91870741563118593854951

theorem tailTrace_2415388 : CollatzResearch.WordTrace tailWord_2415388 prefixEnd_2415388 91870741563118593854951 := by
  unfold tailWord_2415388
  simp only [CollatzResearch.WordTrace]
  refine ⟨44048218886734633136739409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58730958515646177515652545 44048218886734633136739409)
  ·
    refine ⟨33036164165050974852554557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44048218886734633136739409 33036164165050974852554557)
    ·
      refine ⟨12388561561894115569707959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33036164165050974852554557 12388561561894115569707959)
      ·
        refine ⟨18582842342841173354561939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12388561561894115569707959 18582842342841173354561939)
        ·
          refine ⟨27874263514261760031842909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18582842342841173354561939 27874263514261760031842909)
          ·
            refine ⟨10452848817848160011941091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27874263514261760031842909 10452848817848160011941091)
            ·
              refine ⟨15679273226772240017911637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10452848817848160011941091 15679273226772240017911637)
              ·
                refine ⟨91870741563118593854951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 15679273226772240017911637 91870741563118593854951)
                ·
                  rfl

theorem cell22_2415388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 1, 9].length) (baseStart_2415388 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2415388 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2415388 prefixEnd_2415388 := by exact prefixLift 2415388
  have htrace : WordTrace (prefixWord ++ tailWord_2415388) baseStart_2415388 baseEnd_2415388 := by
    simpa [prefixWord, tailWord_2415388, baseEnd_2415388] using wordTrace_append hprefix tailTrace_2415388
  have hstable : (prefixWord ++ tailWord_2415388).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2415388).length < 2 ^ (prefixWord ++ tailWord_2415388).sum := by decide
  have hdescent : baseEnd_2415388 < baseStart_2415388 := by decide
  rcases family_descends (prefixWord ++ tailWord_2415388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2415392 : List Nat := [2, 1, 1, 5, 1, 3, 1, 3, 2, 3]
def baseStart_2415392 : Nat := 118140960795 + 2415392 * 2 ^ 59
def prefixEnd_2415392 : Nat := 4983230072969 + 3 ^ 40 * 2415392 * 2
def baseEnd_2415392 : Nat := 826838043349812667594547

theorem tailTrace_2415392 : CollatzResearch.WordTrace tailWord_2415392 prefixEnd_2415392 826838043349812667594547 := by
  unfold tailWord_2415392
  simp only [CollatzResearch.WordTrace]
  refine ⟨44048291832727387478312215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58731055776969849971082953 44048291832727387478312215)
  ·
    refine ⟨66072437749091081217468323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44048291832727387478312215 66072437749091081217468323)
    ·
      refine ⟨99108656623636621826202485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66072437749091081217468323 99108656623636621826202485)
      ·
        refine ⟨9291436558465933296206483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 99108656623636621826202485 9291436558465933296206483)
        ·
          refine ⟨13937154837698899944309725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9291436558465933296206483 13937154837698899944309725)
          ·
            refine ⟨5226433064137087479116147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13937154837698899944309725 5226433064137087479116147)
            ·
              refine ⟨7839649596205631218674221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5226433064137087479116147 7839649596205631218674221)
              ·
                refine ⟨2939868598577111707002833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7839649596205631218674221 2939868598577111707002833)
                ·
                  refine ⟨2204901448932833780252125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2939868598577111707002833 2204901448932833780252125)
                  ·
                    refine ⟨826838043349812667594547, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2204901448932833780252125 826838043349812667594547)
                    ·
                      rfl

theorem cell22_2415392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 3, 1, 3, 2, 3].length) (baseStart_2415392 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2415392 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2415392 prefixEnd_2415392 := by exact prefixLift 2415392
  have htrace : WordTrace (prefixWord ++ tailWord_2415392) baseStart_2415392 baseEnd_2415392 := by
    simpa [prefixWord, tailWord_2415392, baseEnd_2415392] using wordTrace_append hprefix tailTrace_2415392
  have hstable : (prefixWord ++ tailWord_2415392).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2415392).length < 2 ^ (prefixWord ++ tailWord_2415392).sum := by decide
  have hdescent : baseEnd_2415392 < baseStart_2415392 := by decide
  rcases family_descends (prefixWord ++ tailWord_2415392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2415428 : List Nat := [2, 3, 4, 2, 1, 2, 2, 2, 4]
def baseStart_2415428 : Nat := 118140960795 + 2415428 * 2 ^ 59
def prefixEnd_2415428 : Nat := 4983230072969 + 3 ^ 40 * 2415428 * 2
def baseEnd_2415428 : Nat := 275616788961840191231479

theorem tailTrace_2415428 : CollatzResearch.WordTrace tailWord_2415428 prefixEnd_2415428 275616788961840191231479 := by
  unfold tailWord_2415428
  simp only [CollatzResearch.WordTrace]
  refine ⟨44048948346662176552467469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58731931128882902069956625 44048948346662176552467469)
  ·
    refine ⟨16518355629998316207175301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44048948346662176552467469 16518355629998316207175301)
    ·
      refine ⟨3097191680624684288845369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16518355629998316207175301 3097191680624684288845369)
      ·
        refine ⟨2322893760468513216634027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3097191680624684288845369 2322893760468513216634027)
        ·
          refine ⟨3484340640702769824951041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2322893760468513216634027 3484340640702769824951041)
          ·
            refine ⟨2613255480527077368713281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3484340640702769824951041 2613255480527077368713281)
            ·
              refine ⟨1959941610395308026534961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2613255480527077368713281 1959941610395308026534961)
              ·
                refine ⟨1469956207796481019901221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1959941610395308026534961 1469956207796481019901221)
                ·
                  refine ⟨275616788961840191231479, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1469956207796481019901221 275616788961840191231479)
                  ·
                    rfl

theorem cell22_2415428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 2, 2, 2, 4].length) (baseStart_2415428 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2415428 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2415428 prefixEnd_2415428 := by exact prefixLift 2415428
  have htrace : WordTrace (prefixWord ++ tailWord_2415428) baseStart_2415428 baseEnd_2415428 := by
    simpa [prefixWord, tailWord_2415428, baseEnd_2415428] using wordTrace_append hprefix tailTrace_2415428
  have hstable : (prefixWord ++ tailWord_2415428).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2415428).length < 2 ^ (prefixWord ++ tailWord_2415428).sum := by decide
  have hdescent : baseEnd_2415428 < baseStart_2415428 := by decide
  rcases family_descends (prefixWord ++ tailWord_2415428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2415450 : List Nat := [3, 1, 1, 2, 1, 4, 2, 3, 5]
def baseStart_2415450 : Nat := 118140960795 + 2415450 * 2 ^ 59
def prefixEnd_2415450 : Nat := 4983230072969 + 3 ^ 40 * 2415450 * 2
def baseEnd_2415450 : Nat := 275619299311706616548123

theorem tailTrace_2415450 : CollatzResearch.WordTrace tailWord_2415450 prefixEnd_2415450 275619299311706616548123 := by
  unfold tailWord_2415450
  simp only [CollatzResearch.WordTrace]
  refine ⟨22024674774811162715558951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58732466066163100574823869 22024674774811162715558951)
  ·
    refine ⟨33037012162216744073338427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22024674774811162715558951 33037012162216744073338427)
    ·
      refine ⟨49555518243325116110007641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33037012162216744073338427 49555518243325116110007641)
      ·
        refine ⟨37166638682493837082505731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49555518243325116110007641 37166638682493837082505731)
        ·
          refine ⟨55749958023740755623758597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37166638682493837082505731 55749958023740755623758597)
          ·
            refine ⟨10453117129451391679454737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 55749958023740755623758597 10453117129451391679454737)
            ·
              refine ⟨7839837847088543759591053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10453117129451391679454737 7839837847088543759591053)
              ·
                refine ⟨2939939192658203909846645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7839837847088543759591053 2939939192658203909846645)
                ·
                  refine ⟨275619299311706616548123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2939939192658203909846645 275619299311706616548123)
                  ·
                    rfl

theorem cell22_2415450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 2, 3, 5].length) (baseStart_2415450 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2415450 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2415450 prefixEnd_2415450 := by exact prefixLift 2415450
  have htrace : WordTrace (prefixWord ++ tailWord_2415450) baseStart_2415450 baseEnd_2415450 := by
    simpa [prefixWord, tailWord_2415450, baseEnd_2415450] using wordTrace_append hprefix tailTrace_2415450
  have hstable : (prefixWord ++ tailWord_2415450).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2415450).length < 2 ^ (prefixWord ++ tailWord_2415450).sum := by decide
  have hdescent : baseEnd_2415450 < baseStart_2415450 := by decide
  rcases family_descends (prefixWord ++ tailWord_2415450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2415495 : List Nat := [1, 1, 4, 2, 3, 1, 1, 3, 6]
def baseStart_2415495 : Nat := 118140960795 + 2415495 * 2 ^ 59
def prefixEnd_2415495 : Nat := 4983230072969 + 3 ^ 40 * 2415495 * 2
def baseEnd_2415495 : Nat := 275624434118251577423077

theorem tailTrace_2415495 : CollatzResearch.WordTrace tailWord_2415495 prefixEnd_2415495 275624434118251577423077 := by
  unfold tailWord_2415495
  simp only [CollatzResearch.WordTrace]
  refine ⟨88100340384081623547623939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58733560256054415698415959 88100340384081623547623939)
  ·
    refine ⟨132150510576122435321435909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88100340384081623547623939 132150510576122435321435909)
    ·
      refine ⟨24778220733022956622769233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 132150510576122435321435909 24778220733022956622769233)
      ·
        refine ⟨18583665549767217467076925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24778220733022956622769233 18583665549767217467076925)
        ·
          refine ⟨6968874581162706550153847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18583665549767217467076925 6968874581162706550153847)
          ·
            refine ⟨10453311871744059825230771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6968874581162706550153847 10453311871744059825230771)
            ·
              refine ⟨15679967807616089737846157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10453311871744059825230771 15679967807616089737846157)
              ·
                refine ⟨5879987927856033651692309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15679967807616089737846157 5879987927856033651692309)
                ·
                  refine ⟨275624434118251577423077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5879987927856033651692309 275624434118251577423077)
                  ·
                    rfl

theorem cell22_2415495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 1, 3, 6].length) (baseStart_2415495 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2415495 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2415495 prefixEnd_2415495 := by exact prefixLift 2415495
  have htrace : WordTrace (prefixWord ++ tailWord_2415495) baseStart_2415495 baseEnd_2415495 := by
    simpa [prefixWord, tailWord_2415495, baseEnd_2415495] using wordTrace_append hprefix tailTrace_2415495
  have hstable : (prefixWord ++ tailWord_2415495).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2415495).length < 2 ^ (prefixWord ++ tailWord_2415495).sum := by decide
  have hdescent : baseEnd_2415495 < baseStart_2415495 := by decide
  rcases family_descends (prefixWord ++ tailWord_2415495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2415514 : List Nat := [3, 1, 1, 4, 3, 1, 2, 2, 1, 4]
def baseStart_2415514 : Nat := 118140960795 + 2415514 * 2 ^ 59
def prefixEnd_2415514 : Nat := 4983230072969 + 3 ^ 40 * 2415514 * 2
def baseEnd_2415514 : Nat := 826879806443045016044173

theorem tailTrace_2415514 : CollatzResearch.WordTrace tailWord_2415514 prefixEnd_2415514 826879806443045016044173 := by
  unfold tailWord_2415514
  simp only [CollatzResearch.WordTrace]
  refine ⟨22025258342753197448141399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58734022247341859861710397 22025258342753197448141399)
  ·
    refine ⟨33037887514129796172212099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22025258342753197448141399 33037887514129796172212099)
    ·
      refine ⟨49556831271194694258318149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33037887514129796172212099 49556831271194694258318149)
      ·
        refine ⟨9291905863349005173434653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 49556831271194694258318149 9291905863349005173434653)
        ·
          refine ⟨3484464698755876940037995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9291905863349005173434653 3484464698755876940037995)
          ·
            refine ⟨5226697048133815410056993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3484464698755876940037995 5226697048133815410056993)
            ·
              refine ⟨3920022786100361557542745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5226697048133815410056993 3920022786100361557542745)
              ·
                refine ⟨2940017089575271168157059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3920022786100361557542745 2940017089575271168157059)
                ·
                  refine ⟨4410025634362906752235589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2940017089575271168157059 4410025634362906752235589)
                  ·
                    refine ⟨826879806443045016044173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4410025634362906752235589 826879806443045016044173)
                    ·
                      rfl

theorem cell22_2415514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 1, 2, 2, 1, 4].length) (baseStart_2415514 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2415514 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2415514 prefixEnd_2415514 := by exact prefixLift 2415514
  have htrace : WordTrace (prefixWord ++ tailWord_2415514) baseStart_2415514 baseEnd_2415514 := by
    simpa [prefixWord, tailWord_2415514, baseEnd_2415514] using wordTrace_append hprefix tailTrace_2415514
  have hstable : (prefixWord ++ tailWord_2415514).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2415514).length < 2 ^ (prefixWord ++ tailWord_2415514).sum := by decide
  have hdescent : baseEnd_2415514 < baseStart_2415514 := by decide
  rcases family_descends (prefixWord ++ tailWord_2415514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2415565 : List Nat := [1, 6, 3, 1, 1, 2, 1, 2, 1, 4]
def baseStart_2415565 : Nat := 118140960795 + 2415565 * 2 ^ 59
def prefixEnd_2415565 : Nat := 4983230072969 + 3 ^ 40 * 2415565 * 2
def baseEnd_2415565 : Nat := 826897264785297883019017

theorem tailTrace_2415565 : CollatzResearch.WordTrace tailWord_2415565 prefixEnd_2415565 826897264785297883019017 := by
  unfold tailWord_2415565
  simp only [CollatzResearch.WordTrace]
  refine ⟨88102893493828025502672149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58735262329218683668448099 88102893493828025502672149)
  ·
    refine ⟨4129823132523188695437757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 88102893493828025502672149 4129823132523188695437757)
    ·
      refine ⟨1548683674696195760789159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4129823132523188695437757 1548683674696195760789159)
      ·
        refine ⟨2323025512044293641183739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1548683674696195760789159 2323025512044293641183739)
        ·
          refine ⟨3484538268066440461775609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2323025512044293641183739 3484538268066440461775609)
          ·
            refine ⟨2613403701049830346331707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3484538268066440461775609 2613403701049830346331707)
            ·
              refine ⟨3920105551574745519497561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2613403701049830346331707 3920105551574745519497561)
              ·
                refine ⟨2940079163681059139623171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3920105551574745519497561 2940079163681059139623171)
                ·
                  refine ⟨4410118745521588709434757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2940079163681059139623171 4410118745521588709434757)
                  ·
                    refine ⟨826897264785297883019017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4410118745521588709434757 826897264785297883019017)
                    ·
                      rfl

theorem cell22_2415565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 2, 1, 2, 1, 4].length) (baseStart_2415565 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2415565 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2415565 prefixEnd_2415565 := by exact prefixLift 2415565
  have htrace : WordTrace (prefixWord ++ tailWord_2415565) baseStart_2415565 baseEnd_2415565 := by
    simpa [prefixWord, tailWord_2415565, baseEnd_2415565] using wordTrace_append hprefix tailTrace_2415565
  have hstable : (prefixWord ++ tailWord_2415565).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2415565).length < 2 ^ (prefixWord ++ tailWord_2415565).sum := by decide
  have hdescent : baseEnd_2415565 < baseStart_2415565 := by decide
  rcases family_descends (prefixWord ++ tailWord_2415565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2415600 : List Nat := [2, 1, 1, 1, 3, 2, 1, 4, 2, 5]
def baseStart_2415600 : Nat := 118140960795 + 2415600 * 2 ^ 59
def prefixEnd_2415600 : Nat := 4983230072969 + 3 ^ 40 * 2415600 * 2
def baseEnd_2415600 : Nat := 826909246000569458393909

theorem tailTrace_2415600 : CollatzResearch.WordTrace tailWord_2415600 prefixEnd_2415600 826909246000569458393909 := by
  unfold tailWord_2415600
  simp only [CollatzResearch.WordTrace]
  refine ⟨44052085024350613240098127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58736113365800817653464169 44052085024350613240098127)
  ·
    refine ⟨66078127536525919860147191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44052085024350613240098127 66078127536525919860147191)
    ·
      refine ⟨99117191304788879790220787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66078127536525919860147191 99117191304788879790220787)
      ·
        refine ⟨148675786957183319685331181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99117191304788879790220787 148675786957183319685331181)
        ·
          refine ⟨55753420108943744881999193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 148675786957183319685331181 55753420108943744881999193)
          ·
            refine ⟨41815065081707808661499395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55753420108943744881999193 41815065081707808661499395)
            ·
              refine ⟨62722597622561712992249093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41815065081707808661499395 62722597622561712992249093)
              ·
                refine ⟨11760487054230321186046705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 62722597622561712992249093 11760487054230321186046705)
                ·
                  refine ⟨8820365290672740889535029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11760487054230321186046705 8820365290672740889535029)
                  ·
                    refine ⟨826909246000569458393909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8820365290672740889535029 826909246000569458393909)
                    ·
                      rfl

theorem cell22_2415600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 4, 2, 5].length) (baseStart_2415600 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2415600 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2415600 prefixEnd_2415600 := by exact prefixLift 2415600
  have htrace : WordTrace (prefixWord ++ tailWord_2415600) baseStart_2415600 baseEnd_2415600 := by
    simpa [prefixWord, tailWord_2415600, baseEnd_2415600] using wordTrace_append hprefix tailTrace_2415600
  have hstable : (prefixWord ++ tailWord_2415600).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2415600).length < 2 ^ (prefixWord ++ tailWord_2415600).sum := by decide
  have hdescent : baseEnd_2415600 < baseStart_2415600 := by decide
  rcases family_descends (prefixWord ++ tailWord_2415600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2415617 : List Nat := [1, 2, 4, 1, 2, 3, 1, 1, 2, 5]
def baseStart_2415617 : Nat := 118140960795 + 2415617 * 2 ^ 59
def prefixEnd_2415617 : Nat := 4983230072969 + 3 ^ 40 * 2415617 * 2
def baseEnd_2415617 : Nat := 826915065447987080718857

theorem tailTrace_2415617 : CollatzResearch.WordTrace tailWord_2415617 prefixEnd_2415617 826915065447987080718857 := by
  unfold tailWord_2415617
  simp only [CollatzResearch.WordTrace]
  refine ⟨88104790089639638383565105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58736526726426425589043403 88104790089639638383565105)
  ·
    refine ⟨66078592567229728787673829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88104790089639638383565105 66078592567229728787673829)
    ·
      refine ⟨12389736106355574147688843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 66078592567229728787673829 12389736106355574147688843)
      ·
        refine ⟨18584604159533361221533265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12389736106355574147688843 18584604159533361221533265)
        ·
          refine ⟨13938453119650020916149949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18584604159533361221533265 13938453119650020916149949)
          ·
            refine ⟨5226919919868757843556231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13938453119650020916149949 5226919919868757843556231)
            ·
              refine ⟨7840379879803136765334347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5226919919868757843556231 7840379879803136765334347)
              ·
                refine ⟨11760569819704705148001521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7840379879803136765334347 11760569819704705148001521)
                ·
                  refine ⟨8820427364778528861001141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11760569819704705148001521 8820427364778528861001141)
                  ·
                    refine ⟨826915065447987080718857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8820427364778528861001141 826915065447987080718857)
                    ·
                      rfl

theorem cell22_2415617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 3, 1, 1, 2, 5].length) (baseStart_2415617 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2415617 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2415617 prefixEnd_2415617 := by exact prefixLift 2415617
  have htrace : WordTrace (prefixWord ++ tailWord_2415617) baseStart_2415617 baseEnd_2415617 := by
    simpa [prefixWord, tailWord_2415617, baseEnd_2415617] using wordTrace_append hprefix tailTrace_2415617
  have hstable : (prefixWord ++ tailWord_2415617).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2415617).length < 2 ^ (prefixWord ++ tailWord_2415617).sum := by decide
  have hdescent : baseEnd_2415617 < baseStart_2415617 := by decide
  rcases family_descends (prefixWord ++ tailWord_2415617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2415649 : List Nat := [1, 2, 3, 2, 3, 2, 1, 3, 1, 4]
def baseStart_2415649 : Nat := 118140960795 + 2415649 * 2 ^ 59
def prefixEnd_2415649 : Nat := 4983230072969 + 3 ^ 40 * 2415649 * 2
def baseEnd_2415649 : Nat := 826926019701949663918759

theorem tailTrace_2415649 : CollatzResearch.WordTrace tailWord_2415649 prefixEnd_2415649 826926019701949663918759 := by
  unfold tailWord_2415649
  simp only [CollatzResearch.WordTrace]
  refine ⟨88105957225523707848730001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58737304817015805232486667 88105957225523707848730001)
  ·
    refine ⟨66079467919142780886547501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88105957225523707848730001 66079467919142780886547501)
    ·
      refine ⟨24779800469678542832455313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 66079467919142780886547501 24779800469678542832455313)
      ·
        refine ⟨18584850352258907124341485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24779800469678542832455313 18584850352258907124341485)
        ·
          refine ⟨6969318882097090171628057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18584850352258907124341485 6969318882097090171628057)
          ·
            refine ⟨5226989161572817628721043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6969318882097090171628057 5226989161572817628721043)
            ·
              refine ⟨7840483742359226443081565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5226989161572817628721043 7840483742359226443081565)
              ·
                refine ⟨2940181403384709916155587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7840483742359226443081565 2940181403384709916155587)
                ·
                  refine ⟨4410272105077064874233381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2940181403384709916155587 4410272105077064874233381)
                  ·
                    refine ⟨826926019701949663918759, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4410272105077064874233381 826926019701949663918759)
                    ·
                      rfl

theorem cell22_2415649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 2, 1, 3, 1, 4].length) (baseStart_2415649 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2415649 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2415649 prefixEnd_2415649 := by exact prefixLift 2415649
  have htrace : WordTrace (prefixWord ++ tailWord_2415649) baseStart_2415649 baseEnd_2415649 := by
    simpa [prefixWord, tailWord_2415649, baseEnd_2415649] using wordTrace_append hprefix tailTrace_2415649
  have hstable : (prefixWord ++ tailWord_2415649).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2415649).length < 2 ^ (prefixWord ++ tailWord_2415649).sum := by decide
  have hdescent : baseEnd_2415649 < baseStart_2415649 := by decide
  rcases family_descends (prefixWord ++ tailWord_2415649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2415677 : List Nat := [1, 4, 1, 3, 1, 2, 1, 2, 1, 6]
def baseStart_2415677 : Nat := 118140960795 + 2415677 * 2 ^ 59
def prefixEnd_2415677 : Nat := 4983230072969 + 3 ^ 40 * 2415677 * 2
def baseEnd_2415677 : Nat := 826935604674166924218673

theorem tailTrace_2415677 : CollatzResearch.WordTrace tailWord_2415677 prefixEnd_2415677 826935604674166924218673 := by
  unfold tailWord_2415677
  simp only [CollatzResearch.WordTrace]
  refine ⟨88106978469422268630749285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58737985646281512420499523 88106978469422268630749285)
  ·
    refine ⟨16520058463016675368265491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 88106978469422268630749285 16520058463016675368265491)
    ·
      refine ⟨24780087694525013052398237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16520058463016675368265491 24780087694525013052398237)
      ·
        refine ⟨9292532885446879894649339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24780087694525013052398237 9292532885446879894649339)
        ·
          refine ⟨13938799328170319841974009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9292532885446879894649339 13938799328170319841974009)
          ·
            refine ⟨10454099496127739881480507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13938799328170319841974009 10454099496127739881480507)
            ·
              refine ⟨15681149244191609822220761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10454099496127739881480507 15681149244191609822220761)
              ·
                refine ⟨11760861933143707366665571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15681149244191609822220761 11760861933143707366665571)
                ·
                  refine ⟨17641292899715561049998357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11760861933143707366665571 17641292899715561049998357)
                  ·
                    refine ⟨826935604674166924218673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17641292899715561049998357 826935604674166924218673)
                    ·
                      rfl

theorem cell22_2415677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 1, 2, 1, 6].length) (baseStart_2415677 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2415677 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2415677 prefixEnd_2415677 := by exact prefixLift 2415677
  have htrace : WordTrace (prefixWord ++ tailWord_2415677) baseStart_2415677 baseEnd_2415677 := by
    simpa [prefixWord, tailWord_2415677, baseEnd_2415677] using wordTrace_append hprefix tailTrace_2415677
  have hstable : (prefixWord ++ tailWord_2415677).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2415677).length < 2 ^ (prefixWord ++ tailWord_2415677).sum := by decide
  have hdescent : baseEnd_2415677 < baseStart_2415677 := by decide
  rcases family_descends (prefixWord ++ tailWord_2415677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2415786 : List Nat := [3, 1, 5, 1, 1, 2, 1, 1, 2, 5]
def baseStart_2415786 : Nat := 118140960795 + 2415786 * 2 ^ 59
def prefixEnd_2415786 : Nat := 4983230072969 + 3 ^ 40 * 2415786 * 2
def baseEnd_2415786 : Nat := 826972917601726973243339

theorem tailTrace_2415786 : CollatzResearch.WordTrace tailWord_2415786 prefixEnd_2415786 826972917601726973243339 := by
  unfold tailWord_2415786
  simp only [CollatzResearch.WordTrace]
  refine ⟨22027738506506845061616803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58740636017351586830978141 22027738506506845061616803)
  ·
    refine ⟨33041607759760267592425205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22027738506506845061616803 33041607759760267592425205)
    ·
      refine ⟨3097650727477525086789863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 33041607759760267592425205 3097650727477525086789863)
      ·
        refine ⟨4646476091216287630184795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3097650727477525086789863 4646476091216287630184795)
        ·
          refine ⟨6969714136824431445277193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4646476091216287630184795 6969714136824431445277193)
          ·
            refine ⟨5227285602618323583957895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6969714136824431445277193 5227285602618323583957895)
            ·
              refine ⟨7840928403927485375936843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5227285602618323583957895 7840928403927485375936843)
              ·
                refine ⟨11761392605891228063905265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7840928403927485375936843 11761392605891228063905265)
                ·
                  refine ⟨8821044454418421047928949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11761392605891228063905265 8821044454418421047928949)
                  ·
                    refine ⟨826972917601726973243339, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8821044454418421047928949 826972917601726973243339)
                    ·
                      rfl

theorem cell22_2415786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 2, 1, 1, 2, 5].length) (baseStart_2415786 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2415786 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2415786 prefixEnd_2415786 := by exact prefixLift 2415786
  have htrace : WordTrace (prefixWord ++ tailWord_2415786) baseStart_2415786 baseEnd_2415786 := by
    simpa [prefixWord, tailWord_2415786, baseEnd_2415786] using wordTrace_append hprefix tailTrace_2415786
  have hstable : (prefixWord ++ tailWord_2415786).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2415786).length < 2 ^ (prefixWord ++ tailWord_2415786).sum := by decide
  have hdescent : baseEnd_2415786 < baseStart_2415786 := by decide
  rcases family_descends (prefixWord ++ tailWord_2415786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2415818 : List Nat := [3, 1, 2, 1, 3, 4, 2, 1, 1, 4]
def baseStart_2415818 : Nat := 118140960795 + 2415818 * 2 ^ 59
def prefixEnd_2415818 : Nat := 4983230072969 + 3 ^ 40 * 2415818 * 2
def baseEnd_2415818 : Nat := 826983871855689556443241

theorem tailTrace_2415818 : CollatzResearch.WordTrace tailWord_2415818 prefixEnd_2415818 826983871855689556443241 := by
  unfold tailWord_2415818
  simp only [CollatzResearch.WordTrace]
  refine ⟨22028030290477862427908027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58741414107940966474421405 22028030290477862427908027)
  ·
    refine ⟨33042045435716793641862041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22028030290477862427908027 33042045435716793641862041)
    ·
      refine ⟨24781534076787595231396531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33042045435716793641862041 24781534076787595231396531)
      ·
        refine ⟨37172301115181392847094797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24781534076787595231396531 37172301115181392847094797)
        ·
          refine ⟨13939612918193022317660549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37172301115181392847094797 13939612918193022317660549)
          ·
            refine ⟨2613677422161191684561353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13939612918193022317660549 2613677422161191684561353)
            ·
              refine ⟨1960258066620893763421015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2613677422161191684561353 1960258066620893763421015)
              ·
                refine ⟨2940387099931340645131523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1960258066620893763421015 2940387099931340645131523)
                ·
                  refine ⟨4410580649897010967697285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2940387099931340645131523 4410580649897010967697285)
                  ·
                    refine ⟨826983871855689556443241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4410580649897010967697285 826983871855689556443241)
                    ·
                      rfl

theorem cell22_2415818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 4, 2, 1, 1, 4].length) (baseStart_2415818 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2415818 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2415818 prefixEnd_2415818 := by exact prefixLift 2415818
  have htrace : WordTrace (prefixWord ++ tailWord_2415818) baseStart_2415818 baseEnd_2415818 := by
    simpa [prefixWord, tailWord_2415818, baseEnd_2415818] using wordTrace_append hprefix tailTrace_2415818
  have hstable : (prefixWord ++ tailWord_2415818).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2415818).length < 2 ^ (prefixWord ++ tailWord_2415818).sum := by decide
  have hdescent : baseEnd_2415818 < baseStart_2415818 := by decide
  rcases family_descends (prefixWord ++ tailWord_2415818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2415831 : List Nat := [1, 1, 3, 2, 1, 2, 5, 2, 2, 3]
def baseStart_2415831 : Nat := 118140960795 + 2415831 * 2 ^ 59
def prefixEnd_2415831 : Nat := 4983230072969 + 3 ^ 40 * 2415831 * 2
def baseEnd_2415831 : Nat := 826988322021361855868201

theorem tailTrace_2415831 : CollatzResearch.WordTrace tailWord_2415831 prefixEnd_2415831 826988322021361855868201 := by
  unfold tailWord_2415831
  simp only [CollatzResearch.WordTrace]
  refine ⟨88112595310864352931855347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58741730207242901954570231 88112595310864352931855347)
  ·
    refine ⟨132168892966296529397783021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88112595310864352931855347 132168892966296529397783021)
    ·
      refine ⟨49563334862361198524168633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 132168892966296529397783021 49563334862361198524168633)
      ·
        refine ⟨37172501146770898893126475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49563334862361198524168633 37172501146770898893126475)
        ·
          refine ⟨55758751720156348339689713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37172501146770898893126475 55758751720156348339689713)
          ·
            refine ⟨41819063790117261254767285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55758751720156348339689713 41819063790117261254767285)
            ·
              refine ⟨3920537230323493242634433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 41819063790117261254767285 3920537230323493242634433)
              ·
                refine ⟨2940402922742619931975825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3920537230323493242634433 2940402922742619931975825)
                ·
                  refine ⟨2205302192056964948981869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2940402922742619931975825 2205302192056964948981869)
                  ·
                    refine ⟨826988322021361855868201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2205302192056964948981869 826988322021361855868201)
                    ·
                      rfl

theorem cell22_2415831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 5, 2, 2, 3].length) (baseStart_2415831 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2415831 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2415831 prefixEnd_2415831 := by exact prefixLift 2415831
  have htrace : WordTrace (prefixWord ++ tailWord_2415831) baseStart_2415831 baseEnd_2415831 := by
    simpa [prefixWord, tailWord_2415831, baseEnd_2415831] using wordTrace_append hprefix tailTrace_2415831
  have hstable : (prefixWord ++ tailWord_2415831).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2415831).length < 2 ^ (prefixWord ++ tailWord_2415831).sum := by decide
  have hdescent : baseEnd_2415831 < baseStart_2415831 := by decide
  rcases family_descends (prefixWord ++ tailWord_2415831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2415848 : List Nat := [2, 1, 4, 1, 2, 1, 5, 1, 2, 3]
def baseStart_2415848 : Nat := 118140960795 + 2415848 * 2 ^ 59
def prefixEnd_2415848 : Nat := 4983230072969 + 3 ^ 40 * 2415848 * 2
def baseEnd_2415848 : Nat := 826994141468779478193149

theorem tailTrace_2415848 : CollatzResearch.WordTrace tailWord_2415848 prefixEnd_2415848 826994141468779478193149 := by
  unfold tailWord_2415848
  simp only [CollatzResearch.WordTrace]
  refine ⟨44056607675901382417612099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58742143567868509890149465 44056607675901382417612099)
  ·
    refine ⟨66084911513852073626418149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44056607675901382417612099 66084911513852073626418149)
    ·
      refine ⟨12390920908847263804953403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 66084911513852073626418149 12390920908847263804953403)
      ·
        refine ⟨18586381363270895707430105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12390920908847263804953403 18586381363270895707430105)
        ·
          refine ⟨13939786022453171780572579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18586381363270895707430105 13939786022453171780572579)
          ·
            refine ⟨20909679033679757670858869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13939786022453171780572579 20909679033679757670858869)
            ·
              refine ⟨1960282409407477281643019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 20909679033679757670858869 1960282409407477281643019)
              ·
                refine ⟨2940423614111215922464529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1960282409407477281643019 2940423614111215922464529)
                ·
                  refine ⟨2205317710583411941848397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2940423614111215922464529 2205317710583411941848397)
                  ·
                    refine ⟨826994141468779478193149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2205317710583411941848397 826994141468779478193149)
                    ·
                      rfl

theorem cell22_2415848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 5, 1, 2, 3].length) (baseStart_2415848 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2415848 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2415848 prefixEnd_2415848 := by exact prefixLift 2415848
  have htrace : WordTrace (prefixWord ++ tailWord_2415848) baseStart_2415848 baseEnd_2415848 := by
    simpa [prefixWord, tailWord_2415848, baseEnd_2415848] using wordTrace_append hprefix tailTrace_2415848
  have hstable : (prefixWord ++ tailWord_2415848).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2415848).length < 2 ^ (prefixWord ++ tailWord_2415848).sum := by decide
  have hdescent : baseEnd_2415848 < baseStart_2415848 := by decide
  rcases family_descends (prefixWord ++ tailWord_2415848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2415889 : List Nat := [1, 2, 2, 1, 1, 4, 2, 4, 5]
def baseStart_2415889 : Nat := 118140960795 + 2415889 * 2 ^ 59
def prefixEnd_2415889 : Nat := 4983230072969 + 3 ^ 40 * 2415889 * 2
def baseEnd_2415889 : Nat := 275669392202223012639341

theorem tailTrace_2415889 : CollatzResearch.WordTrace tailWord_2415889 prefixEnd_2415889 275669392202223012639341 := by
  unfold tailWord_2415889
  simp only [CollatzResearch.WordTrace]
  refine ⟨88114710744654228837466721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58743140496436152558311147 88114710744654228837466721)
  ·
    refine ⟨66086033058490671628100041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88114710744654228837466721 66086033058490671628100041)
    ·
      refine ⟨49564524793868003721075031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66086033058490671628100041 49564524793868003721075031)
      ·
        refine ⟨74346787190802005581612547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49564524793868003721075031 74346787190802005581612547)
        ·
          refine ⟨111520180786203008372418821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74346787190802005581612547 111520180786203008372418821)
          ·
            refine ⟨20910033897413064069828529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 111520180786203008372418821 20910033897413064069828529)
            ·
              refine ⟨15682525423059798052371397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20910033897413064069828529 15682525423059798052371397)
              ·
                refine ⟨2940473516823712134819637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15682525423059798052371397 2940473516823712134819637)
                ·
                  refine ⟨275669392202223012639341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2940473516823712134819637 275669392202223012639341)
                  ·
                    rfl

theorem cell22_2415889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 2, 4, 5].length) (baseStart_2415889 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2415889 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2415889 prefixEnd_2415889 := by exact prefixLift 2415889
  have htrace : WordTrace (prefixWord ++ tailWord_2415889) baseStart_2415889 baseEnd_2415889 := by
    simpa [prefixWord, tailWord_2415889, baseEnd_2415889] using wordTrace_append hprefix tailTrace_2415889
  have hstable : (prefixWord ++ tailWord_2415889).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2415889).length < 2 ^ (prefixWord ++ tailWord_2415889).sum := by decide
  have hdescent : baseEnd_2415889 < baseStart_2415889 := by decide
  rcases family_descends (prefixWord ++ tailWord_2415889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2415981 : List Nat := [1, 5, 1, 1, 1, 4, 1, 1, 1, 6]
def baseStart_2415981 : Nat := 118140960795 + 2415981 * 2 ^ 59
def prefixEnd_2415981 : Nat := 4983230072969 + 3 ^ 40 * 2415981 * 2
def baseEnd_2415981 : Nat := 827039670086811464617741

theorem tailTrace_2415981 : CollatzResearch.WordTrace tailWord_2415981 prefixEnd_2415981 827039670086811464617741 := by
  unfold tailWord_2415981
  simp only [CollatzResearch.WordTrace]
  refine ⟨88118066260320928549815797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58745377506880619033210531 88118066260320928549815797)
  ·
    refine ⟨8261068711905087051545231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 88118066260320928549815797 8261068711905087051545231)
    ·
      refine ⟨12391603067857630577317847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8261068711905087051545231 12391603067857630577317847)
      ·
        refine ⟨18587404601786445865976771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12391603067857630577317847 18587404601786445865976771)
        ·
          refine ⟨27881106902679668798965157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18587404601786445865976771 27881106902679668798965157)
          ·
            refine ⟨5227707544252437899805967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27881106902679668798965157 5227707544252437899805967)
            ·
              refine ⟨7841561316378656849708951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5227707544252437899805967 7841561316378656849708951)
              ·
                refine ⟨11762341974567985274563427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7841561316378656849708951 11762341974567985274563427)
                ·
                  refine ⟨17643512961851977911845141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11762341974567985274563427 17643512961851977911845141)
                  ·
                    refine ⟨827039670086811464617741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17643512961851977911845141 827039670086811464617741)
                    ·
                      rfl

theorem cell22_2415981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 4, 1, 1, 1, 6].length) (baseStart_2415981 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2415981 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2415981 prefixEnd_2415981 := by exact prefixLift 2415981
  have htrace : WordTrace (prefixWord ++ tailWord_2415981) baseStart_2415981 baseEnd_2415981 := by
    simpa [prefixWord, tailWord_2415981, baseEnd_2415981] using wordTrace_append hprefix tailTrace_2415981
  have hstable : (prefixWord ++ tailWord_2415981).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2415981).length < 2 ^ (prefixWord ++ tailWord_2415981).sum := by decide
  have hdescent : baseEnd_2415981 < baseStart_2415981 := by decide
  rcases family_descends (prefixWord ++ tailWord_2415981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2416071 : List Nat := [1, 1, 4, 1, 1, 3, 2, 2, 3, 4]
def baseStart_2416071 : Nat := 118140960795 + 2416071 * 2 ^ 59
def prefixEnd_2416071 : Nat := 4983230072969 + 3 ^ 40 * 2416071 * 2
def baseEnd_2416071 : Nat := 827070478926081229867465

theorem tailTrace_2416071 : CollatzResearch.WordTrace tailWord_2416071 prefixEnd_2416071 827070478926081229867465 := by
  unfold tailWord_2416071
  simp only [CollatzResearch.WordTrace]
  refine ⟨88121348829994873920592067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58747565886663249280394711 88121348829994873920592067)
  ·
    refine ⟨132182023244992310880888101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88121348829994873920592067 132182023244992310880888101)
    ·
      refine ⟨24784129358436058290166519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 132182023244992310880888101 24784129358436058290166519)
      ·
        refine ⟨37176194037654087435249779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24784129358436058290166519 37176194037654087435249779)
        ·
          refine ⟨55764291056481131152874669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37176194037654087435249779 55764291056481131152874669)
          ·
            refine ⟨20911609146180424182328001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 55764291056481131152874669 20911609146180424182328001)
            ·
              refine ⟨15683706859635318136746001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20911609146180424182328001 15683706859635318136746001)
              ·
                refine ⟨11762780144726488602559501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15683706859635318136746001 11762780144726488602559501)
                ·
                  refine ⟨4411042554272433225959813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11762780144726488602559501 4411042554272433225959813)
                  ·
                    refine ⟨827070478926081229867465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4411042554272433225959813 827070478926081229867465)
                    ·
                      rfl

theorem cell22_2416071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 2, 2, 3, 4].length) (baseStart_2416071 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2416071 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2416071 prefixEnd_2416071 := by exact prefixLift 2416071
  have htrace : WordTrace (prefixWord ++ tailWord_2416071) baseStart_2416071 baseEnd_2416071 := by
    simpa [prefixWord, tailWord_2416071, baseEnd_2416071] using wordTrace_append hprefix tailTrace_2416071
  have hstable : (prefixWord ++ tailWord_2416071).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2416071).length < 2 ^ (prefixWord ++ tailWord_2416071).sum := by decide
  have hdescent : baseEnd_2416071 < baseStart_2416071 := by decide
  rcases family_descends (prefixWord ++ tailWord_2416071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2416088 : List Nat := [2, 1, 2, 2, 2, 1, 5, 2, 1, 4]
def baseStart_2416088 : Nat := 118140960795 + 2416088 * 2 ^ 59
def prefixEnd_2416088 : Nat := 4983230072969 + 3 ^ 40 * 2416088 * 2
def baseEnd_2416088 : Nat := 827076298373498852192413

theorem tailTrace_2416088 : CollatzResearch.WordTrace tailWord_2416088 prefixEnd_2416088 827076298373498852192413 := by
  unfold tailWord_2416088
  simp only [CollatzResearch.WordTrace]
  refine ⟨44060984435466642911980459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58747979247288857215973945 44060984435466642911980459)
  ·
    refine ⟨66091476653199964367970689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44060984435466642911980459 66091476653199964367970689)
    ·
      refine ⟨49568607489899973275978017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66091476653199964367970689 49568607489899973275978017)
      ·
        refine ⟨37176455617424979956983513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49568607489899973275978017 37176455617424979956983513)
        ·
          refine ⟨27882341713068734967737635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37176455617424979956983513 27882341713068734967737635)
          ·
            refine ⟨41823512569603102451606453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27882341713068734967737635 41823512569603102451606453)
            ·
              refine ⟨3920954303400290854838105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 41823512569603102451606453 3920954303400290854838105)
              ·
                refine ⟨2940715727550218141128579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3920954303400290854838105 2940715727550218141128579)
                ·
                  refine ⟨4411073591325327211692869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2940715727550218141128579 4411073591325327211692869)
                  ·
                    refine ⟨827076298373498852192413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4411073591325327211692869 827076298373498852192413)
                    ·
                      rfl

theorem cell22_2416088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 5, 2, 1, 4].length) (baseStart_2416088 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2416088 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2416088 prefixEnd_2416088 := by exact prefixLift 2416088
  have htrace : WordTrace (prefixWord ++ tailWord_2416088) baseStart_2416088 baseEnd_2416088 := by
    simpa [prefixWord, tailWord_2416088, baseEnd_2416088] using wordTrace_append hprefix tailTrace_2416088
  have hstable : (prefixWord ++ tailWord_2416088).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2416088).length < 2 ^ (prefixWord ++ tailWord_2416088).sum := by decide
  have hdescent : baseEnd_2416088 < baseStart_2416088 := by decide
  rcases family_descends (prefixWord ++ tailWord_2416088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2416120 : List Nat := [2, 1, 2, 1, 1, 5, 4, 2, 4]
def baseStart_2416120 : Nat := 118140960795 + 2416120 * 2 ^ 59
def prefixEnd_2416120 : Nat := 4983230072969 + 3 ^ 40 * 2416120 * 2
def baseEnd_2416120 : Nat := 275695750875820478464105

theorem tailTrace_2416120 : CollatzResearch.WordTrace tailWord_2416120 prefixEnd_2416120 275695750875820478464105 := by
  unfold tailWord_2416120
  simp only [CollatzResearch.WordTrace]
  refine ⟨44061568003408677644562907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58748757337878236859417209 44061568003408677644562907)
  ·
    refine ⟨66092352005113016466844361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44061568003408677644562907 66092352005113016466844361)
    ·
      refine ⟨49569264003834762350133271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66092352005113016466844361 49569264003834762350133271)
      ·
        refine ⟨74353896005752143525199907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49569264003834762350133271 74353896005752143525199907)
        ·
          refine ⟨111530844008628215287799861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74353896005752143525199907 111530844008628215287799861)
          ·
            refine ⟨10456016625808895183231237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 111530844008628215287799861 10456016625808895183231237)
            ·
              refine ⟨1960503117339167846855857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10456016625808895183231237 1960503117339167846855857)
              ·
                refine ⟨1470377338004375885141893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1960503117339167846855857 1470377338004375885141893)
                ·
                  refine ⟨275695750875820478464105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1470377338004375885141893 275695750875820478464105)
                  ·
                    rfl

theorem cell22_2416120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 4, 2, 4].length) (baseStart_2416120 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2416120 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2416120 prefixEnd_2416120 := by exact prefixLift 2416120
  have htrace : WordTrace (prefixWord ++ tailWord_2416120) baseStart_2416120 baseEnd_2416120 := by
    simpa [prefixWord, tailWord_2416120, baseEnd_2416120] using wordTrace_append hprefix tailTrace_2416120
  have hstable : (prefixWord ++ tailWord_2416120).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2416120).length < 2 ^ (prefixWord ++ tailWord_2416120).sum := by decide
  have hdescent : baseEnd_2416120 < baseStart_2416120 := by decide
  rcases family_descends (prefixWord ++ tailWord_2416120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2416135 : List Nat := [1, 1, 4, 3, 2, 1, 2, 3, 2, 3]
def baseStart_2416135 : Nat := 118140960795 + 2416135 * 2 ^ 59
def prefixEnd_2416135 : Nat := 4983230072969 + 3 ^ 40 * 2416135 * 2
def baseEnd_2416135 : Nat := 827092387434006396267269

theorem tailTrace_2416135 : CollatzResearch.WordTrace tailWord_2416135 prefixEnd_2416135 827092387434006396267269 := by
  unfold tailWord_2416135
  simp only [CollatzResearch.WordTrace]
  refine ⟨88123683101763012850921859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58749122067842008567281239 88123683101763012850921859)
  ·
    refine ⟨132185524652644519276382789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88123683101763012850921859 132185524652644519276382789)
    ·
      refine ⟨24784785872370847364321773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 132185524652644519276382789 24784785872370847364321773)
      ·
        refine ⟨9294294702139067761620665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24784785872370847364321773 9294294702139067761620665)
        ·
          refine ⟨6970721026604300821215499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9294294702139067761620665 6970721026604300821215499)
          ·
            refine ⟨10456081539906451231823249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6970721026604300821215499 10456081539906451231823249)
            ·
              refine ⟨7842061154929838423867437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10456081539906451231823249 7842061154929838423867437)
              ·
                refine ⟨2940772933098689408950289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7842061154929838423867437 2940772933098689408950289)
                ·
                  refine ⟨2205579699824017056712717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2940772933098689408950289 2205579699824017056712717)
                  ·
                    refine ⟨827092387434006396267269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2205579699824017056712717 827092387434006396267269)
                    ·
                      rfl

theorem cell22_2416135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 2, 3, 2, 3].length) (baseStart_2416135 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2416135 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2416135 prefixEnd_2416135 := by exact prefixLift 2416135
  have htrace : WordTrace (prefixWord ++ tailWord_2416135) baseStart_2416135 baseEnd_2416135 := by
    simpa [prefixWord, tailWord_2416135, baseEnd_2416135] using wordTrace_append hprefix tailTrace_2416135
  have hstable : (prefixWord ++ tailWord_2416135).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2416135).length < 2 ^ (prefixWord ++ tailWord_2416135).sum := by decide
  have hdescent : baseEnd_2416135 < baseStart_2416135 := by decide
  rcases family_descends (prefixWord ++ tailWord_2416135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2416257 : List Nat := [1, 2, 4, 2, 1, 4, 1, 2, 1, 4]
def baseStart_2416257 : Nat := 118140960795 + 2416257 * 2 ^ 59
def prefixEnd_2416257 : Nat := 4983230072969 + 3 ^ 40 * 2416257 * 2
def baseEnd_2416257 : Nat := 827134150527238744716895

theorem tailTrace_2416257 : CollatzResearch.WordTrace tailWord_2416257 prefixEnd_2416257 827134150527238744716895 := by
  unfold tailWord_2416257
  simp only [CollatzResearch.WordTrace]
  refine ⟨88128132807321027686863025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58752088538214018457908683 88128132807321027686863025)
  ·
    refine ⟨66096099605490770765147269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88128132807321027686863025 66096099605490770765147269)
    ·
      refine ⟨12393018676029519518465113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 66096099605490770765147269 12393018676029519518465113)
      ·
        refine ⟨9294764007022139638848835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12393018676029519518465113 9294764007022139638848835)
        ·
          refine ⟨13942146010533209458273253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9294764007022139638848835 13942146010533209458273253)
          ·
            refine ⟨2614152376974976773426235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13942146010533209458273253 2614152376974976773426235)
            ·
              refine ⟨3921228565462465160139353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2614152376974976773426235 3921228565462465160139353)
              ·
                refine ⟨2940921424096848870104515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3921228565462465160139353 2940921424096848870104515)
                ·
                  refine ⟨4411382136145273305156773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2940921424096848870104515 4411382136145273305156773)
                  ·
                    refine ⟨827134150527238744716895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4411382136145273305156773 827134150527238744716895)
                    ·
                      rfl

theorem cell22_2416257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 4, 1, 2, 1, 4].length) (baseStart_2416257 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2416257 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2416257 prefixEnd_2416257 := by exact prefixLift 2416257
  have htrace : WordTrace (prefixWord ++ tailWord_2416257) baseStart_2416257 baseEnd_2416257 := by
    simpa [prefixWord, tailWord_2416257, baseEnd_2416257] using wordTrace_append hprefix tailTrace_2416257
  have hstable : (prefixWord ++ tailWord_2416257).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2416257).length < 2 ^ (prefixWord ++ tailWord_2416257).sum := by decide
  have hdescent : baseEnd_2416257 < baseStart_2416257 := by decide
  rcases family_descends (prefixWord ++ tailWord_2416257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2416270 : List Nat := [4, 1, 1, 3, 1, 3, 1, 2, 1, 5]
def baseStart_2416270 : Nat := 118140960795 + 2416270 * 2 ^ 59
def prefixEnd_2416270 : Nat := 4983230072969 + 3 ^ 40 * 2416270 * 2
def baseEnd_2416270 : Nat := 827138600692911044141855

theorem tailTrace_2416270 : CollatzResearch.WordTrace tailWord_2416270 prefixEnd_2416270 827138600692911044141855 := by
  unfold tailWord_2416270
  simp only [CollatzResearch.WordTrace]
  refine ⟨11016075869534241363385783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 58752404637515953938057509 11016075869534241363385783)
  ·
    refine ⟨16524113804301362045078675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11016075869534241363385783 16524113804301362045078675)
    ·
      refine ⟨24786170706452043067618013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16524113804301362045078675 24786170706452043067618013)
      ·
        refine ⟨9294814014919516150356755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24786170706452043067618013 9294814014919516150356755)
        ·
          refine ⟨13942221022379274225535133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9294814014919516150356755 13942221022379274225535133)
          ·
            refine ⟨5228332883392227834575675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13942221022379274225535133 5228332883392227834575675)
            ·
              refine ⟨7842499325088341751863513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5228332883392227834575675 7842499325088341751863513)
              ·
                refine ⟨5881874493816256313897635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7842499325088341751863513 5881874493816256313897635)
                ·
                  refine ⟨8822811740724384470846453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5881874493816256313897635 8822811740724384470846453)
                  ·
                    refine ⟨827138600692911044141855, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8822811740724384470846453 827138600692911044141855)
                    ·
                      rfl

theorem cell22_2416270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 3, 1, 2, 1, 5].length) (baseStart_2416270 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2416270 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2416270 prefixEnd_2416270 := by exact prefixLift 2416270
  have htrace : WordTrace (prefixWord ++ tailWord_2416270) baseStart_2416270 baseEnd_2416270 := by
    simpa [prefixWord, tailWord_2416270, baseEnd_2416270] using wordTrace_append hprefix tailTrace_2416270
  have hstable : (prefixWord ++ tailWord_2416270).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2416270).length < 2 ^ (prefixWord ++ tailWord_2416270).sum := by decide
  have hdescent : baseEnd_2416270 < baseStart_2416270 := by decide
  rcases family_descends (prefixWord ++ tailWord_2416270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2416274 : List Nat := [3, 2, 3, 1, 3, 1, 3, 1, 1, 4]
def baseStart_2416274 : Nat := 118140960795 + 2416274 * 2 ^ 59
def prefixEnd_2416274 : Nat := 4983230072969 + 3 ^ 40 * 2416274 * 2
def baseEnd_2416274 : Nat := 827139969974656367041843

theorem tailTrace_2416274 : CollatzResearch.WordTrace tailWord_2416274 prefixEnd_2416274 827139969974656367041843 := by
  unfold tailWord_2416274
  simp only [CollatzResearch.WordTrace]
  refine ⟨22032188212064859897557969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58752501898839626393487917 22032188212064859897557969)
  ·
    refine ⟨16524141159048644923168477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22032188212064859897557969 16524141159048644923168477)
    ·
      refine ⟨6196552934643241846188179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16524141159048644923168477 6196552934643241846188179)
      ·
        refine ⟨9294829401964862769282269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6196552934643241846188179 9294829401964862769282269)
        ·
          refine ⟨3485561025736823538480851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9294829401964862769282269 3485561025736823538480851)
          ·
            refine ⟨5228341538605235307721277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3485561025736823538480851 5228341538605235307721277)
            ·
              refine ⟨1960628076976963240395479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5228341538605235307721277 1960628076976963240395479)
              ·
                refine ⟨2940942115465444860593219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1960628076976963240395479 2940942115465444860593219)
                ·
                  refine ⟨4411413173198167290889829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2940942115465444860593219 4411413173198167290889829)
                  ·
                    refine ⟨827139969974656367041843, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4411413173198167290889829 827139969974656367041843)
                    ·
                      rfl

theorem cell22_2416274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 1, 3, 1, 1, 4].length) (baseStart_2416274 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2416274 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2416274 prefixEnd_2416274 := by exact prefixLift 2416274
  have htrace : WordTrace (prefixWord ++ tailWord_2416274) baseStart_2416274 baseEnd_2416274 := by
    simpa [prefixWord, tailWord_2416274, baseEnd_2416274] using wordTrace_append hprefix tailTrace_2416274
  have hstable : (prefixWord ++ tailWord_2416274).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2416274).length < 2 ^ (prefixWord ++ tailWord_2416274).sum := by decide
  have hdescent : baseEnd_2416274 < baseStart_2416274 := by decide
  rcases family_descends (prefixWord ++ tailWord_2416274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2416289 : List Nat := [1, 2, 3, 3, 2, 3, 2, 2, 4]
def baseStart_2416289 : Nat := 118140960795 + 2416289 * 2 ^ 59
def prefixEnd_2416289 : Nat := 4983230072969 + 3 ^ 40 * 2416289 * 2
def baseEnd_2416289 : Nat := 275715034927067109305599

theorem tailTrace_2416289 : CollatzResearch.WordTrace tailWord_2416289 prefixEnd_2416289 275715034927067109305599 := by
  unfold tailWord_2416289
  simp only [CollatzResearch.WordTrace]
  refine ⟨88129299943205097152027921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58752866628803398101351947 88129299943205097152027921)
  ·
    refine ⟨66096974957403822864020941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88129299943205097152027921 66096974957403822864020941)
    ·
      refine ⟨24786365609026433574007853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 66096974957403822864020941 24786365609026433574007853)
      ·
        refine ⟨9294887103384912590252945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24786365609026433574007853 9294887103384912590252945)
        ·
          refine ⟨6971165327538684442689709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9294887103384912590252945 6971165327538684442689709)
          ·
            refine ⟨2614186997827006666008641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6971165327538684442689709 2614186997827006666008641)
            ·
              refine ⟨1960640248370254999506481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2614186997827006666008641 1960640248370254999506481)
              ·
                refine ⟨1470480186277691249629861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1960640248370254999506481 1470480186277691249629861)
                ·
                  refine ⟨275715034927067109305599, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1470480186277691249629861 275715034927067109305599)
                  ·
                    rfl

theorem cell22_2416289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 3, 2, 2, 4].length) (baseStart_2416289 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2416289 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2416289 prefixEnd_2416289 := by exact prefixLift 2416289
  have htrace : WordTrace (prefixWord ++ tailWord_2416289) baseStart_2416289 baseEnd_2416289 := by
    simpa [prefixWord, tailWord_2416289, baseEnd_2416289] using wordTrace_append hprefix tailTrace_2416289
  have hstable : (prefixWord ++ tailWord_2416289).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2416289).length < 2 ^ (prefixWord ++ tailWord_2416289).sum := by decide
  have hdescent : baseEnd_2416289 < baseStart_2416289 := by decide
  rcases family_descends (prefixWord ++ tailWord_2416289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2416328 : List Nat := [2, 1, 3, 1, 2, 2, 2, 2, 7]
def baseStart_2416328 : Nat := 118140960795 + 2416328 * 2 ^ 59
def prefixEnd_2416328 : Nat := 4983230072969 + 3 ^ 40 * 2416328 * 2
def baseEnd_2416328 : Nat := 275719485092739408730559

theorem tailTrace_2416328 : CollatzResearch.WordTrace tailWord_2416328 prefixEnd_2416328 275719485092739408730559 := by
  unfold tailWord_2416328
  simp only [CollatzResearch.WordTrace]
  refine ⟨44065361195031903406348819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58753814926709204541798425 44065361195031903406348819)
  ·
    refine ⟨66098041792547855109523229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44065361195031903406348819 66098041792547855109523229)
    ·
      refine ⟨24786765672205445666071211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 66098041792547855109523229 24786765672205445666071211)
      ·
        refine ⟨37180148508308168499106817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24786765672205445666071211 37180148508308168499106817)
        ·
          refine ⟨27885111381231126374330113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37180148508308168499106817 27885111381231126374330113)
          ·
            refine ⟨20913833535923344780747585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27885111381231126374330113 20913833535923344780747585)
            ·
              refine ⟨15685375151942508585560689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20913833535923344780747585 15685375151942508585560689)
              ·
                refine ⟨11764031363956881439170517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15685375151942508585560689 11764031363956881439170517)
                ·
                  refine ⟨275719485092739408730559, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11764031363956881439170517 275719485092739408730559)
                  ·
                    rfl

theorem cell22_2416328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 2, 2, 7].length) (baseStart_2416328 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2416328 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2416328 prefixEnd_2416328 := by exact prefixLift 2416328
  have htrace : WordTrace (prefixWord ++ tailWord_2416328) baseStart_2416328 baseEnd_2416328 := by
    simpa [prefixWord, tailWord_2416328, baseEnd_2416328] using wordTrace_append hprefix tailTrace_2416328
  have hstable : (prefixWord ++ tailWord_2416328).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2416328).length < 2 ^ (prefixWord ++ tailWord_2416328).sum := by decide
  have hdescent : baseEnd_2416328 < baseStart_2416328 := by decide
  rcases family_descends (prefixWord ++ tailWord_2416328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2416343 : List Nat := [1, 1, 3, 2, 1, 3, 1, 1, 4, 5]
def baseStart_2416343 : Nat := 118140960795 + 2416343 * 2 ^ 59
def prefixEnd_2416343 : Nat := 4983230072969 + 3 ^ 40 * 2416343 * 2
def baseEnd_2416343 : Nat := 827163590084763187066631

theorem tailTrace_2416343 : CollatzResearch.WordTrace tailWord_2416343 prefixEnd_2416343 827163590084763187066631 := by
  unfold tailWord_2416343
  simp only [CollatzResearch.WordTrace]
  refine ⟨88131269485009464374493683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58754179656672976249662455 88131269485009464374493683)
  ·
    refine ⟨132196904227514196561740525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88131269485009464374493683 132196904227514196561740525)
    ·
      refine ⟨49573839085317823710652697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 132196904227514196561740525 49573839085317823710652697)
      ·
        refine ⟨37180379313988367782989523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49573839085317823710652697 37180379313988367782989523)
        ·
          refine ⟨55770568970982551674484285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37180379313988367782989523 55770568970982551674484285)
          ·
            refine ⟨20913963364118456877931607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 55770568970982551674484285 20913963364118456877931607)
            ·
              refine ⟨31370945046177685316897411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20913963364118456877931607 31370945046177685316897411)
              ·
                refine ⟨47056417569266527975346117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31370945046177685316897411 47056417569266527975346117)
                ·
                  refine ⟨8823078294237473995377397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 47056417569266527975346117 8823078294237473995377397)
                  ·
                    refine ⟨827163590084763187066631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8823078294237473995377397 827163590084763187066631)
                    ·
                      rfl

theorem cell22_2416343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 1, 1, 4, 5].length) (baseStart_2416343 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2416343 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2416343 prefixEnd_2416343 := by exact prefixLift 2416343
  have htrace : WordTrace (prefixWord ++ tailWord_2416343) baseStart_2416343 baseEnd_2416343 := by
    simpa [prefixWord, tailWord_2416343, baseEnd_2416343] using wordTrace_append hprefix tailTrace_2416343
  have hstable : (prefixWord ++ tailWord_2416343).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2416343).length < 2 ^ (prefixWord ++ tailWord_2416343).sum := by decide
  have hdescent : baseEnd_2416343 < baseStart_2416343 := by decide
  rcases family_descends (prefixWord ++ tailWord_2416343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2416345 : List Nat := [1, 2, 1, 2, 3, 3, 3, 2, 5]
def baseStart_2416345 : Nat := 118140960795 + 2416345 * 2 ^ 59
def prefixEnd_2416345 : Nat := 4983230072969 + 3 ^ 40 * 2416345 * 2
def baseEnd_2416345 : Nat := 275721424908545282838875

theorem tailTrace_2416345 : CollatzResearch.WordTrace tailWord_2416345 prefixEnd_2416345 275721424908545282838875 := by
  unfold tailWord_2416345
  simp only [CollatzResearch.WordTrace]
  refine ⟨88131342431002218716066489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58754228287334812477377659 88131342431002218716066489)
  ·
    refine ⟨66098506823251664037049867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88131342431002218716066489 66098506823251664037049867)
    ·
      refine ⟨99147760234877496055574801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66098506823251664037049867 99147760234877496055574801)
      ·
        refine ⟨74360820176158122041681101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 99147760234877496055574801 74360820176158122041681101)
        ·
          refine ⟨27885307566059295765630413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 74360820176158122041681101 27885307566059295765630413)
          ·
            refine ⟨10456990337272235912111405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27885307566059295765630413 10456990337272235912111405)
            ·
              refine ⟨3921371376477088467041777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10456990337272235912111405 3921371376477088467041777)
              ·
                refine ⟨2941028532357816350281333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3921371376477088467041777 2941028532357816350281333)
                ·
                  refine ⟨275721424908545282838875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2941028532357816350281333 275721424908545282838875)
                  ·
                    rfl

theorem cell22_2416345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 3, 2, 5].length) (baseStart_2416345 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2416345 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2416345 prefixEnd_2416345 := by exact prefixLift 2416345
  have htrace : WordTrace (prefixWord ++ tailWord_2416345) baseStart_2416345 baseEnd_2416345 := by
    simpa [prefixWord, tailWord_2416345, baseEnd_2416345] using wordTrace_append hprefix tailTrace_2416345
  have hstable : (prefixWord ++ tailWord_2416345).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2416345).length < 2 ^ (prefixWord ++ tailWord_2416345).sum := by decide
  have hdescent : baseEnd_2416345 < baseStart_2416345 := by decide
  rcases family_descends (prefixWord ++ tailWord_2416345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2416360 : List Nat := [2, 1, 4, 1, 3, 1, 2, 1, 2, 5]
def baseStart_2416360 : Nat := 118140960795 + 2416360 * 2 ^ 59
def prefixEnd_2416360 : Nat := 4983230072969 + 3 ^ 40 * 2416360 * 2
def baseEnd_2416360 : Nat := 827169409532180809391579

theorem tailTrace_2416360 : CollatzResearch.WordTrace tailWord_2416360 prefixEnd_2416360 827169409532180809391579 := by
  unfold tailWord_2416360
  simp only [CollatzResearch.WordTrace]
  refine ⟨44065944762973938138931267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58754593017298584185241689 44065944762973938138931267)
  ·
    refine ⟨66098917144460907208396901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44065944762973938138931267 66098917144460907208396901)
    ·
      refine ⟨12393546964586420101574419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 66098917144460907208396901 12393546964586420101574419)
      ·
        refine ⟨18590320446879630152361629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12393546964586420101574419 18590320446879630152361629)
        ·
          refine ⟨6971370167579861307135611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18590320446879630152361629 6971370167579861307135611)
          ·
            refine ⟨10457055251369791960703417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6971370167579861307135611 10457055251369791960703417)
            ·
              refine ⟨7842791438527343970527563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10457055251369791960703417 7842791438527343970527563)
              ·
                refine ⟨11764187157791015955791345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7842791438527343970527563 11764187157791015955791345)
                ·
                  refine ⟨8823140368343261966843509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11764187157791015955791345 8823140368343261966843509)
                  ·
                    refine ⟨827169409532180809391579, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8823140368343261966843509 827169409532180809391579)
                    ·
                      rfl

theorem cell22_2416360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 2, 1, 2, 5].length) (baseStart_2416360 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2416360 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2416360 prefixEnd_2416360 := by exact prefixLift 2416360
  have htrace : WordTrace (prefixWord ++ tailWord_2416360) baseStart_2416360 baseEnd_2416360 := by
    simpa [prefixWord, tailWord_2416360, baseEnd_2416360] using wordTrace_append hprefix tailTrace_2416360
  have hstable : (prefixWord ++ tailWord_2416360).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2416360).length < 2 ^ (prefixWord ++ tailWord_2416360).sum := by decide
  have hdescent : baseEnd_2416360 < baseStart_2416360 := by decide
  rcases family_descends (prefixWord ++ tailWord_2416360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2416375 : List Nat := [1, 1, 3, 1, 1, 1, 5, 4, 1, 4]
def baseStart_2416375 : Nat := 118140960795 + 2416375 * 2 ^ 59
def prefixEnd_2416375 : Nat := 4983230072969 + 3 ^ 40 * 2416375 * 2
def baseEnd_2416375 : Nat := 827174544338725770266533

theorem tailTrace_2416375 : CollatzResearch.WordTrace tailWord_2416375 prefixEnd_2416375 827174544338725770266533 := by
  unfold tailWord_2416375
  simp only [CollatzResearch.WordTrace]
  refine ⟨88132436620893533839658579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58754957747262355893105719 88132436620893533839658579)
  ·
    refine ⟨132198654931340300759487869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88132436620893533839658579 132198654931340300759487869)
    ·
      refine ⟨49574495599252612784807951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 132198654931340300759487869 49574495599252612784807951)
      ·
        refine ⟨74361743398878919177211927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49574495599252612784807951 74361743398878919177211927)
        ·
          refine ⟨111542615098318378765817891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74361743398878919177211927 111542615098318378765817891)
          ·
            refine ⟨167313922647477568148726837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 111542615098318378765817891 167313922647477568148726837)
            ·
              refine ⟨15685680248201022013943141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 167313922647477568148726837 15685680248201022013943141)
              ·
                refine ⟨2941065046537691627614339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15685680248201022013943141 2941065046537691627614339)
                ·
                  refine ⟨4411597569806537441421509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2941065046537691627614339 4411597569806537441421509)
                  ·
                    refine ⟨827174544338725770266533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4411597569806537441421509 827174544338725770266533)
                    ·
                      rfl

theorem cell22_2416375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 5, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 5, 4, 1, 4].length) (baseStart_2416375 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2416375 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2416375 prefixEnd_2416375 := by exact prefixLift 2416375
  have htrace : WordTrace (prefixWord ++ tailWord_2416375) baseStart_2416375 baseEnd_2416375 := by
    simpa [prefixWord, tailWord_2416375, baseEnd_2416375] using wordTrace_append hprefix tailTrace_2416375
  have hstable : (prefixWord ++ tailWord_2416375).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2416375).length < 2 ^ (prefixWord ++ tailWord_2416375).sum := by decide
  have hdescent : baseEnd_2416375 < baseStart_2416375 := by decide
  rcases family_descends (prefixWord ++ tailWord_2416375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2416403 : List Nat := [1, 1, 1, 2, 1, 3, 2, 2, 3, 6]
def baseStart_2416403 : Nat := 118140960795 + 2416403 * 2 ^ 59
def prefixEnd_2416403 : Nat := 4983230072969 + 3 ^ 40 * 2416403 * 2
def baseEnd_2416403 : Nat := 827184129310943030566447

theorem tailTrace_2416403 : CollatzResearch.WordTrace tailWord_2416403 prefixEnd_2416403 827184129310943030566447 := by
  unfold tailWord_2416403
  simp only [CollatzResearch.WordTrace]
  refine ⟨88133457864792094621677863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58755638576528063081118575 88133457864792094621677863)
  ·
    refine ⟨132200186797188141932516795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88133457864792094621677863 132200186797188141932516795)
    ·
      refine ⟨198300280195782212898775193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132200186797188141932516795 198300280195782212898775193)
      ·
        refine ⟨148725210146836659674081395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 198300280195782212898775193 148725210146836659674081395)
        ·
          refine ⟨223087815220254989511122093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 148725210146836659674081395 223087815220254989511122093)
          ·
            refine ⟨83657930707595621066670785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 223087815220254989511122093 83657930707595621066670785)
            ·
              refine ⟨62743448030696715800003089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 83657930707595621066670785 62743448030696715800003089)
              ·
                refine ⟨47057586023022536850002317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 62743448030696715800003089 47057586023022536850002317)
                ·
                  refine ⟨17646594758633451318750869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 47057586023022536850002317 17646594758633451318750869)
                  ·
                    refine ⟨827184129310943030566447, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17646594758633451318750869 827184129310943030566447)
                    ·
                      rfl

theorem cell22_2416403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 2, 3, 6].length) (baseStart_2416403 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2416403 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2416403 prefixEnd_2416403 := by exact prefixLift 2416403
  have htrace : WordTrace (prefixWord ++ tailWord_2416403) baseStart_2416403 baseEnd_2416403 := by
    simpa [prefixWord, tailWord_2416403, baseEnd_2416403] using wordTrace_append hprefix tailTrace_2416403
  have hstable : (prefixWord ++ tailWord_2416403).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2416403).length < 2 ^ (prefixWord ++ tailWord_2416403).sum := by decide
  have hdescent : baseEnd_2416403 < baseStart_2416403 := by decide
  rcases family_descends (prefixWord ++ tailWord_2416403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2416407 : List Nat := [1, 1, 3, 4, 2, 3, 1, 1, 6]
def baseStart_2416407 : Nat := 118140960795 + 2416407 * 2 ^ 59
def prefixEnd_2416407 : Nat := 4983230072969 + 3 ^ 40 * 2416407 * 2
def baseEnd_2416407 : Nat := 275728499530896117822145

theorem tailTrace_2416407 : CollatzResearch.WordTrace tailWord_2416407 prefixEnd_2416407 275728499530896117822145 := by
  unfold tailWord_2416407
  simp only [CollatzResearch.WordTrace]
  refine ⟨88133603756777603304823475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58755735837851735536548983 88133603756777603304823475)
  ·
    refine ⟨132200405635166404957235213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88133603756777603304823475 132200405635166404957235213)
    ·
      refine ⟨49575152113187401858963205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 132200405635166404957235213 49575152113187401858963205)
      ·
        refine ⟨9295341021222637848555601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 49575152113187401858963205 9295341021222637848555601)
        ·
          refine ⟨6971505765916978386416701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9295341021222637848555601 6971505765916978386416701)
          ·
            refine ⟨2614314662218866894906263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6971505765916978386416701 2614314662218866894906263)
            ·
              refine ⟨3921471993328300342359395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2614314662218866894906263 3921471993328300342359395)
              ·
                refine ⟨5882207989992450513539093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3921471993328300342359395 5882207989992450513539093)
                ·
                  refine ⟨275728499530896117822145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5882207989992450513539093 275728499530896117822145)
                  ·
                    rfl

theorem cell22_2416407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 3, 1, 1, 6].length) (baseStart_2416407 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2416407 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2416407 prefixEnd_2416407 := by exact prefixLift 2416407
  have htrace : WordTrace (prefixWord ++ tailWord_2416407) baseStart_2416407 baseEnd_2416407 := by
    simpa [prefixWord, tailWord_2416407, baseEnd_2416407] using wordTrace_append hprefix tailTrace_2416407
  have hstable : (prefixWord ++ tailWord_2416407).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2416407).length < 2 ^ (prefixWord ++ tailWord_2416407).sum := by decide
  have hdescent : baseEnd_2416407 < baseStart_2416407 := by decide
  rcases family_descends (prefixWord ++ tailWord_2416407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2416465 : List Nat := [1, 2, 2, 1, 5, 1, 1, 1, 2, 6]
def baseStart_2416465 : Nat := 118140960795 + 2416465 * 2 ^ 59
def prefixEnd_2416465 : Nat := 4983230072969 + 3 ^ 40 * 2416465 * 2
def baseEnd_2416465 : Nat := 827205353177995535516257

theorem tailTrace_2416465 : CollatzResearch.WordTrace tailWord_2416465 prefixEnd_2416465 827205353177995535516257 := by
  unfold tailWord_2416465
  simp only [CollatzResearch.WordTrace]
  refine ⟨88135719190567479210434849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58757146127044986140289899 88135719190567479210434849)
  ·
    refine ⟨66101789392925609407826137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88135719190567479210434849 66101789392925609407826137)
    ·
      refine ⟨49576342044694207055869603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66101789392925609407826137 49576342044694207055869603)
      ·
        refine ⟨74364513067041310583804405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49576342044694207055869603 74364513067041310583804405)
        ·
          refine ⟨6971673100035122867231663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 74364513067041310583804405 6971673100035122867231663)
          ·
            refine ⟨10457509650052684300847495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6971673100035122867231663 10457509650052684300847495)
            ·
              refine ⟨15686264475079026451271243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10457509650052684300847495 15686264475079026451271243)
              ·
                refine ⟨23529396712618539676906865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15686264475079026451271243 23529396712618539676906865)
                ·
                  refine ⟨17647047534463904757680149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23529396712618539676906865 17647047534463904757680149)
                  ·
                    refine ⟨827205353177995535516257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17647047534463904757680149 827205353177995535516257)
                    ·
                      rfl

theorem cell22_2416465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 1, 1, 2, 6].length) (baseStart_2416465 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2416465 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2416465 prefixEnd_2416465 := by exact prefixLift 2416465
  have htrace : WordTrace (prefixWord ++ tailWord_2416465) baseStart_2416465 baseEnd_2416465 := by
    simpa [prefixWord, tailWord_2416465, baseEnd_2416465] using wordTrace_append hprefix tailTrace_2416465
  have hstable : (prefixWord ++ tailWord_2416465).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2416465).length < 2 ^ (prefixWord ++ tailWord_2416465).sum := by decide
  have hdescent : baseEnd_2416465 < baseStart_2416465 := by decide
  rcases family_descends (prefixWord ++ tailWord_2416465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2416484 : List Nat := [2, 3, 1, 1, 5, 1, 1, 2, 3, 3]
def baseStart_2416484 : Nat := 118140960795 + 2416484 * 2 ^ 59
def prefixEnd_2416484 : Nat := 4983230072969 + 3 ^ 40 * 2416484 * 2
def baseEnd_2416484 : Nat := 827211857266285819291199

theorem tailTrace_2416484 : CollatzResearch.WordTrace tailWord_2416484 prefixEnd_2416484 827211857266285819291199 := by
  unfold tailWord_2416484
  simp only [CollatzResearch.WordTrace]
  refine ⟨44068206088749322727688253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58757608118332430303584337 44068206088749322727688253)
  ·
    refine ⟨16525577283280996022883095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44068206088749322727688253 16525577283280996022883095)
    ·
      refine ⟨24788365924921494034324643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16525577283280996022883095 24788365924921494034324643)
      ·
        refine ⟨37182548887382241051486965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24788365924921494034324643 37182548887382241051486965)
        ·
          refine ⟨3485863958192085098576903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 37182548887382241051486965 3485863958192085098576903)
          ·
            refine ⟨5228795937288127647865355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3485863958192085098576903 5228795937288127647865355)
            ·
              refine ⟨7843193905932191471798033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5228795937288127647865355 7843193905932191471798033)
              ·
                refine ⟨5882395429449143603848525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7843193905932191471798033 5882395429449143603848525)
                ·
                  refine ⟨2205898286043428851443197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5882395429449143603848525 2205898286043428851443197)
                  ·
                    refine ⟨827211857266285819291199, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2205898286043428851443197 827211857266285819291199)
                    ·
                      rfl

theorem cell22_2416484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 1, 1, 2, 3, 3].length) (baseStart_2416484 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2416484 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2416484 prefixEnd_2416484 := by exact prefixLift 2416484
  have htrace : WordTrace (prefixWord ++ tailWord_2416484) baseStart_2416484 baseEnd_2416484 := by
    simpa [prefixWord, tailWord_2416484, baseEnd_2416484] using wordTrace_append hprefix tailTrace_2416484
  have hstable : (prefixWord ++ tailWord_2416484).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2416484).length < 2 ^ (prefixWord ++ tailWord_2416484).sum := by decide
  have hdescent : baseEnd_2416484 < baseStart_2416484 := by decide
  rcases family_descends (prefixWord ++ tailWord_2416484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2416501 : List Nat := [1, 3, 4, 1, 1, 1, 4, 3, 1, 3]
def baseStart_2416501 : Nat := 118140960795 + 2416501 * 2 ^ 59
def prefixEnd_2416501 : Nat := 4983230072969 + 3 ^ 40 * 2416501 * 2
def baseEnd_2416501 : Nat := 827217676713703441616147

theorem tailTrace_2416501 : CollatzResearch.WordTrace tailWord_2416501 prefixEnd_2416501 827217676713703441616147 := by
  unfold tailWord_2416501
  simp only [CollatzResearch.WordTrace]
  refine ⟨88137032218437057358745357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58758021478958038239163571 88137032218437057358745357)
  ·
    refine ⟨33051387081913896509529509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 88137032218437057358745357 33051387081913896509529509)
    ·
      refine ⟨6197135077858855595536783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 33051387081913896509529509 6197135077858855595536783)
      ·
        refine ⟨9295702616788283393305175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6197135077858855595536783 9295702616788283393305175)
        ·
          refine ⟨13943553925182425089957763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9295702616788283393305175 13943553925182425089957763)
          ·
            refine ⟨20915330887773637634936645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13943553925182425089957763 20915330887773637634936645)
            ·
              refine ⟨3921624541457557056550621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20915330887773637634936645 3921624541457557056550621)
              ·
                refine ⟨1470609203046583896206483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3921624541457557056550621 1470609203046583896206483)
                ·
                  refine ⟨2205913804569875844309725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1470609203046583896206483 2205913804569875844309725)
                  ·
                    refine ⟨827217676713703441616147, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2205913804569875844309725 827217676713703441616147)
                    ·
                      rfl

theorem cell22_2416501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 4, 3, 1, 3].length) (baseStart_2416501 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2416501 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2416501 prefixEnd_2416501 := by exact prefixLift 2416501
  have htrace : WordTrace (prefixWord ++ tailWord_2416501) baseStart_2416501 baseEnd_2416501 := by
    simpa [prefixWord, tailWord_2416501, baseEnd_2416501] using wordTrace_append hprefix tailTrace_2416501
  have hstable : (prefixWord ++ tailWord_2416501).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2416501).length < 2 ^ (prefixWord ++ tailWord_2416501).sum := by decide
  have hdescent : baseEnd_2416501 < baseStart_2416501 := by decide
  rcases family_descends (prefixWord ++ tailWord_2416501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
