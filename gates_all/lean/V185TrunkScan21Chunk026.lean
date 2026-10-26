import V185TrunkScan21Chunk025

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental

namespace V185TrunkScan21Incremental

def tailWord_312924 : List Nat := [2, 2, 4, 1, 2, 2, 1, 3, 4]
def baseStart_312924 : Nat := 118140960795 + 312924 * 2 ^ 59
def prefixEnd_312924 : Nat := 4983230072969 + 3 ^ 40 * 312924 * 2
def baseEnd_312924 : Nat := 71413520145617296493731

theorem tailTrace_312924 : CollatzResearch.WordTrace tailWord_312924 prefixEnd_312924 71413520145617296493731 := by
  unfold tailWord_312924
  simp only [CollatzResearch.WordTrace]
  refine ⟨5706637959168633004740913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7608850612224844006321217 5706637959168633004740913)
  ·
    refine ⟨4279978469376474753555685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5706637959168633004740913 4279978469376474753555685)
    ·
      refine ⟨802495963008089016291691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4279978469376474753555685 802495963008089016291691)
      ·
        refine ⟨1203743944512133524437537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 802495963008089016291691 1203743944512133524437537)
        ·
          refine ⟨902807958384100143328153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1203743944512133524437537 902807958384100143328153)
          ·
            refine ⟨677105968788075107496115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 902807958384100143328153 677105968788075107496115)
            ·
              refine ⟨1015658953182112661244173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 677105968788075107496115 1015658953182112661244173)
              ·
                refine ⟨380872107443292247966565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1015658953182112661244173 380872107443292247966565)
                ·
                  refine ⟨71413520145617296493731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 380872107443292247966565 71413520145617296493731)
                  ·
                    rfl

theorem cell21_312924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 2, 1, 3, 4].length) (baseStart_312924 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_312924 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_312924 prefixEnd_312924 := by exact prefixLift 312924
  have htrace : WordTrace (prefixWord ++ tailWord_312924) baseStart_312924 baseEnd_312924 := by
    simpa [prefixWord, tailWord_312924, baseEnd_312924] using wordTrace_append hprefix tailTrace_312924
  have hstable : (prefixWord ++ tailWord_312924).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_312924).length < 2 ^ (prefixWord ++ tailWord_312924).sum := by decide
  have hdescent : baseEnd_312924 < baseStart_312924 := by decide
  rcases family_descends (prefixWord ++ tailWord_312924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_312983 : List Nat := [1, 1, 3, 3, 2, 2, 2, 3, 4]
def baseStart_312983 : Nat := 118140960795 + 312983 * 2 ^ 59
def prefixEnd_312983 : Nat := 4983230072969 + 3 ^ 40 * 312983 * 2
def baseEnd_312983 : Nat := 71426984749446305010277

theorem tailTrace_312983 : CollatzResearch.WordTrace tailWord_312983 prefixEnd_312983 71426984749446305010277 := by
  unfold tailWord_312983
  simp only [CollatzResearch.WordTrace]
  refine ⟨11415427825123519085879603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7610285216749012723919735 11415427825123519085879603)
  ·
    refine ⟨17123141737685278628819405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11415427825123519085879603 17123141737685278628819405)
    ·
      refine ⟨6421178151631979485807277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17123141737685278628819405 6421178151631979485807277)
      ·
        refine ⟨2407941806861992307177729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6421178151631979485807277 2407941806861992307177729)
        ·
          refine ⟨1805956355146494230383297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2407941806861992307177729 1805956355146494230383297)
          ·
            refine ⟨1354467266359870672787473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1805956355146494230383297 1354467266359870672787473)
            ·
              refine ⟨1015850449769903004590605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1354467266359870672787473 1015850449769903004590605)
              ·
                refine ⟨380943918663713626721477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1015850449769903004590605 380943918663713626721477)
                ·
                  refine ⟨71426984749446305010277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 380943918663713626721477 71426984749446305010277)
                  ·
                    rfl

theorem cell21_312983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 2, 3, 4].length) (baseStart_312983 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_312983 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_312983 prefixEnd_312983 := by exact prefixLift 312983
  have htrace : WordTrace (prefixWord ++ tailWord_312983) baseStart_312983 baseEnd_312983 := by
    simpa [prefixWord, tailWord_312983, baseEnd_312983] using wordTrace_append hprefix tailTrace_312983
  have hstable : (prefixWord ++ tailWord_312983).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_312983).length < 2 ^ (prefixWord ++ tailWord_312983).sum := by decide
  have hdescent : baseEnd_312983 < baseStart_312983 := by decide
  rcases family_descends (prefixWord ++ tailWord_312983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_313011 : List Nat := [1, 1, 1, 2, 3, 3, 1, 2, 7]
def baseStart_313011 : Nat := 118140960795 + 313011 * 2 ^ 59
def prefixEnd_313011 : Nat := 4983230072969 + 3 ^ 40 * 313011 * 2
def baseEnd_313011 : Nat := 71433374730924478543553

theorem tailTrace_313011 : CollatzResearch.WordTrace tailWord_313011 prefixEnd_313011 71433374730924478543553 := by
  unfold tailWord_313011
  simp only [CollatzResearch.WordTrace]
  refine ⟨11416449069022079867898887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7610966046014719911932591 11416449069022079867898887)
  ·
    refine ⟨17124673603533119801848331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11416449069022079867898887 17124673603533119801848331)
    ·
      refine ⟨25687010405299679702772497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17124673603533119801848331 25687010405299679702772497)
      ·
        refine ⟨19265257803974759777079373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25687010405299679702772497 19265257803974759777079373)
        ·
          refine ⟨7224471676490534916404765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19265257803974759777079373 7224471676490534916404765)
          ·
            refine ⟨2709176878683950593651787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7224471676490534916404765 2709176878683950593651787)
            ·
              refine ⟨4063765318025925890477681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2709176878683950593651787 4063765318025925890477681)
              ·
                refine ⟨3047823988519444417858261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4063765318025925890477681 3047823988519444417858261)
                ·
                  refine ⟨71433374730924478543553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3047823988519444417858261 71433374730924478543553)
                  ·
                    rfl

theorem cell21_313011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 1, 2, 7].length) (baseStart_313011 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_313011 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_313011 prefixEnd_313011 := by exact prefixLift 313011
  have htrace : WordTrace (prefixWord ++ tailWord_313011) baseStart_313011 baseEnd_313011 := by
    simpa [prefixWord, tailWord_313011, baseEnd_313011] using wordTrace_append hprefix tailTrace_313011
  have hstable : (prefixWord ++ tailWord_313011).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_313011).length < 2 ^ (prefixWord ++ tailWord_313011).sum := by decide
  have hdescent : baseEnd_313011 < baseStart_313011 := by decide
  rcases family_descends (prefixWord ++ tailWord_313011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_313073 : List Nat := [1, 2, 2, 2, 2, 5, 7]
def baseStart_313073 : Nat := 118140960795 + 313073 * 2 ^ 59
def prefixEnd_313073 : Nat := 4983230072969 + 3 ^ 40 * 313073 * 2
def baseEnd_313073 : Nat := 7938613775069572056677

theorem tailTrace_313073 : CollatzResearch.WordTrace tailWord_313073 prefixEnd_313073 7938613775069572056677 := by
  unfold tailWord_313073
  simp only [CollatzResearch.WordTrace]
  refine ⟨11418710394797464456655873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7612473596531642971103915 11418710394797464456655873)
  ·
    refine ⟨8564032796098098342491905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11418710394797464456655873 8564032796098098342491905)
    ·
      refine ⟨6423024597073573756868929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8564032796098098342491905 6423024597073573756868929)
      ·
        refine ⟨4817268447805180317651697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6423024597073573756868929 4817268447805180317651697)
        ·
          refine ⟨3612951335853885238238773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4817268447805180317651697 3612951335853885238238773)
          ·
            refine ⟨338714187736301741084885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 3612951335853885238238773 338714187736301741084885)
            ·
              refine ⟨7938613775069572056677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 338714187736301741084885 7938613775069572056677)
              ·
                rfl

theorem cell21_313073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 5, 7].length) (baseStart_313073 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_313073 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_313073 prefixEnd_313073 := by exact prefixLift 313073
  have htrace : WordTrace (prefixWord ++ tailWord_313073) baseStart_313073 baseEnd_313073 := by
    simpa [prefixWord, tailWord_313073, baseEnd_313073] using wordTrace_append hprefix tailTrace_313073
  have hstable : (prefixWord ++ tailWord_313073).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_313073).length < 2 ^ (prefixWord ++ tailWord_313073).sum := by decide
  have hdescent : baseEnd_313073 < baseStart_313073 := by decide
  rcases family_descends (prefixWord ++ tailWord_313073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_313090 : List Nat := [3, 4, 1, 1, 1, 1, 4, 6]
def baseStart_313090 : Nat := 118140960795 + 313090 * 2 ^ 59
def prefixEnd_313090 : Nat := 4983230072969 + 3 ^ 40 * 313090 * 2
def baseEnd_313090 : Nat := 23817134535745965575575

theorem tailTrace_313090 : CollatzResearch.WordTrace tailWord_313090 prefixEnd_313090 23817134535745965575575 := by
  unfold tailWord_313090
  simp only [CollatzResearch.WordTrace]
  refine ⟨2854832608933969090006181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7612886957157250906683149 2854832608933969090006181)
  ·
    refine ⟨535281114175119204376159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2854832608933969090006181 535281114175119204376159)
    ·
      refine ⟨802921671262678806564239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 535281114175119204376159 802921671262678806564239)
      ·
        refine ⟨1204382506894018209846359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 802921671262678806564239 1204382506894018209846359)
        ·
          refine ⟨1806573760341027314769539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1204382506894018209846359 1806573760341027314769539)
          ·
            refine ⟨2709860640511540972154309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1806573760341027314769539 2709860640511540972154309)
            ·
              refine ⟨508098870095913932278933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2709860640511540972154309 508098870095913932278933)
              ·
                refine ⟨23817134535745965575575, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 508098870095913932278933 23817134535745965575575)
                ·
                  rfl

theorem cell21_313090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 4, 6].length) (baseStart_313090 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_313090 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_313090 prefixEnd_313090 := by exact prefixLift 313090
  have htrace : WordTrace (prefixWord ++ tailWord_313090) baseStart_313090 baseEnd_313090 := by
    simpa [prefixWord, tailWord_313090, baseEnd_313090] using wordTrace_append hprefix tailTrace_313090
  have hstable : (prefixWord ++ tailWord_313090).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_313090).length < 2 ^ (prefixWord ++ tailWord_313090).sum := by decide
  have hdescent : baseEnd_313090 < baseStart_313090 := by decide
  rcases family_descends (prefixWord ++ tailWord_313090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_313132 : List Nat := [2, 2, 1, 1, 1, 14]
def baseStart_313132 : Nat := 118140960795 + 313132 * 2 ^ 59
def prefixEnd_313132 : Nat := 4983230072969 + 3 ^ 40 * 313132 * 2
def baseEnd_313132 : Nat := 2646703280720561371357

theorem tailTrace_313132 : CollatzResearch.WordTrace tailWord_313132 prefixEnd_313132 2646703280720561371357 := by
  unfold tailWord_313132
  simp only [CollatzResearch.WordTrace]
  refine ⟨5710431150791858766526825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7613908201055811688702433 5710431150791858766526825)
  ·
    refine ⟨4282823363093894074895119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5710431150791858766526825 4282823363093894074895119)
    ·
      refine ⟨6424235044640841112342679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4282823363093894074895119 6424235044640841112342679)
      ·
        refine ⟨9636352566961261668514019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6424235044640841112342679 9636352566961261668514019)
        ·
          refine ⟨14454528850441892502771029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9636352566961261668514019 14454528850441892502771029)
          ·
            refine ⟨2646703280720561371357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 14 14454528850441892502771029 2646703280720561371357)
            ·
              rfl

theorem cell21_313132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 14].length) (baseStart_313132 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_313132 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_313132 prefixEnd_313132 := by exact prefixLift 313132
  have htrace : WordTrace (prefixWord ++ tailWord_313132) baseStart_313132 baseEnd_313132 := by
    simpa [prefixWord, tailWord_313132, baseEnd_313132] using wordTrace_append hprefix tailTrace_313132
  have hstable : (prefixWord ++ tailWord_313132).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_313132).length < 2 ^ (prefixWord ++ tailWord_313132).sum := by decide
  have hdescent : baseEnd_313132 < baseStart_313132 := by decide
  rcases family_descends (prefixWord ++ tailWord_313132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_313138 : List Nat := [3, 2, 1, 1, 3, 2, 4, 2, 3]
def baseStart_313138 : Nat := 118140960795 + 313138 * 2 ^ 59
def prefixEnd_313138 : Nat := 4983230072969 + 3 ^ 40 * 313138 * 2
def baseEnd_313138 : Nat := 71462357861200479926627

theorem tailTrace_313138 : CollatzResearch.WordTrace tailWord_313138 prefixEnd_313138 71462357861200479926627 := by
  unfold tailWord_313138
  simp only [CollatzResearch.WordTrace]
  refine ⟨2855270284890495139443017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7614054093041320371848045 2855270284890495139443017)
  ·
    refine ⟨2141452713667871354582263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2855270284890495139443017 2141452713667871354582263)
    ·
      refine ⟨3212179070501807031873395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2141452713667871354582263 3212179070501807031873395)
      ·
        refine ⟨4818268605752710547810093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3212179070501807031873395 4818268605752710547810093)
        ·
          refine ⟨1806850727157266455428785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4818268605752710547810093 1806850727157266455428785)
          ·
            refine ⟨1355138045367949841571589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1806850727157266455428785 1355138045367949841571589)
            ·
              refine ⟨254088383506490595294673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1355138045367949841571589 254088383506490595294673)
              ·
                refine ⟨190566287629867946471005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 254088383506490595294673 190566287629867946471005)
                ·
                  refine ⟨71462357861200479926627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 190566287629867946471005 71462357861200479926627)
                  ·
                    rfl

theorem cell21_313138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 4, 2, 3].length) (baseStart_313138 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_313138 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_313138 prefixEnd_313138 := by exact prefixLift 313138
  have htrace : WordTrace (prefixWord ++ tailWord_313138) baseStart_313138 baseEnd_313138 := by
    simpa [prefixWord, tailWord_313138, baseEnd_313138] using wordTrace_append hprefix tailTrace_313138
  have hstable : (prefixWord ++ tailWord_313138).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_313138).length < 2 ^ (prefixWord ++ tailWord_313138).sum := by decide
  have hdescent : baseEnd_313138 < baseStart_313138 := by decide
  rcases family_descends (prefixWord ++ tailWord_313138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_313197 : List Nat := [1, 5, 1, 1, 1, 1, 4, 4, 3]
def baseStart_313197 : Nat := 118140960795 + 313197 * 2 ^ 59
def prefixEnd_313197 : Nat := 4983230072969 + 3 ^ 40 * 313197 * 2
def baseEnd_313197 : Nat := 71475822465029488443173

theorem tailTrace_313197 : CollatzResearch.WordTrace tailWord_313197 prefixEnd_313197 71475822465029488443173 := by
  unfold tailWord_313197
  simp only [CollatzResearch.WordTrace]
  refine ⟨11423233046348233634169845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7615488697565489089446563 11423233046348233634169845)
  ·
    refine ⟨1070928098095146903203423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 11423233046348233634169845 1070928098095146903203423)
    ·
      refine ⟨1606392147142720354805135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1070928098095146903203423 1606392147142720354805135)
      ·
        refine ⟨2409588220714080532207703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1606392147142720354805135 2409588220714080532207703)
        ·
          refine ⟨3614382331071120798311555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2409588220714080532207703 3614382331071120798311555)
          ·
            refine ⟨5421573496606681197467333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3614382331071120798311555 5421573496606681197467333)
            ·
              refine ⟨1016545030613752724525125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5421573496606681197467333 1016545030613752724525125)
              ·
                refine ⟨190602193240078635848461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1016545030613752724525125 190602193240078635848461)
                ·
                  refine ⟨71475822465029488443173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 190602193240078635848461 71475822465029488443173)
                  ·
                    rfl

theorem cell21_313197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 4, 4, 3].length) (baseStart_313197 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_313197 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_313197 prefixEnd_313197 := by exact prefixLift 313197
  have htrace : WordTrace (prefixWord ++ tailWord_313197) baseStart_313197 baseEnd_313197 := by
    simpa [prefixWord, tailWord_313197, baseEnd_313197] using wordTrace_append hprefix tailTrace_313197
  have hstable : (prefixWord ++ tailWord_313197).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_313197).length < 2 ^ (prefixWord ++ tailWord_313197).sum := by decide
  have hdescent : baseEnd_313197 < baseStart_313197 := by decide
  rcases family_descends (prefixWord ++ tailWord_313197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_313262 : List Nat := [4, 1, 5, 1, 1, 1, 1, 3, 4]
def baseStart_313262 : Nat := 118140960795 + 313262 * 2 ^ 59
def prefixEnd_313262 : Nat := 4983230072969 + 3 ^ 40 * 313262 * 2
def baseEnd_313262 : Nat := 71490656350603819859707

theorem tailTrace_313262 : CollatzResearch.WordTrace tailWord_313262 prefixEnd_313262 71490656350603819859707 := by
  unfold tailWord_313262
  simp only [CollatzResearch.WordTrace]
  refine ⟨1428200473889093716910755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7617069194075166490190693 1428200473889093716910755)
  ·
    refine ⟨2142300710833640575366133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1428200473889093716910755 2142300710833640575366133)
    ·
      refine ⟨200840691640653803940575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 2142300710833640575366133 200840691640653803940575)
      ·
        refine ⟨301261037460980705910863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 200840691640653803940575 301261037460980705910863)
        ·
          refine ⟨451891556191471058866295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 301261037460980705910863 451891556191471058866295)
          ·
            refine ⟨677837334287206588299443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 451891556191471058866295 677837334287206588299443)
            ·
              refine ⟨1016756001430809882449165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 677837334287206588299443 1016756001430809882449165)
              ·
                refine ⟨381283500536553705918437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1016756001430809882449165 381283500536553705918437)
                ·
                  refine ⟨71490656350603819859707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 381283500536553705918437 71490656350603819859707)
                  ·
                    rfl

theorem cell21_313262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 1, 1, 3, 4].length) (baseStart_313262 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_313262 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_313262 prefixEnd_313262 := by exact prefixLift 313262
  have htrace : WordTrace (prefixWord ++ tailWord_313262) baseStart_313262 baseEnd_313262 := by
    simpa [prefixWord, tailWord_313262, baseEnd_313262] using wordTrace_append hprefix tailTrace_313262
  have hstable : (prefixWord ++ tailWord_313262).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_313262).length < 2 ^ (prefixWord ++ tailWord_313262).sum := by decide
  have hdescent : baseEnd_313262 < baseStart_313262 := by decide
  rcases family_descends (prefixWord ++ tailWord_313262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_313349 : List Nat := [1, 3, 1, 1, 2, 5, 2, 3, 3]
def baseStart_313349 : Nat := 118140960795 + 313349 * 2 ^ 59
def prefixEnd_313349 : Nat := 4983230072969 + 3 ^ 40 * 313349 * 2
def baseEnd_313349 : Nat := 71510510935911001909529

theorem tailTrace_313349 : CollatzResearch.WordTrace tailWord_313349 prefixEnd_313349 71510510935911001909529 := by
  unfold tailWord_313349
  simp only [CollatzResearch.WordTrace]
  refine ⟨11428776941797563593703101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7619184627865042395802067 11428776941797563593703101)
  ·
    refine ⟨4285791353174086347638663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11428776941797563593703101 4285791353174086347638663)
    ·
      refine ⟨6428687029761129521457995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4285791353174086347638663 6428687029761129521457995)
      ·
        refine ⟨9643030544641694282186993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6428687029761129521457995 9643030544641694282186993)
        ·
          refine ⟨7232272908481270711640245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9643030544641694282186993 7232272908481270711640245)
          ·
            refine ⟨678025585170119129216273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 7232272908481270711640245 678025585170119129216273)
            ·
              refine ⟨508519188877589346912205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 678025585170119129216273 508519188877589346912205)
              ·
                refine ⟨190694695829096005092077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 508519188877589346912205 190694695829096005092077)
                ·
                  refine ⟨71510510935911001909529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 190694695829096005092077 71510510935911001909529)
                  ·
                    rfl

theorem cell21_313349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 5, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 5, 2, 3, 3].length) (baseStart_313349 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_313349 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_313349 prefixEnd_313349 := by exact prefixLift 313349
  have htrace : WordTrace (prefixWord ++ tailWord_313349) baseStart_313349 baseEnd_313349 := by
    simpa [prefixWord, tailWord_313349, baseEnd_313349] using wordTrace_append hprefix tailTrace_313349
  have hstable : (prefixWord ++ tailWord_313349).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_313349).length < 2 ^ (prefixWord ++ tailWord_313349).sum := by decide
  have hdescent : baseEnd_313349 < baseStart_313349 := by decide
  rcases family_descends (prefixWord ++ tailWord_313349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_313394 : List Nat := [3, 2, 1, 1, 2, 5, 2, 5]
def baseStart_313394 : Nat := 118140960795 + 313394 * 2 ^ 59
def prefixEnd_313394 : Nat := 4983230072969 + 3 ^ 40 * 313394 * 2
def baseEnd_313394 : Nat := 23840260183000307886479

theorem tailTrace_313394 : CollatzResearch.WordTrace tailWord_313394 prefixEnd_313394 23840260183000307886479 := by
  unfold tailWord_313394
  simp only [CollatzResearch.WordTrace]
  refine ⟨2857604556658634069772809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7620278817756357519394157 2857604556658634069772809)
  ·
    refine ⟨2143203417493975552329607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2857604556658634069772809 2143203417493975552329607)
    ·
      refine ⟨3214805126240963328494411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2143203417493975552329607 3214805126240963328494411)
      ·
        refine ⟨4822207689361444992741617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3214805126240963328494411 4822207689361444992741617)
        ·
          refine ⟨3616655767021083744556213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4822207689361444992741617 3616655767021083744556213)
          ·
            refine ⟨339061478158226601052145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 3616655767021083744556213 339061478158226601052145)
            ·
              refine ⟨254296108618669950789109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 339061478158226601052145 254296108618669950789109)
              ·
                refine ⟨23840260183000307886479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 254296108618669950789109 23840260183000307886479)
                ·
                  rfl

theorem cell21_313394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 5, 2, 5].length) (baseStart_313394 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_313394 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_313394 prefixEnd_313394 := by exact prefixLift 313394
  have htrace : WordTrace (prefixWord ++ tailWord_313394) baseStart_313394 baseEnd_313394 := by
    simpa [prefixWord, tailWord_313394, baseEnd_313394] using wordTrace_append hprefix tailTrace_313394
  have hstable : (prefixWord ++ tailWord_313394).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_313394).length < 2 ^ (prefixWord ++ tailWord_313394).sum := by decide
  have hdescent : baseEnd_313394 < baseStart_313394 := by decide
  rcases family_descends (prefixWord ++ tailWord_313394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_313422 : List Nat := [4, 1, 1, 1, 1, 4, 2, 1, 6]
def baseStart_313422 : Nat := 118140960795 + 313422 * 2 ^ 59
def prefixEnd_313422 : Nat := 4983230072969 + 3 ^ 40 * 313422 * 2
def baseEnd_313422 : Nat := 71527170530479097192713

theorem tailTrace_313422 : CollatzResearch.WordTrace tailWord_313422 prefixEnd_313422 71527170530479097192713 := by
  unfold tailWord_313422
  simp only [CollatzResearch.WordTrace]
  refine ⟨1428929933816637132638815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7620959647022064707407013 1428929933816637132638815)
  ·
    refine ⟨2143394900724955698958223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1428929933816637132638815 2143394900724955698958223)
    ·
      refine ⟨3215092351087433548437335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2143394900724955698958223 3215092351087433548437335)
      ·
        refine ⟨4822638526631150322656003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3215092351087433548437335 4822638526631150322656003)
        ·
          refine ⟨7233957789946725483984005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4822638526631150322656003 7233957789946725483984005)
          ·
            refine ⟨1356367085615011028247001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7233957789946725483984005 1356367085615011028247001)
            ·
              refine ⟨1017275314211258271185251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1356367085615011028247001 1017275314211258271185251)
              ·
                refine ⟨1525912971316887406777877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1017275314211258271185251 1525912971316887406777877)
                ·
                  refine ⟨71527170530479097192713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1525912971316887406777877 71527170530479097192713)
                  ·
                    rfl

theorem cell21_313422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 2, 1, 6].length) (baseStart_313422 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_313422 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_313422 prefixEnd_313422 := by exact prefixLift 313422
  have htrace : WordTrace (prefixWord ++ tailWord_313422) baseStart_313422 baseEnd_313422 := by
    simpa [prefixWord, tailWord_313422, baseEnd_313422] using wordTrace_append hprefix tailTrace_313422
  have hstable : (prefixWord ++ tailWord_313422).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_313422).length < 2 ^ (prefixWord ++ tailWord_313422).sum := by decide
  have hdescent : baseEnd_313422 < baseStart_313422 := by decide
  rcases family_descends (prefixWord ++ tailWord_313422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_313532 : List Nat := [2, 2, 2, 3, 3, 2, 1, 2, 4]
def baseStart_313532 : Nat := 118140960795 + 313532 * 2 ^ 59
def prefixEnd_313532 : Nat := 4983230072969 + 3 ^ 40 * 313532 * 2
def baseEnd_313532 : Nat := 71552274029143350359155

theorem tailTrace_313532 : CollatzResearch.WordTrace tailWord_313532 prefixEnd_313532 71552274029143350359155 := by
  unfold tailWord_313532
  simp only [CollatzResearch.WordTrace]
  refine ⟨5717725750067292923807425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7623634333423057231743233 5717725750067292923807425)
  ·
    refine ⟨4288294312550469692855569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5717725750067292923807425 4288294312550469692855569)
    ·
      refine ⟨3216220734412852269641677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4288294312550469692855569 3216220734412852269641677)
      ·
        refine ⟨1206082775404819601115629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3216220734412852269641677 1206082775404819601115629)
        ·
          refine ⟨452281040776807350418361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1206082775404819601115629 452281040776807350418361)
          ·
            refine ⟨339210780582605512813771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 452281040776807350418361 339210780582605512813771)
            ·
              refine ⟨508816170873908269220657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 339210780582605512813771 508816170873908269220657)
              ·
                refine ⟨381612128155431201915493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 508816170873908269220657 381612128155431201915493)
                ·
                  refine ⟨71552274029143350359155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 381612128155431201915493 71552274029143350359155)
                  ·
                    rfl

theorem cell21_313532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 2, 1, 2, 4].length) (baseStart_313532 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_313532 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_313532 prefixEnd_313532 := by exact prefixLift 313532
  have htrace : WordTrace (prefixWord ++ tailWord_313532) baseStart_313532 baseEnd_313532 := by
    simpa [prefixWord, tailWord_313532, baseEnd_313532] using wordTrace_append hprefix tailTrace_313532
  have hstable : (prefixWord ++ tailWord_313532).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_313532).length < 2 ^ (prefixWord ++ tailWord_313532).sum := by decide
  have hdescent : baseEnd_313532 < baseStart_313532 := by decide
  rcases family_descends (prefixWord ++ tailWord_313532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_313608 : List Nat := [2, 1, 3, 2, 3, 3, 2, 1, 4]
def baseStart_313608 : Nat := 118140960795 + 313608 * 2 ^ 59
def prefixEnd_313608 : Nat := 4983230072969 + 3 ^ 40 * 313608 * 2
def baseEnd_313608 : Nat := 71569618264584107092333

theorem tailTrace_313608 : CollatzResearch.WordTrace tailWord_313608 prefixEnd_313608 71569618264584107092333 := by
  unfold tailWord_313608
  simp only [CollatzResearch.WordTrace]
  refine ⟨5719111723929625413690739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7625482298572833884920985 5719111723929625413690739)
  ·
    refine ⟨8578667585894438120536109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5719111723929625413690739 8578667585894438120536109)
    ·
      refine ⟨3217000344710414295201041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8578667585894438120536109 3217000344710414295201041)
      ·
        refine ⟨2412750258532810721400781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3217000344710414295201041 2412750258532810721400781)
        ·
          refine ⟨904781346949804020525293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2412750258532810721400781 904781346949804020525293)
          ·
            refine ⟨339293005106176507696985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 904781346949804020525293 339293005106176507696985)
            ·
              refine ⟨254469753829632380772739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 339293005106176507696985 254469753829632380772739)
              ·
                refine ⟨381704630744448571159109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 254469753829632380772739 381704630744448571159109)
                ·
                  refine ⟨71569618264584107092333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 381704630744448571159109 71569618264584107092333)
                  ·
                    rfl

theorem cell21_313608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 3, 2, 1, 4].length) (baseStart_313608 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_313608 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_313608 prefixEnd_313608 := by exact prefixLift 313608
  have htrace : WordTrace (prefixWord ++ tailWord_313608) baseStart_313608 baseEnd_313608 := by
    simpa [prefixWord, tailWord_313608, baseEnd_313608] using wordTrace_append hprefix tailTrace_313608
  have hstable : (prefixWord ++ tailWord_313608).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_313608).length < 2 ^ (prefixWord ++ tailWord_313608).sum := by decide
  have hdescent : baseEnd_313608 < baseStart_313608 := by decide
  rcases family_descends (prefixWord ++ tailWord_313608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_313633 : List Nat := [1, 2, 3, 2, 1, 1, 2, 1, 8]
def baseStart_313633 : Nat := 118140960795 + 313633 * 2 ^ 59
def prefixEnd_313633 : Nat := 4983230072969 + 3 ^ 40 * 313633 * 2
def baseEnd_313633 : Nat := 71575323605189619175615

theorem tailTrace_313633 : CollatzResearch.WordTrace tailWord_313633 prefixEnd_313633 71575323605189619175615 := by
  unfold tailWord_313633
  simp only [CollatzResearch.WordTrace]
  refine ⟨11439135272768680097041553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7626090181845786731361035 11439135272768680097041553)
  ·
    refine ⟨8579351454576510072781165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11439135272768680097041553 8579351454576510072781165)
    ·
      refine ⟨3217256795466191277292937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8579351454576510072781165 3217256795466191277292937)
      ·
        refine ⟨2412942596599643457969703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3217256795466191277292937 2412942596599643457969703)
        ·
          refine ⟨3619413894899465186954555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2412942596599643457969703 3619413894899465186954555)
          ·
            refine ⟨5429120842349197780431833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3619413894899465186954555 5429120842349197780431833)
            ·
              refine ⟨4071840631761898335323875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5429120842349197780431833 4071840631761898335323875)
              ·
                refine ⟨6107760947642847502985813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4071840631761898335323875 6107760947642847502985813)
                ·
                  refine ⟨71575323605189619175615, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 6107760947642847502985813 71575323605189619175615)
                  ·
                    rfl

theorem cell21_313633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 2, 1, 8].length) (baseStart_313633 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_313633 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_313633 prefixEnd_313633 := by exact prefixLift 313633
  have htrace : WordTrace (prefixWord ++ tailWord_313633) baseStart_313633 baseEnd_313633 := by
    simpa [prefixWord, tailWord_313633, baseEnd_313633] using wordTrace_append hprefix tailTrace_313633
  have hstable : (prefixWord ++ tailWord_313633).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_313633).length < 2 ^ (prefixWord ++ tailWord_313633).sum := by decide
  have hdescent : baseEnd_313633 < baseStart_313633 := by decide
  rcases family_descends (prefixWord ++ tailWord_313633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_313639 : List Nat := [1, 1, 8, 1, 2, 8]
def baseStart_313639 : Nat := 118140960795 + 313639 * 2 ^ 59
def prefixEnd_313639 : Nat := 4983230072969 + 3 ^ 40 * 313639 * 2
def baseEnd_313639 : Nat := 2650988625442034891689

theorem tailTrace_313639 : CollatzResearch.WordTrace tailWord_313639 prefixEnd_313639 2650988625442034891689 := by
  unfold tailWord_313639
  simp only [CollatzResearch.WordTrace]
  refine ⟨11439354110746943121759971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7626236073831295414506647 11439354110746943121759971)
  ·
    refine ⟨17159031166120414682639957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11439354110746943121759971 17159031166120414682639957)
    ·
      refine ⟨201082396477973609562187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 17159031166120414682639957 201082396477973609562187)
      ·
        refine ⟨301623594716960414343281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 201082396477973609562187 301623594716960414343281)
        ·
          refine ⟨226217696037720310757461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 301623594716960414343281 226217696037720310757461)
          ·
            refine ⟨2650988625442034891689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 226217696037720310757461 2650988625442034891689)
            ·
              rfl

theorem cell21_313639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 2, 8].length) (baseStart_313639 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_313639 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_313639 prefixEnd_313639 := by exact prefixLift 313639
  have htrace : WordTrace (prefixWord ++ tailWord_313639) baseStart_313639 baseEnd_313639 := by
    simpa [prefixWord, tailWord_313639, baseEnd_313639] using wordTrace_append hprefix tailTrace_313639
  have hstable : (prefixWord ++ tailWord_313639).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_313639).length < 2 ^ (prefixWord ++ tailWord_313639).sum := by decide
  have hdescent : baseEnd_313639 < baseStart_313639 := by decide
  rcases family_descends (prefixWord ++ tailWord_313639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_313681 : List Nat := [1, 2, 2, 1, 4, 3, 3, 5]
def baseStart_313681 : Nat := 118140960795 + 313681 * 2 ^ 59
def prefixEnd_313681 : Nat := 4983230072969 + 3 ^ 40 * 313681 * 2
def baseEnd_313681 : Nat := 23862092619717400791839

theorem tailTrace_313681 : CollatzResearch.WordTrace tailWord_313681 prefixEnd_313681 23862092619717400791839 := by
  unfold tailWord_313681
  simp only [CollatzResearch.WordTrace]
  refine ⟨11440885976594784294788897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7627257317729856196525931 11440885976594784294788897)
  ·
    refine ⟨8580664482446088221091673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11440885976594784294788897 8580664482446088221091673)
    ·
      refine ⟨6435498361834566165818755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8580664482446088221091673 6435498361834566165818755)
      ·
        refine ⟨9653247542751849248728133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6435498361834566165818755 9653247542751849248728133)
        ·
          refine ⟨1809983914265971734136525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9653247542751849248728133 1809983914265971734136525)
          ·
            refine ⟨678743967849739400301197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1809983914265971734136525 678743967849739400301197)
            ·
              refine ⟨254528987943652275112949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 678743967849739400301197 254528987943652275112949)
              ·
                refine ⟨23862092619717400791839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 254528987943652275112949 23862092619717400791839)
                ·
                  rfl

theorem cell21_313681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 3, 3, 5].length) (baseStart_313681 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_313681 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_313681 prefixEnd_313681 := by exact prefixLift 313681
  have htrace : WordTrace (prefixWord ++ tailWord_313681) baseStart_313681 baseEnd_313681 := by
    simpa [prefixWord, tailWord_313681, baseEnd_313681] using wordTrace_append hprefix tailTrace_313681
  have hstable : (prefixWord ++ tailWord_313681).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_313681).length < 2 ^ (prefixWord ++ tailWord_313681).sum := by decide
  have hdescent : baseEnd_313681 < baseStart_313681 := by decide
  rcases family_descends (prefixWord ++ tailWord_313681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_313712 : List Nat := [2, 1, 1, 1, 4, 3, 2, 4, 3]
def baseStart_313712 : Nat := 118140960795 + 313712 * 2 ^ 59
def prefixEnd_313712 : Nat := 4983230072969 + 3 ^ 40 * 313712 * 2
def baseEnd_313712 : Nat := 71593352481503037358787

theorem tailTrace_313712 : CollatzResearch.WordTrace tailWord_313712 prefixEnd_313712 71593352481503037358787 := by
  unfold tailWord_313712
  simp only [CollatzResearch.WordTrace]
  refine ⟨5721008319741238294583695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7628011092988317726111593 5721008319741238294583695)
  ·
    refine ⟨8581512479611857441875543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5721008319741238294583695 8581512479611857441875543)
    ·
      refine ⟨12872268719417786162813315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8581512479611857441875543 12872268719417786162813315)
      ·
        refine ⟨19308403079126679244219973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12872268719417786162813315 19308403079126679244219973)
        ·
          refine ⟨3620325577336252358291245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19308403079126679244219973 3620325577336252358291245)
          ·
            refine ⟨1357622091501094634359217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3620325577336252358291245 1357622091501094634359217)
            ·
              refine ⟨1018216568625820975769413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1357622091501094634359217 1018216568625820975769413)
              ·
                refine ⟨190915606617341432956765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1018216568625820975769413 190915606617341432956765)
                ·
                  refine ⟨71593352481503037358787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 190915606617341432956765 71593352481503037358787)
                  ·
                    rfl

theorem cell21_313712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 2, 4, 3].length) (baseStart_313712 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_313712 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_313712 prefixEnd_313712 := by exact prefixLift 313712
  have htrace : WordTrace (prefixWord ++ tailWord_313712) baseStart_313712 baseEnd_313712 := by
    simpa [prefixWord, tailWord_313712, baseEnd_313712] using wordTrace_append hprefix tailTrace_313712
  have hstable : (prefixWord ++ tailWord_313712).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_313712).length < 2 ^ (prefixWord ++ tailWord_313712).sum := by decide
  have hdescent : baseEnd_313712 < baseStart_313712 := by decide
  rcases family_descends (prefixWord ++ tailWord_313712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_313740 : List Nat := [2, 2, 1, 2, 1, 5, 1, 7]
def baseStart_313740 : Nat := 118140960795 + 313740 * 2 ^ 59
def prefixEnd_313740 : Nat := 4983230072969 + 3 ^ 40 * 313740 * 2
def baseEnd_313740 : Nat := 23866580820993736964021

theorem tailTrace_313740 : CollatzResearch.WordTrace tailWord_313740 prefixEnd_313740 23866580820993736964021 := by
  unfold tailWord_313740
  simp only [CollatzResearch.WordTrace]
  refine ⟨5721518941690518685593337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7628691922254024914124449 5721518941690518685593337)
  ·
    refine ⟨4291139206267889014195003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5721518941690518685593337 4291139206267889014195003)
    ·
      refine ⟨6436708809401833521292505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4291139206267889014195003 6436708809401833521292505)
      ·
        refine ⟨4827531607051375140969379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6436708809401833521292505 4827531607051375140969379)
        ·
          refine ⟨7241297410577062711454069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4827531607051375140969379 7241297410577062711454069)
          ·
            refine ⟨678871632241599629198819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 7241297410577062711454069 678871632241599629198819)
            ·
              refine ⟨1018307448362399443798229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 678871632241599629198819 1018307448362399443798229)
              ·
                refine ⟨23866580820993736964021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1018307448362399443798229 23866580820993736964021)
                ·
                  rfl

theorem cell21_313740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 5, 1, 7].length) (baseStart_313740 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_313740 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_313740 prefixEnd_313740 := by exact prefixLift 313740
  have htrace : WordTrace (prefixWord ++ tailWord_313740) baseStart_313740 baseEnd_313740 := by
    simpa [prefixWord, tailWord_313740, baseEnd_313740] using wordTrace_append hprefix tailTrace_313740
  have hstable : (prefixWord ++ tailWord_313740).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_313740).length < 2 ^ (prefixWord ++ tailWord_313740).sum := by decide
  have hdescent : baseEnd_313740 < baseStart_313740 := by decide
  rcases family_descends (prefixWord ++ tailWord_313740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_313757 : List Nat := [1, 4, 2, 1, 4, 2, 7]
def baseStart_313757 : Nat := 118140960795 + 313757 * 2 ^ 59
def prefixEnd_313757 : Nat := 4983230072969 + 3 ^ 40 * 313757 * 2
def baseEnd_313757 : Nat := 7955958010510328789855

theorem tailTrace_313757 : CollatzResearch.WordTrace tailWord_313757 prefixEnd_313757 7955958010510328789855 := by
  unfold tailWord_313757
  simp only [CollatzResearch.WordTrace]
  refine ⟨11443657924319449274555525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7629105282879632849703683 11443657924319449274555525)
  ·
    refine ⟨2145685860809896738979161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11443657924319449274555525 2145685860809896738979161)
    ·
      refine ⟨1609264395607422554234371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2145685860809896738979161 1609264395607422554234371)
      ·
        refine ⟨2413896593411133831351557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1609264395607422554234371 2413896593411133831351557)
        ·
          refine ⟨452605611264587593378417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2413896593411133831351557 452605611264587593378417)
          ·
            refine ⟨339454208448440695033813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 452605611264587593378417 339454208448440695033813)
            ·
              refine ⟨7955958010510328789855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 339454208448440695033813 7955958010510328789855)
              ·
                rfl

theorem cell21_313757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 2, 7].length) (baseStart_313757 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_313757 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_313757 prefixEnd_313757 := by exact prefixLift 313757
  have htrace : WordTrace (prefixWord ++ tailWord_313757) baseStart_313757 baseEnd_313757 := by
    simpa [prefixWord, tailWord_313757, baseEnd_313757] using wordTrace_append hprefix tailTrace_313757
  have hstable : (prefixWord ++ tailWord_313757).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_313757).length < 2 ^ (prefixWord ++ tailWord_313757).sum := by decide
  have hdescent : baseEnd_313757 < baseStart_313757 := by decide
  rcases family_descends (prefixWord ++ tailWord_313757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_313875 : List Nat := [1, 1, 1, 2, 1, 5, 10]
def baseStart_313875 : Nat := 118140960795 + 313875 * 2 ^ 59
def prefixEnd_313875 : Nat := 4983230072969 + 3 ^ 40 * 313875 * 2
def baseEnd_313875 : Nat := 7958950144694552904643

theorem tailTrace_313875 : CollatzResearch.WordTrace tailWord_313875 prefixEnd_313875 7958950144694552904643 := by
  unfold tailWord_313875
  simp only [CollatzResearch.WordTrace]
  refine ⟨11447961737891955427351079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7631974491927970284900719 11447961737891955427351079)
  ·
    refine ⟨17171942606837933141026619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11447961737891955427351079 17171942606837933141026619)
    ·
      refine ⟨25757913910256899711539929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17171942606837933141026619 25757913910256899711539929)
      ·
        refine ⟨19318435432692674783654947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25757913910256899711539929 19318435432692674783654947)
        ·
          refine ⟨28977653149039012175482421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19318435432692674783654947 28977653149039012175482421)
          ·
            refine ⟨2716654982722407391451477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 28977653149039012175482421 2716654982722407391451477)
            ·
              refine ⟨7958950144694552904643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 2716654982722407391451477 7958950144694552904643)
              ·
                rfl

theorem cell21_313875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 10].length) (baseStart_313875 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_313875 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_313875 prefixEnd_313875 := by exact prefixLift 313875
  have htrace : WordTrace (prefixWord ++ tailWord_313875) baseStart_313875 baseEnd_313875 := by
    simpa [prefixWord, tailWord_313875, baseEnd_313875] using wordTrace_append hprefix tailTrace_313875
  have hstable : (prefixWord ++ tailWord_313875).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_313875).length < 2 ^ (prefixWord ++ tailWord_313875).sum := by decide
  have hdescent : baseEnd_313875 < baseStart_313875 := by decide
  rcases family_descends (prefixWord ++ tailWord_313875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_313901 : List Nat := [1, 5, 4, 1, 2, 1, 2, 5]
def baseStart_313901 : Nat := 118140960795 + 313901 * 2 ^ 59
def prefixEnd_313901 : Nat := 4983230072969 + 3 ^ 40 * 313901 * 2
def baseEnd_313901 : Nat := 23878828285493569569467

theorem tailTrace_313901 : CollatzResearch.WordTrace tailWord_313901 prefixEnd_313901 23878828285493569569467 := by
  unfold tailWord_313901
  simp only [CollatzResearch.WordTrace]
  refine ⟨11448910035797761867797557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7632606690531841245198371 11448910035797761867797557)
  ·
    refine ⟨1073335315856040175106021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 11448910035797761867797557 1073335315856040175106021)
    ·
      refine ⟨201250371723007532832379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1073335315856040175106021 201250371723007532832379)
      ·
        refine ⟨301875557584511299248569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 201250371723007532832379 301875557584511299248569)
        ·
          refine ⟨226406668188383474436427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 301875557584511299248569 226406668188383474436427)
          ·
            refine ⟨339610002282575211654641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 226406668188383474436427 339610002282575211654641)
            ·
              refine ⟨254707501711931408740981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 339610002282575211654641 254707501711931408740981)
              ·
                refine ⟨23878828285493569569467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 254707501711931408740981 23878828285493569569467)
                ·
                  rfl

theorem cell21_313901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 2, 1, 2, 5].length) (baseStart_313901 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_313901 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_313901 prefixEnd_313901 := by exact prefixLift 313901
  have htrace : WordTrace (prefixWord ++ tailWord_313901) baseStart_313901 baseEnd_313901 := by
    simpa [prefixWord, tailWord_313901, baseEnd_313901] using wordTrace_append hprefix tailTrace_313901
  have hstable : (prefixWord ++ tailWord_313901).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_313901).length < 2 ^ (prefixWord ++ tailWord_313901).sum := by decide
  have hdescent : baseEnd_313901 < baseStart_313901 := by decide
  rcases family_descends (prefixWord ++ tailWord_313901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_313926 : List Nat := [6, 1, 1, 1, 2, 3, 7]
def baseStart_313926 : Nat := 118140960795 + 313926 * 2 ^ 59
def prefixEnd_313926 : Nat := 4983230072969 + 3 ^ 40 * 313926 * 2
def baseEnd_313926 : Nat := 7960243355231802310187

theorem tailTrace_313926 : CollatzResearch.WordTrace tailWord_313926 prefixEnd_313926 7960243355231802310187 := by
  unfold tailWord_313926
  simp only [CollatzResearch.WordTrace]
  refine ⟨357806933147099723045551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 7633214573804794091638421 357806933147099723045551)
  ·
    refine ⟨536710399720649584568327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 357806933147099723045551 536710399720649584568327)
    ·
      refine ⟨805065599580974376852491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 536710399720649584568327 805065599580974376852491)
      ·
        refine ⟨1207598399371461565278737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 805065599580974376852491 1207598399371461565278737)
        ·
          refine ⟨905698799528596173959053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1207598399371461565278737 905698799528596173959053)
          ·
            refine ⟨339637049823223565234645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 905698799528596173959053 339637049823223565234645)
            ·
              refine ⟨7960243355231802310187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 339637049823223565234645 7960243355231802310187)
              ·
                rfl

theorem cell21_313926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 3, 7].length) (baseStart_313926 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_313926 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_313926 prefixEnd_313926 := by exact prefixLift 313926
  have htrace : WordTrace (prefixWord ++ tailWord_313926) baseStart_313926 baseEnd_313926 := by
    simpa [prefixWord, tailWord_313926, baseEnd_313926] using wordTrace_append hprefix tailTrace_313926
  have hstable : (prefixWord ++ tailWord_313926).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_313926).length < 2 ^ (prefixWord ++ tailWord_313926).sum := by decide
  have hdescent : baseEnd_313926 < baseStart_313926 := by decide
  rcases family_descends (prefixWord ++ tailWord_313926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_313937 : List Nat := [1, 2, 2, 1, 3, 3, 2, 1, 6]
def baseStart_313937 : Nat := 118140960795 + 313937 * 2 ^ 59
def prefixEnd_313937 : Nat := 4983230072969 + 3 ^ 40 * 313937 * 2
def baseEnd_313937 : Nat := 71644700546952646108327

theorem tailTrace_313937 : CollatzResearch.WordTrace tailWord_313937 prefixEnd_313937 71644700546952646108327 := by
  unfold tailWord_313937
  simp only [CollatzResearch.WordTrace]
  refine ⟨11450223063667340016108065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7633482042444893344072043 11450223063667340016108065)
  ·
    refine ⟨8587667297750505012081049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11450223063667340016108065 8587667297750505012081049)
    ·
      refine ⟨6440750473312878759060787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8587667297750505012081049 6440750473312878759060787)
      ·
        refine ⟨9661125709969318138591181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6440750473312878759060787 9661125709969318138591181)
        ·
          refine ⟨3622922141238494301971693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9661125709969318138591181 3622922141238494301971693)
          ·
            refine ⟨1358595802964435363239385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3622922141238494301971693 1358595802964435363239385)
            ·
              refine ⟨1018946852223326522429539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1358595802964435363239385 1018946852223326522429539)
              ·
                refine ⟨1528420278334989783644309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1018946852223326522429539 1528420278334989783644309)
                ·
                  refine ⟨71644700546952646108327, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1528420278334989783644309 71644700546952646108327)
                  ·
                    rfl

theorem cell21_313937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 2, 1, 6].length) (baseStart_313937 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_313937 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_313937 prefixEnd_313937 := by exact prefixLift 313937
  have htrace : WordTrace (prefixWord ++ tailWord_313937) baseStart_313937 baseEnd_313937 := by
    simpa [prefixWord, tailWord_313937, baseEnd_313937] using wordTrace_append hprefix tailTrace_313937
  have hstable : (prefixWord ++ tailWord_313937).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_313937).length < 2 ^ (prefixWord ++ tailWord_313937).sum := by decide
  have hdescent : baseEnd_313937 < baseStart_313937 := by decide
  rcases family_descends (prefixWord ++ tailWord_313937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_313940 : List Nat := [2, 4, 1, 1, 1, 5, 1, 1, 5]
def baseStart_313940 : Nat := 118140960795 + 313940 * 2 ^ 59
def prefixEnd_313940 : Nat := 4983230072969 + 3 ^ 40 * 313940 * 2
def baseEnd_313940 : Nat := 71645385187825307558321

theorem tailTrace_313940 : CollatzResearch.WordTrace tailWord_313940 prefixEnd_313940 71645385187825307558321 := by
  unfold tailWord_313940
  simp only [CollatzResearch.WordTrace]
  refine ⟨5725166241328235764233637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7633554988437647685644849 5725166241328235764233637)
  ·
    refine ⟨1073468670249044205793807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5725166241328235764233637 1073468670249044205793807)
    ·
      refine ⟨1610203005373566308690711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1073468670249044205793807 1610203005373566308690711)
      ·
        refine ⟨2415304508060349463036067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1610203005373566308690711 2415304508060349463036067)
        ·
          refine ⟨3622956762090524194554101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2415304508060349463036067 3622956762090524194554101)
          ·
            refine ⟨339652196445986643239447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 3622956762090524194554101 339652196445986643239447)
            ·
              refine ⟨509478294668979964859171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 339652196445986643239447 509478294668979964859171)
              ·
                refine ⟨764217442003469947288757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 509478294668979964859171 764217442003469947288757)
                ·
                  refine ⟨71645385187825307558321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 764217442003469947288757 71645385187825307558321)
                  ·
                    rfl

theorem cell21_313940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 5, 1, 1, 5].length) (baseStart_313940 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_313940 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_313940 prefixEnd_313940 := by exact prefixLift 313940
  have htrace : WordTrace (prefixWord ++ tailWord_313940) baseStart_313940 baseEnd_313940 := by
    simpa [prefixWord, tailWord_313940, baseEnd_313940] using wordTrace_append hprefix tailTrace_313940
  have hstable : (prefixWord ++ tailWord_313940).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_313940).length < 2 ^ (prefixWord ++ tailWord_313940).sum := by decide
  have hdescent : baseEnd_313940 < baseStart_313940 := by decide
  rcases family_descends (prefixWord ++ tailWord_313940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_313999 : List Nat := [1, 1, 2, 1, 1, 1, 1, 10, 3]
def baseStart_313999 : Nat := 118140960795 + 313999 * 2 ^ 59
def prefixEnd_313999 : Nat := 4983230072969 + 3 ^ 40 * 313999 * 2
def baseEnd_313999 : Nat := 71658849791654316074867

theorem tailTrace_313999 : CollatzResearch.WordTrace tailWord_313999 prefixEnd_313999 71658849791654316074867 := by
  unfold tailWord_313999
  simp only [CollatzResearch.WordTrace]
  refine ⟨11452484389442724604865051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7634989592961816403243367 11452484389442724604865051)
  ·
    refine ⟨17178726584164086907297577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11452484389442724604865051 17178726584164086907297577)
    ·
      refine ⟨12884044938123065180473183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17178726584164086907297577 12884044938123065180473183)
      ·
        refine ⟨19326067407184597770709775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12884044938123065180473183 19326067407184597770709775)
        ·
          refine ⟨28989101110776896656064663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19326067407184597770709775 28989101110776896656064663)
          ·
            refine ⟨43483651666165344984096995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28989101110776896656064663 43483651666165344984096995)
            ·
              refine ⟨65225477499248017476145493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43483651666165344984096995 65225477499248017476145493)
              ·
                refine ⟨191090266111078176199645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 65225477499248017476145493 191090266111078176199645)
                ·
                  refine ⟨71658849791654316074867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 191090266111078176199645 71658849791654316074867)
                  ·
                    rfl

theorem cell21_313999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 10, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 10, 3].length) (baseStart_313999 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_313999 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_313999 prefixEnd_313999 := by exact prefixLift 313999
  have htrace : WordTrace (prefixWord ++ tailWord_313999) baseStart_313999 baseEnd_313999 := by
    simpa [prefixWord, tailWord_313999, baseEnd_313999] using wordTrace_append hprefix tailTrace_313999
  have hstable : (prefixWord ++ tailWord_313999).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_313999).length < 2 ^ (prefixWord ++ tailWord_313999).sum := by decide
  have hdescent : baseEnd_313999 < baseStart_313999 := by decide
  rcases family_descends (prefixWord ++ tailWord_313999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_314120 : List Nat := [2, 1, 3, 2, 2, 3, 2, 6]
def baseStart_314120 : Nat := 118140960795 + 314120 * 2 ^ 59
def prefixEnd_314120 : Nat := 4983230072969 + 3 ^ 40 * 314120 * 2
def baseEnd_314120 : Nat := 23895487880061664852651

theorem tailTrace_314120 : CollatzResearch.WordTrace tailWord_314120 prefixEnd_314120 23895487880061664852651 := by
  unfold tailWord_314120
  simp only [CollatzResearch.WordTrace]
  refine ⟨5728448811002181135009907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7637931748002908180013209 5728448811002181135009907)
  ·
    refine ⟨8592673216503271702514861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5728448811002181135009907 8592673216503271702514861)
    ·
      refine ⟨3222252456188726888443073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8592673216503271702514861 3222252456188726888443073)
      ·
        refine ⟨2416689342141545166332305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3222252456188726888443073 2416689342141545166332305)
        ·
          refine ⟨1812517006606158874749229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2416689342141545166332305 1812517006606158874749229)
          ·
            refine ⟨679693877477309578030961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1812517006606158874749229 679693877477309578030961)
            ·
              refine ⟨509770408107982183523221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 679693877477309578030961 509770408107982183523221)
              ·
                refine ⟨23895487880061664852651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 509770408107982183523221 23895487880061664852651)
                ·
                  rfl

theorem cell21_314120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 3, 2, 6].length) (baseStart_314120 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_314120 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_314120 prefixEnd_314120 := by exact prefixLift 314120
  have htrace : WordTrace (prefixWord ++ tailWord_314120) baseStart_314120 baseEnd_314120 := by
    simpa [prefixWord, tailWord_314120, baseEnd_314120] using wordTrace_append hprefix tailTrace_314120
  have hstable : (prefixWord ++ tailWord_314120).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_314120).length < 2 ^ (prefixWord ++ tailWord_314120).sum := by decide
  have hdescent : baseEnd_314120 < baseStart_314120 := by decide
  rcases family_descends (prefixWord ++ tailWord_314120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_314227 : List Nat := [1, 1, 1, 2, 2, 1, 6, 4, 3]
def baseStart_314227 : Nat := 118140960795 + 314227 * 2 ^ 59
def prefixEnd_314227 : Nat := 4983230072969 + 3 ^ 40 * 314227 * 2
def baseEnd_314227 : Nat := 71710882497976586274401

theorem tailTrace_314227 : CollatzResearch.WordTrace tailWord_314227 prefixEnd_314227 71710882497976586274401 := by
  unfold tailWord_314227
  simp only [CollatzResearch.WordTrace]
  refine ⟨11460800232616719544164935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7640533488411146362776623 11460800232616719544164935)
  ·
    refine ⟨17191200348925079316247403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11460800232616719544164935 17191200348925079316247403)
    ·
      refine ⟨25786800523387618974371105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17191200348925079316247403 25786800523387618974371105)
      ·
        refine ⟨19340100392540714230778329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25786800523387618974371105 19340100392540714230778329)
        ·
          refine ⟨14505075294405535673083747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19340100392540714230778329 14505075294405535673083747)
          ·
            refine ⟨21757612941608303509625621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14505075294405535673083747 21757612941608303509625621)
            ·
              refine ⟨1019888106637889227013701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 21757612941608303509625621 1019888106637889227013701)
              ·
                refine ⟨191229019994604230065069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1019888106637889227013701 191229019994604230065069)
                ·
                  refine ⟨71710882497976586274401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 191229019994604230065069 71710882497976586274401)
                  ·
                    rfl

theorem cell21_314227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 6, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 6, 4, 3].length) (baseStart_314227 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_314227 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_314227 prefixEnd_314227 := by exact prefixLift 314227
  have htrace : WordTrace (prefixWord ++ tailWord_314227) baseStart_314227 baseEnd_314227 := by
    simpa [prefixWord, tailWord_314227, baseEnd_314227] using wordTrace_append hprefix tailTrace_314227
  have hstable : (prefixWord ++ tailWord_314227).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_314227).length < 2 ^ (prefixWord ++ tailWord_314227).sum := by decide
  have hdescent : baseEnd_314227 < baseStart_314227 := by decide
  rcases family_descends (prefixWord ++ tailWord_314227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_314292 : List Nat := [2, 5, 2, 1, 1, 1, 4, 1, 4]
def baseStart_314292 : Nat := 118140960795 + 314292 * 2 ^ 59
def prefixEnd_314292 : Nat := 4983230072969 + 3 ^ 40 * 314292 * 2
def baseEnd_314292 : Nat := 71725716383550917690935

theorem tailTrace_314292 : CollatzResearch.WordTrace tailWord_314292 prefixEnd_314292 71725716383550917690935 := by
  unfold tailWord_314292
  simp only [CollatzResearch.WordTrace]
  refine ⟨5731585488690617822640565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7642113984920823763520753 5731585488690617822640565)
  ·
    refine ⟨537336139564745420872553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 5731585488690617822640565 537336139564745420872553)
    ·
      refine ⟨403002104673559065654415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 537336139564745420872553 403002104673559065654415)
      ·
        refine ⟨604503157010338598481623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 403002104673559065654415 604503157010338598481623)
        ·
          refine ⟨906754735515507897722435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 604503157010338598481623 906754735515507897722435)
          ·
            refine ⟨1360132103273261846583653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 906754735515507897722435 1360132103273261846583653)
            ·
              refine ⟨255024769363736596234435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1360132103273261846583653 255024769363736596234435)
              ·
                refine ⟨382537154045604894351653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 255024769363736596234435 382537154045604894351653)
                ·
                  refine ⟨71725716383550917690935, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 382537154045604894351653 71725716383550917690935)
                  ·
                    rfl

theorem cell21_314292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 4, 1, 4].length) (baseStart_314292 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_314292 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_314292 prefixEnd_314292 := by exact prefixLift 314292
  have htrace : WordTrace (prefixWord ++ tailWord_314292) baseStart_314292 baseEnd_314292 := by
    simpa [prefixWord, tailWord_314292, baseEnd_314292] using wordTrace_append hprefix tailTrace_314292
  have hstable : (prefixWord ++ tailWord_314292).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_314292).length < 2 ^ (prefixWord ++ tailWord_314292).sum := by decide
  have hdescent : baseEnd_314292 < baseStart_314292 := by decide
  rcases family_descends (prefixWord ++ tailWord_314292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_314345 : List Nat := [1, 2, 1, 1, 1, 2, 1, 1, 11]
def baseStart_314345 : Nat := 118140960795 + 314345 * 2 ^ 59
def prefixEnd_314345 : Nat := 4983230072969 + 3 ^ 40 * 314345 * 2
def baseEnd_314345 : Nat := 71737811705634603307493

theorem tailTrace_314345 : CollatzResearch.WordTrace tailWord_314345 prefixEnd_314345 71737811705634603307493 := by
  unfold tailWord_314345
  simp only [CollatzResearch.WordTrace]
  refine ⟨11465104046189225696960489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7643402697459483797973659 11465104046189225696960489)
  ·
    refine ⟨8598828034641919272720367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11465104046189225696960489 8598828034641919272720367)
    ·
      refine ⟨12898242051962878909080551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8598828034641919272720367 12898242051962878909080551)
      ·
        refine ⟨19347363077944318363620827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12898242051962878909080551 19347363077944318363620827)
        ·
          refine ⟨29021044616916477545431241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19347363077944318363620827 29021044616916477545431241)
          ·
            refine ⟨21765783462687358159073431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29021044616916477545431241 21765783462687358159073431)
            ·
              refine ⟨32648675194031037238610147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21765783462687358159073431 32648675194031037238610147)
              ·
                refine ⟨48973012791046555857915221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32648675194031037238610147 48973012791046555857915221)
                ·
                  refine ⟨71737811705634603307493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 48973012791046555857915221 71737811705634603307493)
                  ·
                    rfl

theorem cell21_314345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 1, 11].length) (baseStart_314345 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_314345 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_314345 prefixEnd_314345 := by exact prefixLift 314345
  have htrace : WordTrace (prefixWord ++ tailWord_314345) baseStart_314345 baseEnd_314345 := by
    simpa [prefixWord, tailWord_314345, baseEnd_314345] using wordTrace_append hprefix tailTrace_314345
  have hstable : (prefixWord ++ tailWord_314345).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_314345).length < 2 ^ (prefixWord ++ tailWord_314345).sum := by decide
  have hdescent : baseEnd_314345 < baseStart_314345 := by decide
  rcases family_descends (prefixWord ++ tailWord_314345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_314379 : List Nat := [1, 1, 1, 1, 6, 2, 1, 5, 3]
def baseStart_314379 : Nat := 118140960795 + 314379 * 2 ^ 59
def prefixEnd_314379 : Nat := 4983230072969 + 3 ^ 40 * 314379 * 2
def baseEnd_314379 : Nat := 71745570968858099740757

theorem tailTrace_314379 : CollatzResearch.WordTrace tailWord_314379 prefixEnd_314379 71745570968858099740757 := by
  unfold tailWord_314379
  simp only [CollatzResearch.WordTrace]
  refine ⟨11466344128066049503698191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7644229418710699669132127 11466344128066049503698191)
  ·
    refine ⟨17199516192099074255547287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11466344128066049503698191 17199516192099074255547287)
    ·
      refine ⟨25799274288148611383320931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17199516192099074255547287 25799274288148611383320931)
      ·
        refine ⟨38698911432222917074981397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25799274288148611383320931 38698911432222917074981397)
        ·
          refine ⟨1814011473385449237889753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 38698911432222917074981397 1814011473385449237889753)
          ·
            refine ⟨1360508605039086928417315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1814011473385449237889753 1360508605039086928417315)
            ·
              refine ⟨2040762907558630392625973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1360508605039086928417315 2040762907558630392625973)
              ·
                refine ⟨191321522583621599308685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2040762907558630392625973 191321522583621599308685)
                ·
                  refine ⟨71745570968858099740757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 191321522583621599308685 71745570968858099740757)
                  ·
                    rfl

theorem cell21_314379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 1, 5, 3].length) (baseStart_314379 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_314379 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_314379 prefixEnd_314379 := by exact prefixLift 314379
  have htrace : WordTrace (prefixWord ++ tailWord_314379) baseStart_314379 baseEnd_314379 := by
    simpa [prefixWord, tailWord_314379, baseEnd_314379] using wordTrace_append hprefix tailTrace_314379
  have hstable : (prefixWord ++ tailWord_314379).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_314379).length < 2 ^ (prefixWord ++ tailWord_314379).sum := by decide
  have hdescent : baseEnd_314379 < baseStart_314379 := by decide
  rcases family_descends (prefixWord ++ tailWord_314379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_314393 : List Nat := [1, 2, 1, 2, 1, 1, 7, 2, 4]
def baseStart_314393 : Nat := 118140960795 + 314393 * 2 ^ 59
def prefixEnd_314393 : Nat := 4983230072969 + 3 ^ 40 * 314393 * 2
def baseEnd_314393 : Nat := 71748765959597186507395

theorem tailTrace_314393 : CollatzResearch.WordTrace tailWord_314393 prefixEnd_314393 71748765959597186507395 := by
  unfold tailWord_314393
  simp only [CollatzResearch.WordTrace]
  refine ⟨11466854750015329894707833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7644569833343553263138555 11466854750015329894707833)
  ·
    refine ⟨8600141062511497421030875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11466854750015329894707833 8600141062511497421030875)
    ·
      refine ⟨12900211593767246131546313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8600141062511497421030875 12900211593767246131546313)
      ·
        refine ⟨9675158695325434598659735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12900211593767246131546313 9675158695325434598659735)
        ·
          refine ⟨14512738042988151897989603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9675158695325434598659735 14512738042988151897989603)
          ·
            refine ⟨21769107064482227846984405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14512738042988151897989603 21769107064482227846984405)
            ·
              refine ⟨510213446823802215163697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 21769107064482227846984405 510213446823802215163697)
              ·
                refine ⟨382660085117851661372773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 510213446823802215163697 382660085117851661372773)
                ·
                  refine ⟨71748765959597186507395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 382660085117851661372773 71748765959597186507395)
                  ·
                    rfl

theorem cell21_314393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 7, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 7, 2, 4].length) (baseStart_314393 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_314393 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_314393 prefixEnd_314393 := by exact prefixLift 314393
  have htrace : WordTrace (prefixWord ++ tailWord_314393) baseStart_314393 baseEnd_314393 := by
    simpa [prefixWord, tailWord_314393, baseEnd_314393] using wordTrace_append hprefix tailTrace_314393
  have hstable : (prefixWord ++ tailWord_314393).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_314393).length < 2 ^ (prefixWord ++ tailWord_314393).sum := by decide
  have hdescent : baseEnd_314393 < baseStart_314393 := by decide
  rcases family_descends (prefixWord ++ tailWord_314393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_314424 : List Nat := [2, 1, 2, 1, 5, 1, 4, 5]
def baseStart_314424 : Nat := 118140960795 + 314424 * 2 ^ 59
def prefixEnd_314424 : Nat := 4983230072969 + 3 ^ 40 * 314424 * 2
def baseEnd_314424 : Nat := 23918613527316007163555

theorem tailTrace_314424 : CollatzResearch.WordTrace tailWord_314424 prefixEnd_314424 23918613527316007163555 := by
  unfold tailWord_314424
  simp only [CollatzResearch.WordTrace]
  refine ⟨5733992706451511094543163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7645323608602014792724217 5733992706451511094543163)
  ·
    refine ⟨8600989059677266641814745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5733992706451511094543163 8600989059677266641814745)
    ·
      refine ⟨6450741794757949981361059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8600989059677266641814745 6450741794757949981361059)
      ·
        refine ⟨9676112692136924972041589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6450741794757949981361059 9676112692136924972041589)
        ·
          refine ⟨907135564887836716128899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 9676112692136924972041589 907135564887836716128899)
          ·
            refine ⟨1360703347331755074193349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 907135564887836716128899 1360703347331755074193349)
            ·
              refine ⟨255131877624704076411253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1360703347331755074193349 255131877624704076411253)
              ·
                refine ⟨23918613527316007163555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 255131877624704076411253 23918613527316007163555)
                ·
                  rfl

theorem cell21_314424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 4, 5].length) (baseStart_314424 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_314424 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_314424 prefixEnd_314424 := by exact prefixLift 314424
  have htrace : WordTrace (prefixWord ++ tailWord_314424) baseStart_314424 baseEnd_314424 := by
    simpa [prefixWord, tailWord_314424, baseEnd_314424] using wordTrace_append hprefix tailTrace_314424
  have hstable : (prefixWord ++ tailWord_314424).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_314424).length < 2 ^ (prefixWord ++ tailWord_314424).sum := by decide
  have hdescent : baseEnd_314424 < baseStart_314424 := by decide
  rcases family_descends (prefixWord ++ tailWord_314424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_314461 : List Nat := [1, 4, 4, 1, 3, 1, 2, 1, 4]
def baseStart_314461 : Nat := 118140960795 + 314461 * 2 ^ 59
def prefixEnd_314461 : Nat := 4983230072969 + 3 ^ 40 * 314461 * 2
def baseEnd_314461 : Nat := 71764284486044179373923

theorem tailTrace_314461 : CollatzResearch.WordTrace tailWord_314461 prefixEnd_314461 71764284486044179373923 := by
  unfold tailWord_314461
  simp only [CollatzResearch.WordTrace]
  refine ⟨11469334913768977508183237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7646223275845985005455491 11469334913768977508183237)
  ·
    refine ⟨2150500296331683282784357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11469334913768977508183237 2150500296331683282784357)
    ·
      refine ⟨403218805562190615522067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2150500296331683282784357 403218805562190615522067)
      ·
        refine ⟨604828208343285923283101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 403218805562190615522067 604828208343285923283101)
        ·
          refine ⟨226810578128732221231163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 604828208343285923283101 226810578128732221231163)
          ·
            refine ⟨340215867193098331846745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 226810578128732221231163 340215867193098331846745)
            ·
              refine ⟨255161900394823748885059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 340215867193098331846745 255161900394823748885059)
              ·
                refine ⟨382742850592235623327589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 255161900394823748885059 382742850592235623327589)
                ·
                  refine ⟨71764284486044179373923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 382742850592235623327589 71764284486044179373923)
                  ·
                    rfl

theorem cell21_314461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 3, 1, 2, 1, 4].length) (baseStart_314461 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_314461 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_314461 prefixEnd_314461 := by exact prefixLift 314461
  have htrace : WordTrace (prefixWord ++ tailWord_314461) baseStart_314461 baseEnd_314461 := by
    simpa [prefixWord, tailWord_314461, baseEnd_314461] using wordTrace_append hprefix tailTrace_314461
  have hstable : (prefixWord ++ tailWord_314461).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_314461).length < 2 ^ (prefixWord ++ tailWord_314461).sum := by decide
  have hdescent : baseEnd_314461 < baseStart_314461 := by decide
  rcases family_descends (prefixWord ++ tailWord_314461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_314469 : List Nat := [1, 3, 1, 3, 2, 1, 3, 3, 4]
def baseStart_314469 : Nat := 118140960795 + 314469 * 2 ^ 59
def prefixEnd_314469 : Nat := 4983230072969 + 3 ^ 40 * 314469 * 2
def baseEnd_314469 : Nat := 71766110195037943240573

theorem tailTrace_314469 : CollatzResearch.WordTrace tailWord_314469 prefixEnd_314469 71766110195037943240573 := by
  unfold tailWord_314469
  simp only [CollatzResearch.WordTrace]
  refine ⟨11469626697739994874474461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7646417798493329916316307 11469626697739994874474461)
  ·
    refine ⟨4301110011652498077927923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11469626697739994874474461 4301110011652498077927923)
    ·
      refine ⟨6451665017478747116891885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4301110011652498077927923 6451665017478747116891885)
      ·
        refine ⟨2419374381554530168834457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6451665017478747116891885 2419374381554530168834457)
        ·
          refine ⟨1814530786165897626625843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2419374381554530168834457 1814530786165897626625843)
          ·
            refine ⟨2721796179248846439938765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1814530786165897626625843 2721796179248846439938765)
            ·
              refine ⟨1020673567218317414977037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2721796179248846439938765 1020673567218317414977037)
              ·
                refine ⟨382752587706869030616389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1020673567218317414977037 382752587706869030616389)
                ·
                  refine ⟨71766110195037943240573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 382752587706869030616389 71766110195037943240573)
                  ·
                    rfl

theorem cell21_314469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 3, 3, 4].length) (baseStart_314469 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_314469 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_314469 prefixEnd_314469 := by exact prefixLift 314469
  have htrace : WordTrace (prefixWord ++ tailWord_314469) baseStart_314469 baseEnd_314469 := by
    simpa [prefixWord, tailWord_314469, baseEnd_314469] using wordTrace_append hprefix tailTrace_314469
  have hstable : (prefixWord ++ tailWord_314469).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_314469).length < 2 ^ (prefixWord ++ tailWord_314469).sum := by decide
  have hdescent : baseEnd_314469 < baseStart_314469 := by decide
  rcases family_descends (prefixWord ++ tailWord_314469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_314604 : List Nat := [2, 2, 1, 1, 2, 4, 1, 2, 6]
def baseStart_314604 : Nat := 118140960795 + 314604 * 2 ^ 59
def prefixEnd_314604 : Nat := 4983230072969 + 3 ^ 40 * 314604 * 2
def baseEnd_314604 : Nat := 71796919034307708490297

theorem tailTrace_314604 : CollatzResearch.WordTrace tailWord_314604 prefixEnd_314604 71796919034307708490297 := by
  unfold tailWord_314604
  simp only [CollatzResearch.WordTrace]
  refine ⟨5737275276125456465319433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7649700368167275287092577 5737275276125456465319433)
  ·
    refine ⟨4302956457094092348989575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5737275276125456465319433 4302956457094092348989575)
    ·
      refine ⟨6454434685641138523484363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4302956457094092348989575 6454434685641138523484363)
      ·
        refine ⟨9681652028461707785226545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6454434685641138523484363 9681652028461707785226545)
        ·
          refine ⟨7261239021346280838919909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9681652028461707785226545 7261239021346280838919909)
          ·
            refine ⟨1361482316502427657297483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7261239021346280838919909 1361482316502427657297483)
            ·
              refine ⟨2042223474753641485946225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1361482316502427657297483 2042223474753641485946225)
              ·
                refine ⟨1531667606065231114459669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2042223474753641485946225 1531667606065231114459669)
                ·
                  refine ⟨71796919034307708490297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1531667606065231114459669 71796919034307708490297)
                  ·
                    rfl

theorem cell21_314604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 6].length) (baseStart_314604 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_314604 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_314604 prefixEnd_314604 := by exact prefixLift 314604
  have htrace : WordTrace (prefixWord ++ tailWord_314604) baseStart_314604 baseEnd_314604 := by
    simpa [prefixWord, tailWord_314604, baseEnd_314604] using wordTrace_append hprefix tailTrace_314604
  have hstable : (prefixWord ++ tailWord_314604).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_314604).length < 2 ^ (prefixWord ++ tailWord_314604).sum := by decide
  have hdescent : baseEnd_314604 < baseStart_314604 := by decide
  rcases family_descends (prefixWord ++ tailWord_314604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_314635 : List Nat := [1, 1, 1, 1, 5, 4, 2, 6]
def baseStart_314635 : Nat := 118140960795 + 314635 * 2 ^ 59
def prefixEnd_314635 : Nat := 4983230072969 + 3 ^ 40 * 314635 * 2
def baseEnd_314635 : Nat := 23934664552219514491189

theorem tailTrace_314635 : CollatzResearch.WordTrace tailWord_314635 prefixEnd_314635 23934664552219514491189 := by
  unfold tailWord_314635
  simp only [CollatzResearch.WordTrace]
  refine ⟨11475681215138605225017359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7650454143425736816678239 11475681215138605225017359)
  ·
    refine ⟨17213521822707907837526039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11475681215138605225017359 17213521822707907837526039)
    ·
      refine ⟨25820282734061861756289059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17213521822707907837526039 25820282734061861756289059)
      ·
        refine ⟨38730424101092792634433589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25820282734061861756289059 38730424101092792634433589)
        ·
          refine ⟨3630977259477449309478149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 38730424101092792634433589 3630977259477449309478149)
          ·
            refine ⟨680808236152021745527153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3630977259477449309478149 680808236152021745527153)
            ·
              refine ⟨510606177114016309145365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 680808236152021745527153 510606177114016309145365)
              ·
                refine ⟨23934664552219514491189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 510606177114016309145365 23934664552219514491189)
                ·
                  rfl

theorem cell21_314635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 4, 2, 6].length) (baseStart_314635 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_314635 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_314635 prefixEnd_314635 := by exact prefixLift 314635
  have htrace : WordTrace (prefixWord ++ tailWord_314635) baseStart_314635 baseEnd_314635 := by
    simpa [prefixWord, tailWord_314635, baseEnd_314635] using wordTrace_append hprefix tailTrace_314635
  have hstable : (prefixWord ++ tailWord_314635).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_314635).length < 2 ^ (prefixWord ++ tailWord_314635).sum := by decide
  have hdescent : baseEnd_314635 < baseStart_314635 := by decide
  rcases family_descends (prefixWord ++ tailWord_314635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_314638 : List Nat := [4, 1, 1, 2, 1, 3, 4, 1, 4]
def baseStart_314638 : Nat := 118140960795 + 314638 * 2 ^ 59
def prefixEnd_314638 : Nat := 4983230072969 + 3 ^ 40 * 314638 * 2
def baseEnd_314638 : Nat := 71804678297531204923561

theorem tailTrace_314638 : CollatzResearch.WordTrace tailWord_314638 prefixEnd_314638 71804678297531204923561 := by
  unfold tailWord_314638
  simp only [CollatzResearch.WordTrace]
  refine ⟨1434473829265967092172071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7650527089418491158251045 1434473829265967092172071)
  ·
    refine ⟨2151710743898950638258107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1434473829265967092172071 2151710743898950638258107)
    ·
      refine ⟨3227566115848425957387161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2151710743898950638258107 3227566115848425957387161)
      ·
        refine ⟨2420674586886319468040371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3227566115848425957387161 2420674586886319468040371)
        ·
          refine ⟨3631011880329479202060557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2420674586886319468040371 3631011880329479202060557)
          ·
            refine ⟨1361629455123554700772709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3631011880329479202060557 1361629455123554700772709)
            ·
              refine ⟨255305522835666506394883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1361629455123554700772709 255305522835666506394883)
              ·
                refine ⟨382958284253499759592325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 255305522835666506394883 382958284253499759592325)
                ·
                  refine ⟨71804678297531204923561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 382958284253499759592325 71804678297531204923561)
                  ·
                    rfl

theorem cell21_314638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 4, 1, 4].length) (baseStart_314638 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_314638 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_314638 prefixEnd_314638 := by exact prefixLift 314638
  have htrace : WordTrace (prefixWord ++ tailWord_314638) baseStart_314638 baseEnd_314638 := by
    simpa [prefixWord, tailWord_314638, baseEnd_314638] using wordTrace_append hprefix tailTrace_314638
  have hstable : (prefixWord ++ tailWord_314638).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_314638).length < 2 ^ (prefixWord ++ tailWord_314638).sum := by decide
  have hdescent : baseEnd_314638 < baseStart_314638 := by decide
  rcases family_descends (prefixWord ++ tailWord_314638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_314725 : List Nat := [1, 3, 1, 3, 1, 2, 1, 2, 7]
def baseStart_314725 : Nat := 118140960795 + 314725 * 2 ^ 59
def prefixEnd_314725 : Nat := 4983230072969 + 3 ^ 40 * 314725 * 2
def baseEnd_314725 : Nat := 71824532882838386973383

theorem tailTrace_314725 : CollatzResearch.WordTrace tailWord_314725 prefixEnd_314725 71824532882838386973383 := by
  unfold tailWord_314725
  simp only [CollatzResearch.WordTrace]
  refine ⟨11478963784812550595793629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7652642523208367063862419 11478963784812550595793629)
  ·
    refine ⟨4304611419304706473422611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11478963784812550595793629 4304611419304706473422611)
    ·
      refine ⟨6456917128957059710133917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4304611419304706473422611 6456917128957059710133917)
      ·
        refine ⟨2421343923358897391300219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6456917128957059710133917 2421343923358897391300219)
        ·
          refine ⟨3632015885038346086950329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2421343923358897391300219 3632015885038346086950329)
          ·
            refine ⟨2724011913778759565212747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3632015885038346086950329 2724011913778759565212747)
            ·
              refine ⟨4086017870668139347819121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2724011913778759565212747 4086017870668139347819121)
              ·
                refine ⟨3064513403001104510864341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4086017870668139347819121 3064513403001104510864341)
                ·
                  refine ⟨71824532882838386973383, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3064513403001104510864341 71824532882838386973383)
                  ·
                    rfl

theorem cell21_314725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 1, 2, 7].length) (baseStart_314725 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_314725 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_314725 prefixEnd_314725 := by exact prefixLift 314725
  have htrace : WordTrace (prefixWord ++ tailWord_314725) baseStart_314725 baseEnd_314725 := by
    simpa [prefixWord, tailWord_314725, baseEnd_314725] using wordTrace_append hprefix tailTrace_314725
  have hstable : (prefixWord ++ tailWord_314725).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_314725).length < 2 ^ (prefixWord ++ tailWord_314725).sum := by decide
  have hdescent : baseEnd_314725 < baseStart_314725 := by decide
  rcases family_descends (prefixWord ++ tailWord_314725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_314849 : List Nat := [1, 2, 3, 1, 2, 4, 2, 2, 4]
def baseStart_314849 : Nat := 118140960795 + 314849 * 2 ^ 59
def prefixEnd_314849 : Nat := 4983230072969 + 3 ^ 40 * 314849 * 2
def baseEnd_314849 : Nat := 71852831372241726906463

theorem tailTrace_314849 : CollatzResearch.WordTrace tailWord_314849 prefixEnd_314849 71852831372241726906463 := by
  unfold tailWord_314849
  simp only [CollatzResearch.WordTrace]
  refine ⟨11483486436363319773307601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7655657624242213182205067 11483486436363319773307601)
  ·
    refine ⟨8612614827272489829980701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11483486436363319773307601 8612614827272489829980701)
    ·
      refine ⟨3229730560227183686242763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8612614827272489829980701 3229730560227183686242763)
      ·
        refine ⟨4844595840340775529364145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3229730560227183686242763 4844595840340775529364145)
        ·
          refine ⟨3633446880255581647023109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4844595840340775529364145 3633446880255581647023109)
          ·
            refine ⟨681271290047921558816833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3633446880255581647023109 681271290047921558816833)
            ·
              refine ⟨510953467535941169112625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 681271290047921558816833 510953467535941169112625)
              ·
                refine ⟨383215100651955876834469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 510953467535941169112625 383215100651955876834469)
                ·
                  refine ⟨71852831372241726906463, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 383215100651955876834469 71852831372241726906463)
                  ·
                    rfl

theorem cell21_314849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 4, 2, 2, 4].length) (baseStart_314849 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_314849 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_314849 prefixEnd_314849 := by exact prefixLift 314849
  have htrace : WordTrace (prefixWord ++ tailWord_314849) baseStart_314849 baseEnd_314849 := by
    simpa [prefixWord, tailWord_314849, baseEnd_314849] using wordTrace_append hprefix tailTrace_314849
  have hstable : (prefixWord ++ tailWord_314849).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_314849).length < 2 ^ (prefixWord ++ tailWord_314849).sum := by decide
  have hdescent : baseEnd_314849 < baseStart_314849 := by decide
  rcases family_descends (prefixWord ++ tailWord_314849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_314877 : List Nat := [1, 4, 1, 1, 1, 4, 1, 1, 7]
def baseStart_314877 : Nat := 118140960795 + 314877 * 2 ^ 59
def prefixEnd_314877 : Nat := 4983230072969 + 3 ^ 40 * 314877 * 2
def baseEnd_314877 : Nat := 71859221353719900439739

theorem tailTrace_314877 : CollatzResearch.WordTrace tailWord_314877 prefixEnd_314877 71859221353719900439739 := by
  unfold tailWord_314877
  simp only [CollatzResearch.WordTrace]
  refine ⟨11484507680261880555326885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7656338453507920370217923 11484507680261880555326885)
  ·
    refine ⟨2153345190049102604123791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11484507680261880555326885 2153345190049102604123791)
    ·
      refine ⟨3230017785073653906185687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2153345190049102604123791 3230017785073653906185687)
      ·
        refine ⟨4845026677610480859278531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3230017785073653906185687 4845026677610480859278531)
        ·
          refine ⟨7267540016415721288917797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4845026677610480859278531 7267540016415721288917797)
          ·
            refine ⟨1362663753077947741672087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7267540016415721288917797 1362663753077947741672087)
            ·
              refine ⟨2043995629616921612508131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1362663753077947741672087 2043995629616921612508131)
              ·
                refine ⟨3065993444425382418762197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2043995629616921612508131 3065993444425382418762197)
                ·
                  refine ⟨71859221353719900439739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3065993444425382418762197 71859221353719900439739)
                  ·
                    rfl

theorem cell21_314877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 1, 1, 7].length) (baseStart_314877 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_314877 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_314877 prefixEnd_314877 := by exact prefixLift 314877
  have htrace : WordTrace (prefixWord ++ tailWord_314877) baseStart_314877 baseEnd_314877 := by
    simpa [prefixWord, tailWord_314877, baseEnd_314877] using wordTrace_append hprefix tailTrace_314877
  have hstable : (prefixWord ++ tailWord_314877).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_314877).length < 2 ^ (prefixWord ++ tailWord_314877).sum := by decide
  have hdescent : baseEnd_314877 < baseStart_314877 := by decide
  rcases family_descends (prefixWord ++ tailWord_314877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_314900 : List Nat := [2, 4, 3, 1, 3, 1, 1, 2, 4]
def baseStart_314900 : Nat := 118140960795 + 314900 * 2 ^ 59
def prefixEnd_314900 : Nat := 4983230072969 + 3 ^ 40 * 314900 * 2
def baseEnd_314900 : Nat := 71864470267076971556359

theorem tailTrace_314900 : CollatzResearch.WordTrace tailWord_314900 prefixEnd_314900 71864470267076971556359 := by
  unfold tailWord_314900
  simp only [CollatzResearch.WordTrace]
  refine ⟨5742673279589277741707077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7656897706119036988942769 5742673279589277741707077)
  ·
    refine ⟨1076751239922989576570077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5742673279589277741707077 1076751239922989576570077)
    ·
      refine ⟨403781714971121091213779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1076751239922989576570077 403781714971121091213779)
      ·
        refine ⟨605672572456681636820669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 403781714971121091213779 605672572456681636820669)
        ·
          refine ⟨227127214671255613807751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 605672572456681636820669 227127214671255613807751)
          ·
            refine ⟨340690822006883420711627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 227127214671255613807751 340690822006883420711627)
            ·
              refine ⟨511036233010325131067441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 340690822006883420711627 511036233010325131067441)
              ·
                refine ⟨383277174757743848300581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 511036233010325131067441 383277174757743848300581)
                ·
                  refine ⟨71864470267076971556359, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 383277174757743848300581 71864470267076971556359)
                  ·
                    rfl

theorem cell21_314900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 3, 1, 1, 2, 4].length) (baseStart_314900 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_314900 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_314900 prefixEnd_314900 := by exact prefixLift 314900
  have htrace : WordTrace (prefixWord ++ tailWord_314900) baseStart_314900 baseEnd_314900 := by
    simpa [prefixWord, tailWord_314900, baseEnd_314900] using wordTrace_append hprefix tailTrace_314900
  have hstable : (prefixWord ++ tailWord_314900).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_314900).length < 2 ^ (prefixWord ++ tailWord_314900).sum := by decide
  have hdescent : baseEnd_314900 < baseStart_314900 := by decide
  rcases family_descends (prefixWord ++ tailWord_314900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_314908 : List Nat := [2, 2, 3, 1, 2, 1, 3, 1, 6]
def baseStart_314908 : Nat := 118140960795 + 314908 * 2 ^ 59
def prefixEnd_314908 : Nat := 4983230072969 + 3 ^ 40 * 314908 * 2
def baseEnd_314908 : Nat := 71866295976070735423009

theorem tailTrace_314908 : CollatzResearch.WordTrace tailWord_314908 prefixEnd_314908 71866295976070735423009 := by
  unfold tailWord_314908
  simp only [CollatzResearch.WordTrace]
  refine ⟨5742819171574786424852689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7657092228766381899803585 5742819171574786424852689)
  ·
    refine ⟨4307114378681089818639517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5742819171574786424852689 4307114378681089818639517)
    ·
      refine ⟨1615167892005408681989819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4307114378681089818639517 1615167892005408681989819)
      ·
        refine ⟨2422751838008113022984729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1615167892005408681989819 2422751838008113022984729)
        ·
          refine ⟨1817063878506084767238547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2422751838008113022984729 1817063878506084767238547)
          ·
            refine ⟨2725595817759127150857821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1817063878506084767238547 2725595817759127150857821)
            ·
              refine ⟨1022098431659672681571683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2725595817759127150857821 1022098431659672681571683)
              ·
                refine ⟨1533147647489509022357525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1022098431659672681571683 1533147647489509022357525)
                ·
                  refine ⟨71866295976070735423009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1533147647489509022357525 71866295976070735423009)
                  ·
                    rfl

theorem cell21_314908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 3, 1, 6].length) (baseStart_314908 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_314908 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_314908 prefixEnd_314908 := by exact prefixLift 314908
  have htrace : WordTrace (prefixWord ++ tailWord_314908) baseStart_314908 baseEnd_314908 := by
    simpa [prefixWord, tailWord_314908, baseEnd_314908] using wordTrace_append hprefix tailTrace_314908
  have hstable : (prefixWord ++ tailWord_314908).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_314908).length < 2 ^ (prefixWord ++ tailWord_314908).sum := by decide
  have hdescent : baseEnd_314908 < baseStart_314908 := by decide
  rcases family_descends (prefixWord ++ tailWord_314908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_314970 : List Nat := [3, 1, 1, 2, 1, 1, 1, 8, 3]
def baseStart_314970 : Nat := 118140960795 + 314970 * 2 ^ 59
def prefixEnd_314970 : Nat := 4983230072969 + 3 ^ 40 * 314970 * 2
def baseEnd_314970 : Nat := 71880445220772405389549

theorem tailTrace_314970 : CollatzResearch.WordTrace tailWord_314970 prefixEnd_314970 71880445220772405389549 := by
  unfold tailWord_314970
  simp only [CollatzResearch.WordTrace]
  refine ⟨2871974917231239359615591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7658599779283304958974909 2871974917231239359615591)
  ·
    refine ⟨4307962375846859039423387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2871974917231239359615591 4307962375846859039423387)
    ·
      refine ⟨6461943563770288559135081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4307962375846859039423387 6461943563770288559135081)
      ·
        refine ⟨4846457672827716419351311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6461943563770288559135081 4846457672827716419351311)
        ·
          refine ⟨7269686509241574629026967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4846457672827716419351311 7269686509241574629026967)
          ·
            refine ⟨10904529763862361943540451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7269686509241574629026967 10904529763862361943540451)
            ·
              refine ⟨16356794645793542915310677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10904529763862361943540451 16356794645793542915310677)
              ·
                refine ⟨191681187255393081038797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 16356794645793542915310677 191681187255393081038797)
                ·
                  refine ⟨71880445220772405389549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 191681187255393081038797 71880445220772405389549)
                  ·
                    rfl

theorem cell21_314970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 8, 3].length) (baseStart_314970 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_314970 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_314970 prefixEnd_314970 := by exact prefixLift 314970
  have htrace : WordTrace (prefixWord ++ tailWord_314970) baseStart_314970 baseEnd_314970 := by
    simpa [prefixWord, tailWord_314970, baseEnd_314970] using wordTrace_append hprefix tailTrace_314970
  have hstable : (prefixWord ++ tailWord_314970).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_314970).length < 2 ^ (prefixWord ++ tailWord_314970).sum := by decide
  have hdescent : baseEnd_314970 < baseStart_314970 := by decide
  rcases family_descends (prefixWord ++ tailWord_314970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_314973 : List Nat := [1, 4, 4, 2, 1, 1, 2, 6]
def baseStart_314973 : Nat := 118140960795 + 314973 * 2 ^ 59
def prefixEnd_314973 : Nat := 4983230072969 + 3 ^ 40 * 314973 * 2
def baseEnd_314973 : Nat := 23960376620548355613181

theorem tailTrace_314973 : CollatzResearch.WordTrace tailWord_314973 prefixEnd_314973 23960376620548355613181 := by
  unfold tailWord_314973
  simp only [CollatzResearch.WordTrace]
  refine ⟨11488009087914088950821573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7658672725276059300547715 11488009087914088950821573)
  ·
    refine ⟨2154001703983891678279045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11488009087914088950821573 2154001703983891678279045)
    ·
      refine ⟨403875319496979689677321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2154001703983891678279045 403875319496979689677321)
      ·
        refine ⟨302906489622734767257991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 403875319496979689677321 302906489622734767257991)
        ·
          refine ⟨454359734434102150886987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 302906489622734767257991 454359734434102150886987)
          ·
            refine ⟨681539601651153226330481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 454359734434102150886987 681539601651153226330481)
            ·
              refine ⟨511154701238364919747861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 681539601651153226330481 511154701238364919747861)
              ·
                refine ⟨23960376620548355613181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 511154701238364919747861 23960376620548355613181)
                ·
                  rfl

theorem cell21_314973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 1, 2, 6].length) (baseStart_314973 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_314973 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_314973 prefixEnd_314973 := by exact prefixLift 314973
  have htrace : WordTrace (prefixWord ++ tailWord_314973) baseStart_314973 baseEnd_314973 := by
    simpa [prefixWord, tailWord_314973, baseEnd_314973] using wordTrace_append hprefix tailTrace_314973
  have hstable : (prefixWord ++ tailWord_314973).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_314973).length < 2 ^ (prefixWord ++ tailWord_314973).sum := by decide
  have hdescent : baseEnd_314973 < baseStart_314973 := by decide
  rcases family_descends (prefixWord ++ tailWord_314973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_315063 : List Nat := [1, 1, 3, 1, 5, 2, 2, 3, 3]
def baseStart_315063 : Nat := 118140960795 + 315063 * 2 ^ 59
def prefixEnd_315063 : Nat := 4983230072969 + 3 ^ 40 * 315063 * 2
def baseEnd_315063 : Nat := 71901669087824910339359

theorem tailTrace_315063 : CollatzResearch.WordTrace tailWord_315063 prefixEnd_315063 71901669087824910339359 := by
  unfold tailWord_315063
  simp only [CollatzResearch.WordTrace]
  refine ⟨11491291657588034321597843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7660861105058689547731895 11491291657588034321597843)
  ·
    refine ⟨17236937486382051482396765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11491291657588034321597843 17236937486382051482396765)
    ·
      refine ⟨6463851557393269305898787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17236937486382051482396765 6463851557393269305898787)
      ·
        refine ⟨9695777336089903958848181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6463851557393269305898787 9695777336089903958848181)
        ·
          refine ⟨908979125258428496142017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 9695777336089903958848181 908979125258428496142017)
          ·
            refine ⟨681734343943821372106513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 908979125258428496142017 681734343943821372106513)
            ·
              refine ⟨511300757957866029079885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 681734343943821372106513 511300757957866029079885)
              ·
                refine ⟨191737784234199760904957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 511300757957866029079885 191737784234199760904957)
                ·
                  refine ⟨71901669087824910339359, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 191737784234199760904957 71901669087824910339359)
                  ·
                    rfl

theorem cell21_315063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 2, 2, 3, 3].length) (baseStart_315063 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_315063 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_315063 prefixEnd_315063 := by exact prefixLift 315063
  have htrace : WordTrace (prefixWord ++ tailWord_315063) baseStart_315063 baseEnd_315063 := by
    simpa [prefixWord, tailWord_315063, baseEnd_315063] using wordTrace_append hprefix tailTrace_315063
  have hstable : (prefixWord ++ tailWord_315063).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_315063).length < 2 ^ (prefixWord ++ tailWord_315063).sum := by decide
  have hdescent : baseEnd_315063 < baseStart_315063 := by decide
  rcases family_descends (prefixWord ++ tailWord_315063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_315119 : List Nat := [1, 1, 2, 1, 5, 1, 1, 1, 8]
def baseStart_315119 : Nat := 118140960795 + 315119 * 2 ^ 59
def prefixEnd_315119 : Nat := 4983230072969 + 3 ^ 40 * 315119 * 2
def baseEnd_315119 : Nat := 71914449050781257405911

theorem tailTrace_315119 : CollatzResearch.WordTrace tailWord_315119 prefixEnd_315119 71914449050781257405911 := by
  unfold tailWord_315119
  simp only [CollatzResearch.WordTrace]
  refine ⟨11493334145385155885636411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7662222763590103923757607 11493334145385155885636411)
  ·
    refine ⟨17240001218077733828454617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11493334145385155885636411 17240001218077733828454617)
    ·
      refine ⟨12930000913558300371340963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17240001218077733828454617 12930000913558300371340963)
      ·
        refine ⟨19395001370337450557011445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12930000913558300371340963 19395001370337450557011445)
        ·
          refine ⟨1818281378469135989719823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 19395001370337450557011445 1818281378469135989719823)
          ·
            refine ⟨2727422067703703984579735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1818281378469135989719823 2727422067703703984579735)
            ·
              refine ⟨4091133101555555976869603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2727422067703703984579735 4091133101555555976869603)
              ·
                refine ⟨6136699652333333965304405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4091133101555555976869603 6136699652333333965304405)
                ·
                  refine ⟨71914449050781257405911, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 6136699652333333965304405 71914449050781257405911)
                  ·
                    rfl

theorem cell21_315119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 1, 1, 8].length) (baseStart_315119 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_315119 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_315119 prefixEnd_315119 := by exact prefixLift 315119
  have htrace : WordTrace (prefixWord ++ tailWord_315119) baseStart_315119 baseEnd_315119 := by
    simpa [prefixWord, tailWord_315119, baseEnd_315119] using wordTrace_append hprefix tailTrace_315119
  have hstable : (prefixWord ++ tailWord_315119).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_315119).length < 2 ^ (prefixWord ++ tailWord_315119).sum := by decide
  have hdescent : baseEnd_315119 < baseStart_315119 := by decide
  rcases family_descends (prefixWord ++ tailWord_315119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_315150 : List Nat := [4, 1, 1, 2, 1, 1, 3, 8]
def baseStart_315150 : Nat := 118140960795 + 315150 * 2 ^ 59
def prefixEnd_315150 : Nat := 4983230072969 + 3 ^ 40 * 315150 * 2
def baseEnd_315150 : Nat := 23973841224377364129727

theorem tailTrace_315150 : CollatzResearch.WordTrace tailWord_315150 prefixEnd_315150 23973841224377364129727 := by
  unfold tailWord_315150
  simp only [CollatzResearch.WordTrace]
  refine ⟨1436808101034106022501863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7662976538848565453343269 1436808101034106022501863)
  ·
    refine ⟨2155212151551159033752795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1436808101034106022501863 2155212151551159033752795)
    ·
      refine ⟨3232818227326738550629193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2155212151551159033752795 3232818227326738550629193)
      ·
        refine ⟨2424613670495053912971895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3232818227326738550629193 2424613670495053912971895)
        ·
          refine ⟨3636920505742580869457843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2424613670495053912971895 3636920505742580869457843)
          ·
            refine ⟨5455380758613871304186765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3636920505742580869457843 5455380758613871304186765)
            ·
              refine ⟨2045767784480201739070037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5455380758613871304186765 2045767784480201739070037)
              ·
                refine ⟨23973841224377364129727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2045767784480201739070037 23973841224377364129727)
                ·
                  rfl

theorem cell21_315150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 3, 8].length) (baseStart_315150 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_315150 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_315150 prefixEnd_315150 := by exact prefixLift 315150
  have htrace : WordTrace (prefixWord ++ tailWord_315150) baseStart_315150 baseEnd_315150 := by
    simpa [prefixWord, tailWord_315150, baseEnd_315150] using wordTrace_append hprefix tailTrace_315150
  have hstable : (prefixWord ++ tailWord_315150).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_315150).length < 2 ^ (prefixWord ++ tailWord_315150).sum := by decide
  have hdescent : baseEnd_315150 < baseStart_315150 := by decide
  rcases family_descends (prefixWord ++ tailWord_315150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_315246 : List Nat := [4, 1, 2, 3, 1, 3, 1, 2, 4]
def baseStart_315246 : Nat := 118140960795 + 315246 * 2 ^ 59
def prefixEnd_315246 : Nat := 4983230072969 + 3 ^ 40 * 315246 * 2
def baseEnd_315246 : Nat := 71943432181057258788985

theorem tailTrace_315246 : CollatzResearch.WordTrace tailWord_315246 prefixEnd_315246 71943432181057258788985 := by
  unfold tailWord_315246
  simp only [CollatzResearch.WordTrace]
  refine ⟨1437245776990632071938699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7665310810616704383673061 1437245776990632071938699)
  ·
    refine ⟨2155868665485948107908049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1437245776990632071938699 2155868665485948107908049)
    ·
      refine ⟨1616901499114461080931037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2155868665485948107908049 1616901499114461080931037)
      ·
        refine ⟨606338062167922905349139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1616901499114461080931037 606338062167922905349139)
        ·
          refine ⟨909507093251884358023709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 606338062167922905349139 909507093251884358023709)
          ·
            refine ⟨341065159969456634258891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 909507093251884358023709 341065159969456634258891)
            ·
              refine ⟨511597739954184951388337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 341065159969456634258891 511597739954184951388337)
              ·
                refine ⟨383698304965638713541253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 511597739954184951388337 383698304965638713541253)
                ·
                  refine ⟨71943432181057258788985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 383698304965638713541253 71943432181057258788985)
                  ·
                    rfl

theorem cell21_315246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 3, 1, 2, 4].length) (baseStart_315246 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_315246 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_315246 prefixEnd_315246 := by exact prefixLift 315246
  have htrace : WordTrace (prefixWord ++ tailWord_315246) baseStart_315246 baseEnd_315246 := by
    simpa [prefixWord, tailWord_315246, baseEnd_315246] using wordTrace_append hprefix tailTrace_315246
  have hstable : (prefixWord ++ tailWord_315246).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_315246).length < 2 ^ (prefixWord ++ tailWord_315246).sum := by decide
  have hdescent : baseEnd_315246 < baseStart_315246 := by decide
  rcases family_descends (prefixWord ++ tailWord_315246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_315257 : List Nat := [1, 2, 1, 3, 2, 2, 4, 1, 5]
def baseStart_315257 : Nat := 118140960795 + 315257 * 2 ^ 59
def prefixEnd_315257 : Nat := 4983230072969 + 3 ^ 40 * 315257 * 2
def baseEnd_315257 : Nat := 71945942530923684105629

theorem tailTrace_315257 : CollatzResearch.WordTrace tailWord_315257 prefixEnd_315257 71945942530923684105629 := by
  unfold tailWord_315257
  simp only [CollatzResearch.WordTrace]
  refine ⟨11498367418885205454160025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7665578279256803636106683 11498367418885205454160025)
  ·
    refine ⟨8623775564163904090620019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11498367418885205454160025 8623775564163904090620019)
    ·
      refine ⟨12935663346245856135930029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8623775564163904090620019 12935663346245856135930029)
      ·
        refine ⟨4850873754842196050973761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12935663346245856135930029 4850873754842196050973761)
        ·
          refine ⟨3638155316131647038230321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4850873754842196050973761 3638155316131647038230321)
          ·
            refine ⟨2728616487098735278672741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3638155316131647038230321 2728616487098735278672741)
            ·
              refine ⟨511615591331012864751139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2728616487098735278672741 511615591331012864751139)
              ·
                refine ⟨767423386996519297126709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 511615591331012864751139 767423386996519297126709)
                ·
                  refine ⟨71945942530923684105629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 767423386996519297126709 71945942530923684105629)
                  ·
                    rfl

theorem cell21_315257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 4, 1, 5].length) (baseStart_315257 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_315257 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_315257 prefixEnd_315257 := by exact prefixLift 315257
  have htrace : WordTrace (prefixWord ++ tailWord_315257) baseStart_315257 baseEnd_315257 := by
    simpa [prefixWord, tailWord_315257, baseEnd_315257] using wordTrace_append hprefix tailTrace_315257
  have hstable : (prefixWord ++ tailWord_315257).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_315257).length < 2 ^ (prefixWord ++ tailWord_315257).sum := by decide
  have hdescent : baseEnd_315257 < baseStart_315257 := by decide
  rcases family_descends (prefixWord ++ tailWord_315257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_315364 : List Nat := [2, 3, 1, 1, 1, 1, 6, 2, 4]
def baseStart_315364 : Nat := 118140960795 + 315364 * 2 ^ 59
def prefixEnd_315364 : Nat := 4983230072969 + 3 ^ 40 * 315364 * 2
def baseEnd_315364 : Nat := 71970361388715275822077

theorem tailTrace_315364 : CollatzResearch.WordTrace tailWord_315364 prefixEnd_315364 71970361388715275822077 := by
  unfold tailWord_315364
  simp only [CollatzResearch.WordTrace]
  refine ⟨5751135014748781364152573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7668180019665041818870097 5751135014748781364152573)
  ·
    refine ⟨2156675630530793011557215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5751135014748781364152573 2156675630530793011557215)
    ·
      refine ⟨3235013445796189517335823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2156675630530793011557215 3235013445796189517335823)
      ·
        refine ⟨4852520168694284276003735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3235013445796189517335823 4852520168694284276003735)
        ·
          refine ⟨7278780253041426414005603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4852520168694284276003735 7278780253041426414005603)
          ·
            refine ⟨10918170379562139621008405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7278780253041426414005603 10918170379562139621008405)
            ·
              refine ⟨511789236541975294734769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 10918170379562139621008405 511789236541975294734769)
              ·
                refine ⟨383841927406481471051077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 511789236541975294734769 383841927406481471051077)
                ·
                  refine ⟨71970361388715275822077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 383841927406481471051077 71970361388715275822077)
                  ·
                    rfl

theorem cell21_315364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 6, 2, 4].length) (baseStart_315364 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_315364 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_315364 prefixEnd_315364 := by exact prefixLift 315364
  have htrace : WordTrace (prefixWord ++ tailWord_315364) baseStart_315364 baseEnd_315364 := by
    simpa [prefixWord, tailWord_315364, baseEnd_315364] using wordTrace_append hprefix tailTrace_315364
  have hstable : (prefixWord ++ tailWord_315364).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_315364).length < 2 ^ (prefixWord ++ tailWord_315364).sum := by decide
  have hdescent : baseEnd_315364 < baseStart_315364 := by decide
  rcases family_descends (prefixWord ++ tailWord_315364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_315367 : List Nat := [1, 1, 5, 2, 3, 1, 1, 4, 3]
def baseStart_315367 : Nat := 118140960795 + 315367 * 2 ^ 59
def prefixEnd_315367 : Nat := 4983230072969 + 3 ^ 40 * 315367 * 2
def baseEnd_315367 : Nat := 71971046029587937272071

theorem tailTrace_315367 : CollatzResearch.WordTrace tailWord_315367 prefixEnd_315367 71971046029587937272071 := by
  unfold tailWord_315367
  simp only [CollatzResearch.WordTrace]
  refine ⟨11502379448486694240664355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7668252965657796160442903 11502379448486694240664355)
  ·
    refine ⟨17253569172730041360996533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11502379448486694240664355 17253569172730041360996533)
    ·
      refine ⟨1617522109943441377593425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 17253569172730041360996533 1617522109943441377593425)
      ·
        refine ⟨1213141582457581033195069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1617522109943441377593425 1213141582457581033195069)
        ·
          refine ⟨454928093421592887448151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1213141582457581033195069 454928093421592887448151)
          ·
            refine ⟨682392140132389331172227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 454928093421592887448151 682392140132389331172227)
            ·
              refine ⟨1023588210198583996758341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 682392140132389331172227 1023588210198583996758341)
              ·
                refine ⟨191922789412234499392189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1023588210198583996758341 191922789412234499392189)
                ·
                  refine ⟨71971046029587937272071, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 191922789412234499392189 71971046029587937272071)
                  ·
                    rfl

theorem cell21_315367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 1, 1, 4, 3].length) (baseStart_315367 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_315367 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_315367 prefixEnd_315367 := by exact prefixLift 315367
  have htrace : WordTrace (prefixWord ++ tailWord_315367) baseStart_315367 baseEnd_315367 := by
    simpa [prefixWord, tailWord_315367, baseEnd_315367] using wordTrace_append hprefix tailTrace_315367
  have hstable : (prefixWord ++ tailWord_315367).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_315367).length < 2 ^ (prefixWord ++ tailWord_315367).sum := by decide
  have hdescent : baseEnd_315367 < baseStart_315367 := by decide
  rcases family_descends (prefixWord ++ tailWord_315367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_315412 : List Nat := [2, 4, 3, 2, 1, 1, 8]
def baseStart_315412 : Nat := 118140960795 + 315412 * 2 ^ 59
def prefixEnd_315412 : Nat := 4983230072969 + 3 ^ 40 * 315412 * 2
def baseEnd_315412 : Nat := 7997923960297539891331

theorem tailTrace_315412 : CollatzResearch.WordTrace tailWord_315412 prefixEnd_315412 7997923960297539891331 := by
  unfold tailWord_315412
  simp only [CollatzResearch.WordTrace]
  refine ⟨5752010366661833463026245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7669347155549111284034993 5752010366661833463026245)
  ·
    refine ⟨1078501943749093774317421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5752010366661833463026245 1078501943749093774317421)
    ·
      refine ⟨404438228905910165369033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1078501943749093774317421 404438228905910165369033)
      ·
        refine ⟨303328671679432624026775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 404438228905910165369033 303328671679432624026775)
        ·
          refine ⟨454993007519148936040163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 303328671679432624026775 454993007519148936040163)
          ·
            refine ⟨682489511278723404060245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 454993007519148936040163 682489511278723404060245)
            ·
              refine ⟨7997923960297539891331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 682489511278723404060245 7997923960297539891331)
              ·
                rfl

theorem cell21_315412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 1, 8].length) (baseStart_315412 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_315412 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_315412 prefixEnd_315412 := by exact prefixLift 315412
  have htrace : WordTrace (prefixWord ++ tailWord_315412) baseStart_315412 baseEnd_315412 := by
    simpa [prefixWord, tailWord_315412, baseEnd_315412] using wordTrace_append hprefix tailTrace_315412
  have hstable : (prefixWord ++ tailWord_315412).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_315412).length < 2 ^ (prefixWord ++ tailWord_315412).sum := by decide
  have hdescent : baseEnd_315412 < baseStart_315412 := by decide
  rcases family_descends (prefixWord ++ tailWord_315412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_315423 : List Nat := [1, 1, 2, 4, 1, 2, 3, 1, 6]
def baseStart_315423 : Nat := 118140960795 + 315423 * 2 ^ 59
def prefixEnd_315423 : Nat := 4983230072969 + 3 ^ 40 * 315423 * 2
def baseEnd_315423 : Nat := 71983825992544284338623

theorem tailTrace_315423 : CollatzResearch.WordTrace tailWord_315423 prefixEnd_315423 71983825992544284338623 := by
  unfold tailWord_315423
  simp only [CollatzResearch.WordTrace]
  refine ⟨11504421936283815804702923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7669614624189210536468615 11504421936283815804702923)
  ·
    refine ⟨17256632904425723707054385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11504421936283815804702923 17256632904425723707054385)
    ·
      refine ⟨12942474678319292780290789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17256632904425723707054385 12942474678319292780290789)
      ·
        refine ⟨2426714002184867396304523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12942474678319292780290789 2426714002184867396304523)
        ·
          refine ⟨3640071003277301094456785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2426714002184867396304523 3640071003277301094456785)
          ·
            refine ⟨2730053252457975820842589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3640071003277301094456785 2730053252457975820842589)
            ·
              refine ⟨1023769969671740932815971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2730053252457975820842589 1023769969671740932815971)
              ·
                refine ⟨1535654954507611399223957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1023769969671740932815971 1535654954507611399223957)
                ·
                  refine ⟨71983825992544284338623, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1535654954507611399223957 71983825992544284338623)
                  ·
                    rfl

theorem cell21_315423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 3, 1, 6].length) (baseStart_315423 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_315423 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_315423 prefixEnd_315423 := by exact prefixLift 315423
  have htrace : WordTrace (prefixWord ++ tailWord_315423) baseStart_315423 baseEnd_315423 := by
    simpa [prefixWord, tailWord_315423, baseEnd_315423] using wordTrace_append hprefix tailTrace_315423
  have hstable : (prefixWord ++ tailWord_315423).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_315423).length < 2 ^ (prefixWord ++ tailWord_315423).sum := by decide
  have hdescent : baseEnd_315423 < baseStart_315423 := by decide
  rcases family_descends (prefixWord ++ tailWord_315423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_315426 : List Nat := [3, 3, 1, 1, 1, 2, 1, 6, 3]
def baseStart_315426 : Nat := 118140960795 + 315426 * 2 ^ 59
def prefixEnd_315426 : Nat := 4983230072969 + 3 ^ 40 * 315426 * 2
def baseEnd_315426 : Nat := 71984510633416945788617

theorem tailTrace_315426 : CollatzResearch.WordTrace tailWord_315426 prefixEnd_315426 71984510633416945788617 := by
  unfold tailWord_315426
  simp only [CollatzResearch.WordTrace]
  refine ⟨2876132838818236829265533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7669687570181964878041421 2876132838818236829265533)
  ·
    refine ⟨1078549814556838810974575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2876132838818236829265533 1078549814556838810974575)
    ·
      refine ⟨1617824721835258216461863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1078549814556838810974575 1617824721835258216461863)
      ·
        refine ⟨2426737082752887324692795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1617824721835258216461863 2426737082752887324692795)
        ·
          refine ⟨3640105624129330987039193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2426737082752887324692795 3640105624129330987039193)
          ·
            refine ⟨2730079218096998240279395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3640105624129330987039193 2730079218096998240279395)
            ·
              refine ⟨4095118827145497360419093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2730079218096998240279395 4095118827145497360419093)
              ·
                refine ⟨191958695022445188769645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 4095118827145497360419093 191958695022445188769645)
                ·
                  refine ⟨71984510633416945788617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 191958695022445188769645 71984510633416945788617)
                  ·
                    rfl

theorem cell21_315426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 1, 6, 3].length) (baseStart_315426 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_315426 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_315426 prefixEnd_315426 := by exact prefixLift 315426
  have htrace : WordTrace (prefixWord ++ tailWord_315426) baseStart_315426 baseEnd_315426 := by
    simpa [prefixWord, tailWord_315426, baseEnd_315426] using wordTrace_append hprefix tailTrace_315426
  have hstable : (prefixWord ++ tailWord_315426).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_315426).length < 2 ^ (prefixWord ++ tailWord_315426).sum := by decide
  have hdescent : baseEnd_315426 < baseStart_315426 := by decide
  rcases family_descends (prefixWord ++ tailWord_315426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_315468 : List Nat := [2, 2, 1, 3, 1, 1, 2, 2, 7]
def baseStart_315468 : Nat := 118140960795 + 315468 * 2 ^ 59
def prefixEnd_315468 : Nat := 4983230072969 + 3 ^ 40 * 315468 * 2
def baseEnd_315468 : Nat := 71994095605634206088531

theorem tailTrace_315468 : CollatzResearch.WordTrace tailWord_315468 prefixEnd_315468 71994095605634206088531 := by
  unfold tailWord_315468
  simp only [CollatzResearch.WordTrace]
  refine ⟨5753031610560394245045529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7670708814080525660060705 5753031610560394245045529)
  ·
    refine ⟨4314773707920295683784147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5753031610560394245045529 4314773707920295683784147)
    ·
      refine ⟨6472160561880443525676221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4314773707920295683784147 6472160561880443525676221)
      ·
        refine ⟨2427060210705166322128583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6472160561880443525676221 2427060210705166322128583)
        ·
          refine ⟨3640590316057749483192875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2427060210705166322128583 3640590316057749483192875)
          ·
            refine ⟨5460885474086624224789313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3640590316057749483192875 5460885474086624224789313)
            ·
              refine ⟨4095664105564968168591985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5460885474086624224789313 4095664105564968168591985)
              ·
                refine ⟨3071748079173726126443989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4095664105564968168591985 3071748079173726126443989)
                ·
                  refine ⟨71994095605634206088531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3071748079173726126443989 71994095605634206088531)
                  ·
                    rfl

theorem cell21_315468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 2, 2, 7].length) (baseStart_315468 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_315468 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_315468 prefixEnd_315468 := by exact prefixLift 315468
  have htrace : WordTrace (prefixWord ++ tailWord_315468) baseStart_315468 baseEnd_315468 := by
    simpa [prefixWord, tailWord_315468, baseEnd_315468] using wordTrace_append hprefix tailTrace_315468
  have hstable : (prefixWord ++ tailWord_315468).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_315468).length < 2 ^ (prefixWord ++ tailWord_315468).sum := by decide
  have hdescent : baseEnd_315468 < baseStart_315468 := by decide
  rcases family_descends (prefixWord ++ tailWord_315468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_315623 : List Nat := [1, 1, 5, 3, 1, 1, 4, 5]
def baseStart_315623 : Nat := 118140960795 + 315623 * 2 ^ 59
def prefixEnd_315623 : Nat := 4983230072969 + 3 ^ 40 * 315623 * 2
def baseEnd_315623 : Nat := 24009822905796127001627

theorem tailTrace_315623 : CollatzResearch.WordTrace tailWord_315623 prefixEnd_315623 24009822905796127001627 := by
  unfold tailWord_315623
  simp only [CollatzResearch.WordTrace]
  refine ⟨11511716535559249961983523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7674477690372833307989015 11511716535559249961983523)
  ·
    refine ⟨17267574803338874942975285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11511716535559249961983523 17267574803338874942975285)
    ·
      refine ⟨1618835137813019525903933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 17267574803338874942975285 1618835137813019525903933)
      ·
        refine ⟨607063176679882322213975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1618835137813019525903933 607063176679882322213975)
        ·
          refine ⟨910594765019823483320963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 607063176679882322213975 910594765019823483320963)
          ·
            refine ⟨1365892147529735224981445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 910594765019823483320963 1365892147529735224981445)
            ·
              refine ⟨256104777661825354684021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1365892147529735224981445 256104777661825354684021)
              ·
                refine ⟨24009822905796127001627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 256104777661825354684021 24009822905796127001627)
                ·
                  rfl

theorem cell21_315623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 4, 5].length) (baseStart_315623 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_315623 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_315623 prefixEnd_315623 := by exact prefixLift 315623
  have htrace : WordTrace (prefixWord ++ tailWord_315623) baseStart_315623 baseEnd_315623 := by
    simpa [prefixWord, tailWord_315623, baseEnd_315623] using wordTrace_append hprefix tailTrace_315623
  have hstable : (prefixWord ++ tailWord_315623).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_315623).length < 2 ^ (prefixWord ++ tailWord_315623).sum := by decide
  have hdescent : baseEnd_315623 < baseStart_315623 := by decide
  rcases family_descends (prefixWord ++ tailWord_315623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_315651 : List Nat := [1, 1, 1, 3, 2, 3, 2, 4, 4]
def baseStart_315651 : Nat := 118140960795 + 315651 * 2 ^ 59
def prefixEnd_315651 : Nat := 4983230072969 + 3 ^ 40 * 315651 * 2
def baseEnd_315651 : Nat := 72035858698866554538157

theorem tailTrace_315651 : CollatzResearch.WordTrace tailWord_315651 prefixEnd_315651 72035858698866554538157 := by
  unfold tailWord_315651
  simp only [CollatzResearch.WordTrace]
  refine ⟨11512737779457810744002807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7675158519638540496001871 11512737779457810744002807)
  ·
    refine ⟨17269106669186716116004211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11512737779457810744002807 17269106669186716116004211)
    ·
      refine ⟨25903660003780074174006317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17269106669186716116004211 25903660003780074174006317)
      ·
        refine ⟨9713872501417527815252369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25903660003780074174006317 9713872501417527815252369)
        ·
          refine ⟨7285404376063145861439277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9713872501417527815252369 7285404376063145861439277)
          ·
            refine ⟨2732026641023679698039729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7285404376063145861439277 2732026641023679698039729)
            ·
              refine ⟨2049019980767759773529797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2732026641023679698039729 2049019980767759773529797)
              ·
                refine ⟨384191246393954957536837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2049019980767759773529797 384191246393954957536837)
                ·
                  refine ⟨72035858698866554538157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 384191246393954957536837 72035858698866554538157)
                  ·
                    rfl

theorem cell21_315651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 2, 4, 4].length) (baseStart_315651 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_315651 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_315651 prefixEnd_315651 := by exact prefixLift 315651
  have htrace : WordTrace (prefixWord ++ tailWord_315651) baseStart_315651 baseEnd_315651 := by
    simpa [prefixWord, tailWord_315651, baseEnd_315651] using wordTrace_append hprefix tailTrace_315651
  have hstable : (prefixWord ++ tailWord_315651).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_315651).length < 2 ^ (prefixWord ++ tailWord_315651).sum := by decide
  have hdescent : baseEnd_315651 < baseStart_315651 := by decide
  rcases family_descends (prefixWord ++ tailWord_315651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_315665 : List Nat := [1, 2, 2, 1, 1, 5, 1, 8]
def baseStart_315665 : Nat := 118140960795 + 315665 * 2 ^ 59
def prefixEnd_315665 : Nat := 4983230072969 + 3 ^ 40 * 315665 * 2
def baseEnd_315665 : Nat := 24013017896535213768265

theorem tailTrace_315665 : CollatzResearch.WordTrace tailWord_315665 prefixEnd_315665 24013017896535213768265 := by
  unfold tailWord_315665
  simp only [CollatzResearch.WordTrace]
  refine ⟨11513248401407091135012449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7675498934271394090008299 11513248401407091135012449)
  ·
    refine ⟨8634936301055318351259337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11513248401407091135012449 8634936301055318351259337)
    ·
      refine ⟨6476202225791488763444503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8634936301055318351259337 6476202225791488763444503)
      ·
        refine ⟨9714303338687233145166755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6476202225791488763444503 9714303338687233145166755)
        ·
          refine ⟨14571455008030849717750133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9714303338687233145166755 14571455008030849717750133)
          ·
            refine ⟨1366073907002892161039075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 14571455008030849717750133 1366073907002892161039075)
            ·
              refine ⟨2049110860504338241558613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1366073907002892161039075 2049110860504338241558613)
              ·
                refine ⟨24013017896535213768265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2049110860504338241558613 24013017896535213768265)
                ·
                  rfl

theorem cell21_315665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 1, 8].length) (baseStart_315665 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_315665 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_315665 prefixEnd_315665 := by exact prefixLift 315665
  have htrace : WordTrace (prefixWord ++ tailWord_315665) baseStart_315665 baseEnd_315665 := by
    simpa [prefixWord, tailWord_315665, baseEnd_315665] using wordTrace_append hprefix tailTrace_315665
  have hstable : (prefixWord ++ tailWord_315665).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_315665).length < 2 ^ (prefixWord ++ tailWord_315665).sum := by decide
  have hdescent : baseEnd_315665 < baseStart_315665 := by decide
  rcases family_descends (prefixWord ++ tailWord_315665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_315682 : List Nat := [3, 3, 1, 1, 3, 1, 2, 7]
def baseStart_315682 : Nat := 118140960795 + 315682 * 2 ^ 59
def prefixEnd_315682 : Nat := 4983230072969 + 3 ^ 40 * 315682 * 2
def baseEnd_315682 : Nat := 24014311107072463173809

theorem tailTrace_315682 : CollatzResearch.WordTrace tailWord_315682 prefixEnd_315682 24014311107072463173809 := by
  unfold tailWord_315682
  simp only [CollatzResearch.WordTrace]
  refine ⟨2878467110586375759595325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7675912294897002025587533 2878467110586375759595325)
  ·
    refine ⟨1079425166469890909848247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2878467110586375759595325 1079425166469890909848247)
    ·
      refine ⟨1619137749704836364772371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1079425166469890909848247 1619137749704836364772371)
      ·
        refine ⟨2428706624557254547158557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1619137749704836364772371 2428706624557254547158557)
        ·
          refine ⟨910764984208970455184459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2428706624557254547158557 910764984208970455184459)
          ·
            refine ⟨1366147476313455682776689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 910764984208970455184459 1366147476313455682776689)
            ·
              refine ⟨1024610607235091762082517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1366147476313455682776689 1024610607235091762082517)
              ·
                refine ⟨24014311107072463173809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1024610607235091762082517 24014311107072463173809)
                ·
                  rfl

theorem cell21_315682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 2, 7].length) (baseStart_315682 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_315682 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_315682 prefixEnd_315682 := by exact prefixLift 315682
  have htrace : WordTrace (prefixWord ++ tailWord_315682) baseStart_315682 baseEnd_315682 := by
    simpa [prefixWord, tailWord_315682, baseEnd_315682] using wordTrace_append hprefix tailTrace_315682
  have hstable : (prefixWord ++ tailWord_315682).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_315682).length < 2 ^ (prefixWord ++ tailWord_315682).sum := by decide
  have hdescent : baseEnd_315682 < baseStart_315682 := by decide
  rcases family_descends (prefixWord ++ tailWord_315682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_315716 : List Nat := [2, 3, 4, 1, 2, 2, 1, 6]
def baseStart_315716 : Nat := 118140960795 + 315716 * 2 ^ 59
def prefixEnd_315716 : Nat := 4983230072969 + 3 ^ 40 * 315716 * 2
def baseEnd_315716 : Nat := 24016897528146961984897

theorem tailTrace_315716 : CollatzResearch.WordTrace tailWord_315716 prefixEnd_315716 24016897528146961984897 := by
  unfold tailWord_315716
  simp only [CollatzResearch.WordTrace]
  refine ⟨5757554262111163422559501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7676739016148217896746001 5757554262111163422559501)
  ·
    refine ⟨2159082848291686283459813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5757554262111163422559501 2159082848291686283459813)
    ·
      refine ⟨404828034054691178148715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2159082848291686283459813 404828034054691178148715)
      ·
        refine ⟨607242051082036767223073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 404828034054691178148715 607242051082036767223073)
        ·
          refine ⟨455431538311527575417305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 607242051082036767223073 455431538311527575417305)
          ·
            refine ⟨341573653733645681562979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 455431538311527575417305 341573653733645681562979)
            ·
              refine ⟨512360480600468522344469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 341573653733645681562979 512360480600468522344469)
              ·
                refine ⟨24016897528146961984897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 512360480600468522344469 24016897528146961984897)
                ·
                  rfl

theorem cell21_315716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 2, 1, 6].length) (baseStart_315716 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_315716 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_315716 prefixEnd_315716 := by exact prefixLift 315716
  have htrace : WordTrace (prefixWord ++ tailWord_315716) baseStart_315716 baseEnd_315716 := by
    simpa [prefixWord, tailWord_315716, baseEnd_315716] using wordTrace_append hprefix tailTrace_315716
  have hstable : (prefixWord ++ tailWord_315716).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_315716).length < 2 ^ (prefixWord ++ tailWord_315716).sum := by decide
  have hdescent : baseEnd_315716 < baseStart_315716 := by decide
  rcases family_descends (prefixWord ++ tailWord_315716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_315798 : List Nat := [5, 3, 1, 2, 1, 2, 1, 3, 3]
def baseStart_315798 : Nat := 118140960795 + 315798 * 2 ^ 59
def prefixEnd_315798 : Nat := 4983230072969 + 3 ^ 40 * 315798 * 2
def baseEnd_315798 : Nat := 72069406101626965587857

theorem tailTrace_315798 : CollatzResearch.WordTrace tailWord_315798 prefixEnd_315798 72069406101626965587857 := by
  unfold tailWord_315798
  simp only [CollatzResearch.WordTrace]
  refine ⟨719881206870328428100253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 7678732873283503233069365 719881206870328428100253)
  ·
    refine ⟨269955452576373160537595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 719881206870328428100253 269955452576373160537595)
    ·
      refine ⟨404933178864559740806393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 269955452576373160537595 404933178864559740806393)
      ·
        refine ⟨303699884148419805604795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 404933178864559740806393 303699884148419805604795)
        ·
          refine ⟨455549826222629708407193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 303699884148419805604795 455549826222629708407193)
          ·
            refine ⟨341662369666972281305395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 455549826222629708407193 341662369666972281305395)
            ·
              refine ⟨512493554500458421958093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 341662369666972281305395 512493554500458421958093)
              ·
                refine ⟨192185082937671908234285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 512493554500458421958093 192185082937671908234285)
                ·
                  refine ⟨72069406101626965587857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 192185082937671908234285 72069406101626965587857)
                  ·
                    rfl

theorem cell21_315798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 2, 1, 3, 3].length) (baseStart_315798 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_315798 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_315798 prefixEnd_315798 := by exact prefixLift 315798
  have htrace : WordTrace (prefixWord ++ tailWord_315798) baseStart_315798 baseEnd_315798 := by
    simpa [prefixWord, tailWord_315798, baseEnd_315798] using wordTrace_append hprefix tailTrace_315798
  have hstable : (prefixWord ++ tailWord_315798).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_315798).length < 2 ^ (prefixWord ++ tailWord_315798).sum := by decide
  have hdescent : baseEnd_315798 < baseStart_315798 := by decide
  rcases family_descends (prefixWord ++ tailWord_315798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_315837 : List Nat := [1, 4, 1, 2, 2, 4, 2, 1, 4]
def baseStart_315837 : Nat := 118140960795 + 315837 * 2 ^ 59
def prefixEnd_315837 : Nat := 4983230072969 + 3 ^ 40 * 315837 * 2
def baseEnd_315837 : Nat := 72078306432971564437777

theorem tailTrace_315837 : CollatzResearch.WordTrace tailWord_315837 prefixEnd_315837 72078306432971564437777 := by
  unfold tailWord_315837
  simp only [CollatzResearch.WordTrace]
  refine ⟨11519521756783964510273765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7679681171189309673515843 11519521756783964510273765)
  ·
    refine ⟨2159910329396993345676331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11519521756783964510273765 2159910329396993345676331)
    ·
      refine ⟨3239865494095490018514497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2159910329396993345676331 3239865494095490018514497)
      ·
        refine ⟨2429899120571617513885873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3239865494095490018514497 2429899120571617513885873)
        ·
          refine ⟨1822424340428713135414405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2429899120571617513885873 1822424340428713135414405)
          ·
            refine ⟨341704563830383712890201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1822424340428713135414405 341704563830383712890201)
            ·
              refine ⟨256278422872787784667651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 341704563830383712890201 256278422872787784667651)
              ·
                refine ⟨384417634309181677001477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 256278422872787784667651 384417634309181677001477)
                ·
                  refine ⟨72078306432971564437777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 384417634309181677001477 72078306432971564437777)
                  ·
                    rfl

theorem cell21_315837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 4, 2, 1, 4].length) (baseStart_315837 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_315837 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_315837 prefixEnd_315837 := by exact prefixLift 315837
  have htrace : WordTrace (prefixWord ++ tailWord_315837) baseStart_315837 baseEnd_315837 := by
    simpa [prefixWord, tailWord_315837, baseEnd_315837] using wordTrace_append hprefix tailTrace_315837
  have hstable : (prefixWord ++ tailWord_315837).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_315837).length < 2 ^ (prefixWord ++ tailWord_315837).sum := by decide
  have hdescent : baseEnd_315837 < baseStart_315837 := by decide
  rcases family_descends (prefixWord ++ tailWord_315837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_315865 : List Nat := [1, 2, 1, 2, 4, 1, 2, 5, 3]
def baseStart_315865 : Nat := 118140960795 + 315865 * 2 ^ 59
def prefixEnd_315865 : Nat := 4983230072969 + 3 ^ 40 * 315865 * 2
def baseEnd_315865 : Nat := 72084696414449737971053

theorem tailTrace_315865 : CollatzResearch.WordTrace tailWord_315865 prefixEnd_315865 72084696414449737971053 := by
  unfold tailWord_315865
  simp only [CollatzResearch.WordTrace]
  refine ⟨11520543000682525292293049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7680362000455016861528699 11520543000682525292293049)
  ·
    refine ⟨8640407250511893969219787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11520543000682525292293049 8640407250511893969219787)
    ·
      refine ⟨12960610875767840953829681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8640407250511893969219787 12960610875767840953829681)
      ·
        refine ⟨9720458156825880715372261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12960610875767840953829681 9720458156825880715372261)
        ·
          refine ⟨1822585904404852634132299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9720458156825880715372261 1822585904404852634132299)
          ·
            refine ⟨2733878856607278951198449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1822585904404852634132299 2733878856607278951198449)
            ·
              refine ⟨2050409142455459213398837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2733878856607278951198449 2050409142455459213398837)
              ·
                refine ⟨192225857105199301256141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2050409142455459213398837 192225857105199301256141)
                ·
                  refine ⟨72084696414449737971053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 192225857105199301256141 72084696414449737971053)
                  ·
                    rfl

theorem cell21_315865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 2, 5, 3].length) (baseStart_315865 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_315865 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_315865 prefixEnd_315865 := by exact prefixLift 315865
  have htrace : WordTrace (prefixWord ++ tailWord_315865) baseStart_315865 baseEnd_315865 := by
    simpa [prefixWord, tailWord_315865, baseEnd_315865] using wordTrace_append hprefix tailTrace_315865
  have hstable : (prefixWord ++ tailWord_315865).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_315865).length < 2 ^ (prefixWord ++ tailWord_315865).sum := by decide
  have hdescent : baseEnd_315865 < baseStart_315865 := by decide
  rcases family_descends (prefixWord ++ tailWord_315865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_315874 : List Nat := [3, 3, 3, 2, 2, 1, 2, 2, 3]
def baseStart_315874 : Nat := 118140960795 + 315874 * 2 ^ 59
def prefixEnd_315874 : Nat := 4983230072969 + 3 ^ 40 * 315874 * 2
def baseEnd_315874 : Nat := 72086750337067722321035

theorem tailTrace_315874 : CollatzResearch.WordTrace tailWord_315874 prefixEnd_315874 72086750337067722321035 := by
  unfold tailWord_315874
  simp only [CollatzResearch.WordTrace]
  refine ⟨2880217814412479957342669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7680580838433279886247117 2880217814412479957342669)
  ·
    refine ⟨1080081680404679984003501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2880217814412479957342669 1080081680404679984003501)
    ·
      refine ⟨405030630151754994001313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1080081680404679984003501 405030630151754994001313)
      ·
        refine ⟨303772972613816245500985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 405030630151754994001313 303772972613816245500985)
        ·
          refine ⟨227829729460362184125739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 303772972613816245500985 227829729460362184125739)
          ·
            refine ⟨341744594190543276188609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 227829729460362184125739 341744594190543276188609)
            ·
              refine ⟨256308445642907457141457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 341744594190543276188609 256308445642907457141457)
              ·
                refine ⟨192231334232180592856093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 256308445642907457141457 192231334232180592856093)
                ·
                  refine ⟨72086750337067722321035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 192231334232180592856093 72086750337067722321035)
                  ·
                    rfl

theorem cell21_315874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 2, 1, 2, 2, 3].length) (baseStart_315874 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_315874 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_315874 prefixEnd_315874 := by exact prefixLift 315874
  have htrace : WordTrace (prefixWord ++ tailWord_315874) baseStart_315874 baseEnd_315874 := by
    simpa [prefixWord, tailWord_315874, baseEnd_315874] using wordTrace_append hprefix tailTrace_315874
  have hstable : (prefixWord ++ tailWord_315874).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_315874).length < 2 ^ (prefixWord ++ tailWord_315874).sum := by decide
  have hdescent : baseEnd_315874 < baseStart_315874 := by decide
  rcases family_descends (prefixWord ++ tailWord_315874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_315882 : List Nat := [3, 1, 3, 1, 3, 2, 1, 4, 3]
def baseStart_315882 : Nat := 118140960795 + 315882 * 2 ^ 59
def prefixEnd_315882 : Nat := 4983230072969 + 3 ^ 40 * 315882 * 2
def baseEnd_315882 : Nat := 72088576046061486187685

theorem tailTrace_315882 : CollatzResearch.WordTrace tailWord_315882 prefixEnd_315882 72088576046061486187685 := by
  unfold tailWord_315882
  simp only [CollatzResearch.WordTrace]
  refine ⟨2880290760405234298915475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7680775361080624797107933 2880290760405234298915475)
  ·
    refine ⟨4320436140607851448373213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2880290760405234298915475 4320436140607851448373213)
    ·
      refine ⟨1620163552727944293139955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4320436140607851448373213 1620163552727944293139955)
      ·
        refine ⟨2430245329091916439709933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1620163552727944293139955 2430245329091916439709933)
        ·
          refine ⟨911341998409468664891225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2430245329091916439709933 911341998409468664891225)
          ·
            refine ⟨683506498807101498668419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 911341998409468664891225 683506498807101498668419)
            ·
              refine ⟨1025259748210652248002629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 683506498807101498668419 1025259748210652248002629)
              ·
                refine ⟨192236202789497296500493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1025259748210652248002629 192236202789497296500493)
                ·
                  refine ⟨72088576046061486187685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 192236202789497296500493 72088576046061486187685)
                  ·
                    rfl

theorem cell21_315882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 2, 1, 4, 3].length) (baseStart_315882 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_315882 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_315882 prefixEnd_315882 := by exact prefixLift 315882
  have htrace : WordTrace (prefixWord ++ tailWord_315882) baseStart_315882 baseEnd_315882 := by
    simpa [prefixWord, tailWord_315882, baseEnd_315882] using wordTrace_append hprefix tailTrace_315882
  have hstable : (prefixWord ++ tailWord_315882).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_315882).length < 2 ^ (prefixWord ++ tailWord_315882).sum := by decide
  have hdescent : baseEnd_315882 < baseStart_315882 := by decide
  rcases family_descends (prefixWord ++ tailWord_315882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_315941 : List Nat := [1, 3, 1, 2, 2, 1, 4, 4, 3]
def baseStart_315941 : Nat := 118140960795 + 315941 * 2 ^ 59
def prefixEnd_315941 : Nat := 4983230072969 + 3 ^ 40 * 315941 * 2
def baseEnd_315941 : Nat := 72102040649890494704231

theorem tailTrace_315941 : CollatzResearch.WordTrace tailWord_315941 prefixEnd_315941 72102040649890494704231 := by
  unfold tailWord_315941
  simp only [CollatzResearch.WordTrace]
  refine ⟨11523314948407190272059677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7682209965604793514706451 11523314948407190272059677)
  ·
    refine ⟨4321243105652696352022379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11523314948407190272059677 4321243105652696352022379)
    ·
      refine ⟨6481864658479044528033569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4321243105652696352022379 6481864658479044528033569)
      ·
        refine ⟨4861398493859283396025177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6481864658479044528033569 4861398493859283396025177)
        ·
          refine ⟨3646048870394462547018883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4861398493859283396025177 3646048870394462547018883)
          ·
            refine ⟨5469073305591693820528325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3646048870394462547018883 5469073305591693820528325)
            ·
              refine ⟨1025451244798442591349061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5469073305591693820528325 1025451244798442591349061)
              ·
                refine ⟨192272108399707985877949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1025451244798442591349061 192272108399707985877949)
                ·
                  refine ⟨72102040649890494704231, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 192272108399707985877949 72102040649890494704231)
                  ·
                    rfl

theorem cell21_315941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 4, 4, 3].length) (baseStart_315941 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_315941 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_315941 prefixEnd_315941 := by exact prefixLift 315941
  have htrace : WordTrace (prefixWord ++ tailWord_315941) baseStart_315941 baseEnd_315941 := by
    simpa [prefixWord, tailWord_315941, baseEnd_315941] using wordTrace_append hprefix tailTrace_315941
  have hstable : (prefixWord ++ tailWord_315941).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_315941).length < 2 ^ (prefixWord ++ tailWord_315941).sum := by decide
  have hdescent : baseEnd_315941 < baseStart_315941 := by decide
  rcases family_descends (prefixWord ++ tailWord_315941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_315983 : List Nat := [1, 1, 2, 1, 1, 2, 4, 2, 7]
def baseStart_315983 : Nat := 118140960795 + 315983 * 2 ^ 59
def prefixEnd_315983 : Nat := 4983230072969 + 3 ^ 40 * 315983 * 2
def baseEnd_315983 : Nat := 72111625622107755004145

theorem tailTrace_315983 : CollatzResearch.WordTrace tailWord_315983 prefixEnd_315983 72111625622107755004145 := by
  unfold tailWord_315983
  simp only [CollatzResearch.WordTrace]
  refine ⟨11524846814255031445088603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7683231209503354296725735 11524846814255031445088603)
  ·
    refine ⟨17287270221382547167632905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11524846814255031445088603 17287270221382547167632905)
    ·
      refine ⟨12965452666036910375724679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17287270221382547167632905 12965452666036910375724679)
      ·
        refine ⟨19448178999055365563587019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12965452666036910375724679 19448178999055365563587019)
        ·
          refine ⟨29172268498583048345380529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19448178999055365563587019 29172268498583048345380529)
          ·
            refine ⟨21879201373937286259035397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29172268498583048345380529 21879201373937286259035397)
            ·
              refine ⟨4102350257613241173569137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21879201373937286259035397 4102350257613241173569137)
              ·
                refine ⟨3076762693209930880176853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4102350257613241173569137 3076762693209930880176853)
                ·
                  refine ⟨72111625622107755004145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3076762693209930880176853 72111625622107755004145)
                  ·
                    rfl

theorem cell21_315983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 4, 2, 7].length) (baseStart_315983 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_315983 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_315983 prefixEnd_315983 := by exact prefixLift 315983
  have htrace : WordTrace (prefixWord ++ tailWord_315983) baseStart_315983 baseEnd_315983 := by
    simpa [prefixWord, tailWord_315983, baseEnd_315983] using wordTrace_append hprefix tailTrace_315983
  have hstable : (prefixWord ++ tailWord_315983).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_315983).length < 2 ^ (prefixWord ++ tailWord_315983).sum := by decide
  have hdescent : baseEnd_315983 < baseStart_315983 := by decide
  rcases family_descends (prefixWord ++ tailWord_315983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_316000 : List Nat := [2, 1, 1, 3, 2, 1, 5, 1, 5]
def baseStart_316000 : Nat := 118140960795 + 316000 * 2 ^ 59
def prefixEnd_316000 : Nat := 4983230072969 + 3 ^ 40 * 316000 * 2
def baseEnd_316000 : Nat := 72115505253719503220777

theorem tailTrace_316000 : CollatzResearch.WordTrace tailWord_316000 prefixEnd_316000 72115505253719503220777 := by
  unfold tailWord_316000
  simp only [CollatzResearch.WordTrace]
  refine ⟨5762733427596721674228727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7683644570128962232304969 5762733427596721674228727)
  ·
    refine ⟨8644100141395082511343091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5762733427596721674228727 8644100141395082511343091)
    ·
      refine ⟨12966150212092623767014637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8644100141395082511343091 12966150212092623767014637)
      ·
        refine ⟨4862306329534733912630489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12966150212092623767014637 4862306329534733912630489)
        ·
          refine ⟨3646729747151050434472867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4862306329534733912630489 3646729747151050434472867)
          ·
            refine ⟨5470094620726575651709301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3646729747151050434472867 5470094620726575651709301)
            ·
              refine ⟨512821370693116467347747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5470094620726575651709301 512821370693116467347747)
              ·
                refine ⟨769232056039674701021621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 512821370693116467347747 769232056039674701021621)
                ·
                  refine ⟨72115505253719503220777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 769232056039674701021621 72115505253719503220777)
                  ·
                    rfl

theorem cell21_316000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 5, 1, 5].length) (baseStart_316000 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_316000 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_316000 prefixEnd_316000 := by exact prefixLift 316000
  have htrace : WordTrace (prefixWord ++ tailWord_316000) baseStart_316000 baseEnd_316000 := by
    simpa [prefixWord, tailWord_316000, baseEnd_316000] using wordTrace_append hprefix tailTrace_316000
  have hstable : (prefixWord ++ tailWord_316000).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_316000).length < 2 ^ (prefixWord ++ tailWord_316000).sum := by decide
  have hdescent : baseEnd_316000 < baseStart_316000 := by decide
  rcases family_descends (prefixWord ++ tailWord_316000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_316090 : List Nat := [3, 1, 1, 1, 2, 3, 2, 2, 6]
def baseStart_316090 : Nat := 118140960795 + 316090 * 2 ^ 59
def prefixEnd_316090 : Nat := 4983230072969 + 3 ^ 40 * 316090 * 2
def baseEnd_316090 : Nat := 72136044479899346720593

theorem tailTrace_316090 : CollatzResearch.WordTrace tailWord_316090 prefixEnd_316090 72136044479899346720593 := by
  unfold tailWord_316090
  simp only [CollatzResearch.WordTrace]
  refine ⟨2882187356216847179808431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7685832949911592479489149 2882187356216847179808431)
  ·
    refine ⟨4323281034325270769712647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2882187356216847179808431 4323281034325270769712647)
    ·
      refine ⟨6484921551487906154568971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4323281034325270769712647 6484921551487906154568971)
      ·
        refine ⟨9727382327231859231853457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6484921551487906154568971 9727382327231859231853457)
        ·
          refine ⟨7295536745423894423890093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9727382327231859231853457 7295536745423894423890093)
          ·
            refine ⟨2735826279533960408958785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7295536745423894423890093 2735826279533960408958785)
            ·
              refine ⟨2051869709650470306719089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2735826279533960408958785 2051869709650470306719089)
              ·
                refine ⟨1538902282237852730039317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2051869709650470306719089 1538902282237852730039317)
                ·
                  refine ⟨72136044479899346720593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1538902282237852730039317 72136044479899346720593)
                  ·
                    rfl

theorem cell21_316090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 2, 2, 6].length) (baseStart_316090 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_316090 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_316090 prefixEnd_316090 := by exact prefixLift 316090
  have htrace : WordTrace (prefixWord ++ tailWord_316090) baseStart_316090 baseEnd_316090 := by
    simpa [prefixWord, tailWord_316090, baseEnd_316090] using wordTrace_append hprefix tailTrace_316090
  have hstable : (prefixWord ++ tailWord_316090).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_316090).length < 2 ^ (prefixWord ++ tailWord_316090).sum := by decide
  have hdescent : baseEnd_316090 < baseStart_316090 := by decide
  rcases family_descends (prefixWord ++ tailWord_316090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_316093 : List Nat := [1, 4, 1, 2, 1, 3, 1, 5, 3]
def baseStart_316093 : Nat := 118140960795 + 316093 * 2 ^ 59
def prefixEnd_316093 : Nat := 4983230072969 + 3 ^ 40 * 316093 * 2
def baseEnd_316093 : Nat := 72136729120772008170587

theorem tailTrace_316093 : CollatzResearch.WordTrace tailWord_316093 prefixEnd_316093 72136729120772008170587 := by
  unfold tailWord_316093
  simp only [CollatzResearch.WordTrace]
  refine ⟨11528858843856520231592933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7685905895904346821061955 11528858843856520231592933)
  ·
    refine ⟨2161661033223097543423675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11528858843856520231592933 2161661033223097543423675)
    ·
      refine ⟨3242491549834646315135513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2161661033223097543423675 3242491549834646315135513)
      ·
        refine ⟨2431868662375984736351635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3242491549834646315135513 2431868662375984736351635)
        ·
          refine ⟨3647802993563977104527453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2431868662375984736351635 3647802993563977104527453)
          ·
            refine ⟨1367926122586491414197795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3647802993563977104527453 1367926122586491414197795)
            ·
              refine ⟨2051889183879737121296693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1367926122586491414197795 2051889183879737121296693)
              ·
                refine ⟨192364610988725355121565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2051889183879737121296693 192364610988725355121565)
                ·
                  refine ⟨72136729120772008170587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 192364610988725355121565 72136729120772008170587)
                  ·
                    rfl

theorem cell21_316093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 1, 5, 3].length) (baseStart_316093 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_316093 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_316093 prefixEnd_316093 := by exact prefixLift 316093
  have htrace : WordTrace (prefixWord ++ tailWord_316093) baseStart_316093 baseEnd_316093 := by
    simpa [prefixWord, tailWord_316093, baseEnd_316093] using wordTrace_append hprefix tailTrace_316093
  have hstable : (prefixWord ++ tailWord_316093).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_316093).length < 2 ^ (prefixWord ++ tailWord_316093).sum := by decide
  have hdescent : baseEnd_316093 < baseStart_316093 := by decide
  rcases family_descends (prefixWord ++ tailWord_316093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_316214 : List Nat := [5, 1, 2, 2, 2, 9]
def baseStart_316214 : Nat := 118140960795 + 316214 * 2 ^ 59
def prefixEnd_316214 : Nat := 4983230072969 + 3 ^ 40 * 316214 * 2
def baseEnd_316214 : Nat := 2672753443307506913099

theorem tailTrace_316214 : CollatzResearch.WordTrace tailWord_316214 prefixEnd_316214 2672753443307506913099 := by
  unfold tailWord_316214
  simp only [CollatzResearch.WordTrace]
  refine ⟨720829504776134868546731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 7688848050945438597831797 720829504776134868546731)
  ·
    refine ⟨1081244257164202302820097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 720829504776134868546731 1081244257164202302820097)
    ·
      refine ⟨810933192873151727115073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1081244257164202302820097 810933192873151727115073)
      ·
        refine ⟨608199894654863795336305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 810933192873151727115073 608199894654863795336305)
        ·
          refine ⟨456149920991147846502229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 608199894654863795336305 456149920991147846502229)
          ·
            refine ⟨2672753443307506913099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 456149920991147846502229 2672753443307506913099)
            ·
              rfl

theorem cell21_316214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 9].length) (baseStart_316214 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_316214 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_316214 prefixEnd_316214 := by exact prefixLift 316214
  have htrace : WordTrace (prefixWord ++ tailWord_316214) baseStart_316214 baseEnd_316214 := by
    simpa [prefixWord, tailWord_316214, baseEnd_316214] using wordTrace_append hprefix tailTrace_316214
  have hstable : (prefixWord ++ tailWord_316214).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_316214).length < 2 ^ (prefixWord ++ tailWord_316214).sum := by decide
  have hdescent : baseEnd_316214 < baseStart_316214 := by decide
  rcases family_descends (prefixWord ++ tailWord_316214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_316287 : List Nat := [1, 1, 2, 2, 1, 1, 5, 3, 5]
def baseStart_316287 : Nat := 118140960795 + 316287 * 2 ^ 59
def prefixEnd_316287 : Nat := 4983230072969 + 3 ^ 40 * 316287 * 2
def baseEnd_316287 : Nat := 72181002563870781936857

theorem tailTrace_316287 : CollatzResearch.WordTrace tailWord_316287 prefixEnd_316287 72181002563870781936857 := by
  unfold tailWord_316287
  simp only [CollatzResearch.WordTrace]
  refine ⟨11535934605153691364155115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7690623070102460909436743 11535934605153691364155115)
  ·
    refine ⟨17303901907730537046232673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11535934605153691364155115 17303901907730537046232673)
    ·
      refine ⟨12977926430797902784674505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17303901907730537046232673 12977926430797902784674505)
      ·
        refine ⟨9733444823098427088505879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12977926430797902784674505 9733444823098427088505879)
        ·
          refine ⟨14600167234647640632758819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9733444823098427088505879 14600167234647640632758819)
          ·
            refine ⟨21900250851971460949138229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14600167234647640632758819 21900250851971460949138229)
            ·
              refine ⟨2053148517372324463981709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 21900250851971460949138229 2053148517372324463981709)
              ·
                refine ⟨769930694014621673993141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2053148517372324463981709 769930694014621673993141)
                ·
                  refine ⟨72181002563870781936857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 769930694014621673993141 72181002563870781936857)
                  ·
                    rfl

theorem cell21_316287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 5, 3, 5].length) (baseStart_316287 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_316287 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_316287 prefixEnd_316287 := by exact prefixLift 316287
  have htrace : WordTrace (prefixWord ++ tailWord_316287) baseStart_316287 baseEnd_316287 := by
    simpa [prefixWord, tailWord_316287, baseEnd_316287] using wordTrace_append hprefix tailTrace_316287
  have hstable : (prefixWord ++ tailWord_316287).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_316287).length < 2 ^ (prefixWord ++ tailWord_316287).sum := by decide
  have hdescent : baseEnd_316287 < baseStart_316287 := by decide
  rcases family_descends (prefixWord ++ tailWord_316287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_316352 : List Nat := [2, 1, 1, 2, 3, 5, 2, 1, 4]
def baseStart_316352 : Nat := 118140960795 + 316352 * 2 ^ 59
def prefixEnd_316352 : Nat := 4983230072969 + 3 ^ 40 * 316352 * 2
def baseEnd_316352 : Nat := 72195836449445113353391

theorem tailTrace_316352 : CollatzResearch.WordTrace tailWord_316352 prefixEnd_316352 72195836449445113353391 := by
  unfold tailWord_316352
  simp only [CollatzResearch.WordTrace]
  refine ⟨5769152674959103732635655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7692203566612138310180873 5769152674959103732635655)
  ·
    refine ⟨8653729012438655598953483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5769152674959103732635655 8653729012438655598953483)
    ·
      refine ⟨12980593518657983398430225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8653729012438655598953483 12980593518657983398430225)
      ·
        refine ⟨9735445138993487548822669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12980593518657983398430225 9735445138993487548822669)
        ·
          refine ⟨3650791927122557830808501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9735445138993487548822669 3650791927122557830808501)
          ·
            refine ⟨342261743167739796638297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 3650791927122557830808501 342261743167739796638297)
            ·
              refine ⟨256696307375804847478723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 342261743167739796638297 256696307375804847478723)
              ·
                refine ⟨385044461063707271218085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 256696307375804847478723 385044461063707271218085)
                ·
                  refine ⟨72195836449445113353391, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 385044461063707271218085 72195836449445113353391)
                  ·
                    rfl

theorem cell21_316352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 5, 2, 1, 4].length) (baseStart_316352 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_316352 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_316352 prefixEnd_316352 := by exact prefixLift 316352
  have htrace : WordTrace (prefixWord ++ tailWord_316352) baseStart_316352 baseEnd_316352 := by
    simpa [prefixWord, tailWord_316352, baseEnd_316352] using wordTrace_append hprefix tailTrace_316352
  have hstable : (prefixWord ++ tailWord_316352).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_316352).length < 2 ^ (prefixWord ++ tailWord_316352).sum := by decide
  have hdescent : baseEnd_316352 < baseStart_316352 := by decide
  rcases family_descends (prefixWord ++ tailWord_316352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_316445 : List Nat := [1, 4, 2, 2, 4, 1, 1, 2, 4]
def baseStart_316445 : Nat := 118140960795 + 316445 * 2 ^ 59
def prefixEnd_316445 : Nat := 4983230072969 + 3 ^ 40 * 316445 * 2
def baseEnd_316445 : Nat := 72217060316497618303201

theorem tailTrace_316445 : CollatzResearch.WordTrace tailWord_316445 prefixEnd_316445 72217060316497618303201 := by
  unfold tailWord_316445
  simp only [CollatzResearch.WordTrace]
  refine ⟨11541697338581284348406789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7694464892387522898937859 11541697338581284348406789)
  ·
    refine ⟨2164068250983990815326273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11541697338581284348406789 2164068250983990815326273)
    ·
      refine ⟨1623051188237993111494705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2164068250983990815326273 1623051188237993111494705)
      ·
        refine ⟨1217288391178494833621029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1623051188237993111494705 1217288391178494833621029)
        ·
          refine ⟨228241573345967781303943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1217288391178494833621029 228241573345967781303943)
          ·
            refine ⟨342362360018951671955915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 228241573345967781303943 342362360018951671955915)
            ·
              refine ⟨513543540028427507933873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 342362360018951671955915 513543540028427507933873)
              ·
                refine ⟨385157655021320630950405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 513543540028427507933873 385157655021320630950405)
                ·
                  refine ⟨72217060316497618303201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 385157655021320630950405 72217060316497618303201)
                  ·
                    rfl

theorem cell21_316445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 4, 1, 1, 2, 4].length) (baseStart_316445 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_316445 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_316445 prefixEnd_316445 := by exact prefixLift 316445
  have htrace : WordTrace (prefixWord ++ tailWord_316445) baseStart_316445 baseEnd_316445 := by
    simpa [prefixWord, tailWord_316445, baseEnd_316445] using wordTrace_append hprefix tailTrace_316445
  have hstable : (prefixWord ++ tailWord_316445).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_316445).length < 2 ^ (prefixWord ++ tailWord_316445).sum := by decide
  have hdescent : baseEnd_316445 < baseStart_316445 := by decide
  rcases family_descends (prefixWord ++ tailWord_316445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_316529 : List Nat := [1, 2, 2, 2, 1, 1, 2, 2, 8]
def baseStart_316529 : Nat := 118140960795 + 316529 * 2 ^ 59
def prefixEnd_316529 : Nat := 4983230072969 + 3 ^ 40 * 316529 * 2
def baseEnd_316529 : Nat := 72236230260932138903029

theorem tailTrace_316529 : CollatzResearch.WordTrace tailWord_316529 prefixEnd_316529 72236230260932138903029 := by
  unfold tailWord_316529
  simp only [CollatzResearch.WordTrace]
  refine ⟨11544761070276966694464641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7696507380184644462976427 11544761070276966694464641)
  ·
    refine ⟨8658570802707725020848481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11544761070276966694464641 8658570802707725020848481)
    ·
      refine ⟨6493928102030793765636361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8658570802707725020848481 6493928102030793765636361)
      ·
        refine ⟨4870446076523095324227271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6493928102030793765636361 4870446076523095324227271)
        ·
          refine ⟨7305669114784642986340907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4870446076523095324227271 7305669114784642986340907)
          ·
            refine ⟨10958503672176964479511361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7305669114784642986340907 10958503672176964479511361)
            ·
              refine ⟨8218877754132723359633521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10958503672176964479511361 8218877754132723359633521)
              ·
                refine ⟨6164158315599542519725141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8218877754132723359633521 6164158315599542519725141)
                ·
                  refine ⟨72236230260932138903029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 6164158315599542519725141 72236230260932138903029)
                  ·
                    rfl

theorem cell21_316529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 2, 8].length) (baseStart_316529 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_316529 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_316529 prefixEnd_316529 := by exact prefixLift 316529
  have htrace : WordTrace (prefixWord ++ tailWord_316529) baseStart_316529 baseEnd_316529 := by
    simpa [prefixWord, tailWord_316529, baseEnd_316529] using wordTrace_append hprefix tailTrace_316529
  have hstable : (prefixWord ++ tailWord_316529).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_316529).length < 2 ^ (prefixWord ++ tailWord_316529).sum := by decide
  have hdescent : baseEnd_316529 < baseStart_316529 := by decide
  rcases family_descends (prefixWord ++ tailWord_316529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_316653 : List Nat := [1, 5, 1, 2, 2, 2, 1, 7]
def baseStart_316653 : Nat := 118140960795 + 316653 * 2 ^ 59
def prefixEnd_316653 : Nat := 4983230072969 + 3 ^ 40 * 316653 * 2
def baseEnd_316653 : Nat := 24088176250111826278703

theorem tailTrace_316653 : CollatzResearch.WordTrace tailWord_316653 prefixEnd_316653 24088176250111826278703 := by
  unfold tailWord_316653
  simp only [CollatzResearch.WordTrace]
  refine ⟨11549283721827735871978613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7699522481218490581319075 11549283721827735871978613)
  ·
    refine ⟨1082745348921350237997995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 11549283721827735871978613 1082745348921350237997995)
    ·
      refine ⟨1624118023382025356996993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1082745348921350237997995 1624118023382025356996993)
      ·
        refine ⟨1218088517536519017747745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1624118023382025356996993 1218088517536519017747745)
        ·
          refine ⟨913566388152389263310809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1218088517536519017747745 913566388152389263310809)
          ·
            refine ⟨685174791114291947483107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 913566388152389263310809 685174791114291947483107)
            ·
              refine ⟨1027762186671437921224661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 685174791114291947483107 1027762186671437921224661)
              ·
                refine ⟨24088176250111826278703, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1027762186671437921224661 24088176250111826278703)
                ·
                  rfl

theorem cell21_316653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 2, 1, 7].length) (baseStart_316653 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_316653 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_316653 prefixEnd_316653 := by exact prefixLift 316653
  have htrace : WordTrace (prefixWord ++ tailWord_316653) baseStart_316653 baseEnd_316653 := by
    simpa [prefixWord, tailWord_316653, baseEnd_316653] using wordTrace_append hprefix tailTrace_316653
  have hstable : (prefixWord ++ tailWord_316653).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_316653).length < 2 ^ (prefixWord ++ tailWord_316653).sum := by decide
  have hdescent : baseEnd_316653 < baseStart_316653 := by decide
  rcases family_descends (prefixWord ++ tailWord_316653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_316681 : List Nat := [1, 2, 1, 1, 3, 3, 1, 3, 6]
def baseStart_316681 : Nat := 118140960795 + 316681 * 2 ^ 59
def prefixEnd_316681 : Nat := 4983230072969 + 3 ^ 40 * 316681 * 2
def baseEnd_316681 : Nat := 72270918731813652369385

theorem tailTrace_316681 : CollatzResearch.WordTrace tailWord_316681 prefixEnd_316681 72270918731813652369385 := by
  unfold tailWord_316681
  simp only [CollatzResearch.WordTrace]
  refine ⟨11550304965726296653997897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7700203310484197769331931 11550304965726296653997897)
  ·
    refine ⟨8662728724294722490498423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11550304965726296653997897 8662728724294722490498423)
    ·
      refine ⟨12994093086442083735747635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8662728724294722490498423 12994093086442083735747635)
      ·
        refine ⟨19491139629663125603621453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12994093086442083735747635 19491139629663125603621453)
        ·
          refine ⟨7309177361123672101358045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19491139629663125603621453 7309177361123672101358045)
          ·
            refine ⟨2740941510421377038009267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7309177361123672101358045 2740941510421377038009267)
            ·
              refine ⟨4111412265632065557013901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2740941510421377038009267 4111412265632065557013901)
              ·
                refine ⟨1541779599612024583880213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4111412265632065557013901 1541779599612024583880213)
                ·
                  refine ⟨72270918731813652369385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1541779599612024583880213 72270918731813652369385)
                  ·
                    rfl

theorem cell21_316681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 1, 3, 6].length) (baseStart_316681 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_316681 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_316681 prefixEnd_316681 := by exact prefixLift 316681
  have htrace : WordTrace (prefixWord ++ tailWord_316681) baseStart_316681 baseEnd_316681 := by
    simpa [prefixWord, tailWord_316681, baseEnd_316681] using wordTrace_append hprefix tailTrace_316681
  have hstable : (prefixWord ++ tailWord_316681).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_316681).length < 2 ^ (prefixWord ++ tailWord_316681).sum := by decide
  have hdescent : baseEnd_316681 < baseStart_316681 := by decide
  rcases family_descends (prefixWord ++ tailWord_316681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_316684 : List Nat := [2, 2, 1, 2, 2, 5, 1, 1, 5]
def baseStart_316684 : Nat := 118140960795 + 316684 * 2 ^ 59
def prefixEnd_316684 : Nat := 4983230072969 + 3 ^ 40 * 316684 * 2
def baseEnd_316684 : Nat := 72271603372686313819379

theorem tailTrace_316684 : CollatzResearch.WordTrace tailWord_316684 prefixEnd_316684 72271603372686313819379 := by
  unfold tailWord_316684
  simp only [CollatzResearch.WordTrace]
  refine ⟨5775207192357714083178553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7700276256476952110904737 5775207192357714083178553)
  ·
    refine ⟨4331405394268285562383915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5775207192357714083178553 4331405394268285562383915)
    ·
      refine ⟨6497108091402428343575873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4331405394268285562383915 6497108091402428343575873)
      ·
        refine ⟨4872831068551821257681905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6497108091402428343575873 4872831068551821257681905)
        ·
          refine ⟨3654623301413865943261429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4872831068551821257681905 3654623301413865943261429)
          ·
            refine ⟨342620934507549932180759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 3654623301413865943261429 342620934507549932180759)
            ·
              refine ⟨513931401761324898271139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 342620934507549932180759 513931401761324898271139)
              ·
                refine ⟨770897102641987347406709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 513931401761324898271139 770897102641987347406709)
                ·
                  refine ⟨72271603372686313819379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 770897102641987347406709 72271603372686313819379)
                  ·
                    rfl

theorem cell21_316684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 5, 1, 1, 5].length) (baseStart_316684 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_316684 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_316684 prefixEnd_316684 := by exact prefixLift 316684
  have htrace : WordTrace (prefixWord ++ tailWord_316684) baseStart_316684 baseEnd_316684 := by
    simpa [prefixWord, tailWord_316684, baseEnd_316684] using wordTrace_append hprefix tailTrace_316684
  have hstable : (prefixWord ++ tailWord_316684).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_316684).length < 2 ^ (prefixWord ++ tailWord_316684).sum := by decide
  have hdescent : baseEnd_316684 < baseStart_316684 := by decide
  rcases family_descends (prefixWord ++ tailWord_316684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_316690 : List Nat := [3, 2, 4, 2, 1, 2, 2, 1, 4]
def baseStart_316690 : Nat := 118140960795 + 316690 * 2 ^ 59
def prefixEnd_316690 : Nat := 4983230072969 + 3 ^ 40 * 316690 * 2
def baseEnd_316690 : Nat := 72272972654431636719367

theorem tailTrace_316690 : CollatzResearch.WordTrace tailWord_316690 prefixEnd_316690 72272972654431636719367 := by
  unfold tailWord_316690
  simp only [CollatzResearch.WordTrace]
  refine ⟨2887658305673422797768881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7700422148462460794050349 2887658305673422797768881)
  ·
    refine ⟨2165743729255067098326661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2887658305673422797768881 2165743729255067098326661)
    ·
      refine ⟨406076949235325080936249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2165743729255067098326661 406076949235325080936249)
      ·
        refine ⟨304557711926493810702187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 406076949235325080936249 304557711926493810702187)
        ·
          refine ⟨456836567889740716053281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 304557711926493810702187 456836567889740716053281)
          ·
            refine ⟨342627425917305537039961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 456836567889740716053281 342627425917305537039961)
            ·
              refine ⟨256970569437979152779971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 342627425917305537039961 256970569437979152779971)
              ·
                refine ⟨385455854156968729169957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 256970569437979152779971 385455854156968729169957)
                ·
                  refine ⟨72272972654431636719367, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 385455854156968729169957 72272972654431636719367)
                  ·
                    rfl

theorem cell21_316690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 2, 2, 1, 4].length) (baseStart_316690 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_316690 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_316690 prefixEnd_316690 := by exact prefixLift 316690
  have htrace : WordTrace (prefixWord ++ tailWord_316690) baseStart_316690 baseEnd_316690 := by
    simpa [prefixWord, tailWord_316690, baseEnd_316690] using wordTrace_append hprefix tailTrace_316690
  have hstable : (prefixWord ++ tailWord_316690).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_316690).length < 2 ^ (prefixWord ++ tailWord_316690).sum := by decide
  have hdescent : baseEnd_316690 < baseStart_316690 := by decide
  rcases family_descends (prefixWord ++ tailWord_316690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_316729 : List Nat := [1, 2, 1, 6, 3, 8]
def baseStart_316729 : Nat := 118140960795 + 316729 * 2 ^ 59
def prefixEnd_316729 : Nat := 4983230072969 + 3 ^ 40 * 316729 * 2
def baseEnd_316729 : Nat := 2677106406880601317381

theorem tailTrace_316729 : CollatzResearch.WordTrace tailWord_316729 prefixEnd_316729 2677106406880601317381 := by
  unfold tailWord_316729
  simp only [CollatzResearch.WordTrace]
  refine ⟨11552055669552400851745241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7701370446368267234496827 11552055669552400851745241)
  ·
    refine ⟨8664041752164300638808931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11552055669552400851745241 8664041752164300638808931)
    ·
      refine ⟨12996062628246450958213397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8664041752164300638808931 12996062628246450958213397)
      ·
        refine ⟨609190435699052388666253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 12996062628246450958213397 609190435699052388666253)
        ·
          refine ⟨228446413387144645749845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 609190435699052388666253 228446413387144645749845)
          ·
            refine ⟨2677106406880601317381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 228446413387144645749845 2677106406880601317381)
            ·
              rfl

theorem cell21_316729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 3, 8].length) (baseStart_316729 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_316729 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_316729 prefixEnd_316729 := by exact prefixLift 316729
  have htrace : WordTrace (prefixWord ++ tailWord_316729) baseStart_316729 baseEnd_316729 := by
    simpa [prefixWord, tailWord_316729, baseEnd_316729] using wordTrace_append hprefix tailTrace_316729
  have hstable : (prefixWord ++ tailWord_316729).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_316729).length < 2 ^ (prefixWord ++ tailWord_316729).sum := by decide
  have hdescent : baseEnd_316729 < baseStart_316729 := by decide
  rcases family_descends (prefixWord ++ tailWord_316729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_316912 : List Nat := [2, 1, 1, 1, 3, 5, 1, 4, 3]
def baseStart_316912 : Nat := 118140960795 + 316912 * 2 ^ 59
def prefixEnd_316912 : Nat := 4983230072969 + 3 ^ 40 * 316912 * 2
def baseEnd_316912 : Nat := 72323636079008584018913

theorem tailTrace_316912 : CollatzResearch.WordTrace tailWord_316912 prefixEnd_316912 72323636079008584018913 := by
  unfold tailWord_316912
  simp only [CollatzResearch.WordTrace]
  refine ⟨5779365113944711552828495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7705820151926282070437993 5779365113944711552828495)
  ·
    refine ⟨8669047670917067329242743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5779365113944711552828495 8669047670917067329242743)
    ·
      refine ⟨13003571506375600993864115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8669047670917067329242743 13003571506375600993864115)
      ·
        refine ⟨19505357259563401490796173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13003571506375600993864115 19505357259563401490796173)
        ·
          refine ⟨7314508972336275559048565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19505357259563401490796173 7314508972336275559048565)
          ·
            refine ⟨685735216156525833660803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 7314508972336275559048565 685735216156525833660803)
            ·
              refine ⟨1028602824234788750491205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 685735216156525833660803 1028602824234788750491205)
              ·
                refine ⟨192863029544022890717101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1028602824234788750491205 192863029544022890717101)
                ·
                  refine ⟨72323636079008584018913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 192863029544022890717101 72323636079008584018913)
                  ·
                    rfl

theorem cell21_316912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 5, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 5, 1, 4, 3].length) (baseStart_316912 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_316912 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_316912 prefixEnd_316912 := by exact prefixLift 316912
  have htrace : WordTrace (prefixWord ++ tailWord_316912) baseStart_316912 baseEnd_316912 := by
    simpa [prefixWord, tailWord_316912, baseEnd_316912] using wordTrace_append hprefix tailTrace_316912
  have hstable : (prefixWord ++ tailWord_316912).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_316912).length < 2 ^ (prefixWord ++ tailWord_316912).sum := by decide
  have hdescent : baseEnd_316912 < baseStart_316912 := by decide
  rcases family_descends (prefixWord ++ tailWord_316912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_316954 : List Nat := [3, 1, 1, 3, 1, 1, 1, 1, 9]
def baseStart_316954 : Nat := 118140960795 + 316954 * 2 ^ 59
def prefixEnd_316954 : Nat := 4983230072969 + 3 ^ 40 * 316954 * 2
def baseEnd_316954 : Nat := 72333221051225844318827

theorem tailTrace_316954 : CollatzResearch.WordTrace tailWord_316954 prefixEnd_316954 72333221051225844318827 := by
  unfold tailWord_316954
  simp only [CollatzResearch.WordTrace]
  refine ⟨2890065523434316069671479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7706841395824842852457277 2890065523434316069671479)
  ·
    refine ⟨4335098285151474104507219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2890065523434316069671479 4335098285151474104507219)
    ·
      refine ⟨6502647427727211156760829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4335098285151474104507219 6502647427727211156760829)
      ·
        refine ⟨2438492785397704183785311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6502647427727211156760829 2438492785397704183785311)
        ·
          refine ⟨3657739178096556275677967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2438492785397704183785311 3657739178096556275677967)
          ·
            refine ⟨5486608767144834413516951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3657739178096556275677967 5486608767144834413516951)
            ·
              refine ⟨8229913150717251620275427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5486608767144834413516951 8229913150717251620275427)
              ·
                refine ⟨12344869726075877430413141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8229913150717251620275427 12344869726075877430413141)
                ·
                  refine ⟨72333221051225844318827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 12344869726075877430413141 72333221051225844318827)
                  ·
                    rfl

theorem cell21_316954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 1, 9].length) (baseStart_316954 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_316954 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_316954 prefixEnd_316954 := by exact prefixLift 316954
  have htrace : WordTrace (prefixWord ++ tailWord_316954) baseStart_316954 baseEnd_316954 := by
    simpa [prefixWord, tailWord_316954, baseEnd_316954] using wordTrace_append hprefix tailTrace_316954
  have hstable : (prefixWord ++ tailWord_316954).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_316954).length < 2 ^ (prefixWord ++ tailWord_316954).sum := by decide
  have hdescent : baseEnd_316954 < baseStart_316954 := by decide
  rcases family_descends (prefixWord ++ tailWord_316954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_317092 : List Nat := [2, 3, 1, 2, 2, 2, 3, 6]
def baseStart_317092 : Nat := 118140960795 + 317092 * 2 ^ 59
def prefixEnd_317092 : Nat := 4983230072969 + 3 ^ 40 * 317092 * 2
def baseEnd_317092 : Nat := 24121571510456090339515

theorem tailTrace_317092 : CollatzResearch.WordTrace tailWord_317092 prefixEnd_317092 24121571510456090339515 := by
  unfold tailWord_317092
  simp only [CollatzResearch.WordTrace]
  refine ⟨5782647683618656923604765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7710196911491542564806353 5782647683618656923604765)
  ·
    refine ⟨2168492881356996346351787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5782647683618656923604765 2168492881356996346351787)
    ·
      refine ⟨3252739322035494519527681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2168492881356996346351787 3252739322035494519527681)
      ·
        refine ⟨2439554491526620889645761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3252739322035494519527681 2439554491526620889645761)
        ·
          refine ⟨1829665868644965667234321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2439554491526620889645761 1829665868644965667234321)
          ·
            refine ⟨1372249401483724250425741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1829665868644965667234321 1372249401483724250425741)
            ·
              refine ⟨514593525556396593909653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1372249401483724250425741 514593525556396593909653)
              ·
                refine ⟨24121571510456090339515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 514593525556396593909653 24121571510456090339515)
                ·
                  rfl

theorem cell21_317092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 3, 6].length) (baseStart_317092 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_317092 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_317092 prefixEnd_317092 := by exact prefixLift 317092
  have htrace : WordTrace (prefixWord ++ tailWord_317092) baseStart_317092 baseEnd_317092 := by
    simpa [prefixWord, tailWord_317092, baseEnd_317092] using wordTrace_append hprefix tailTrace_317092
  have hstable : (prefixWord ++ tailWord_317092).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_317092).length < 2 ^ (prefixWord ++ tailWord_317092).sum := by decide
  have hdescent : baseEnd_317092 < baseStart_317092 := by decide
  rcases family_descends (prefixWord ++ tailWord_317092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_317106 : List Nat := [3, 2, 1, 1, 1, 2, 3, 1, 7]
def baseStart_317106 : Nat := 118140960795 + 317106 * 2 ^ 59
def prefixEnd_317106 : Nat := 4983230072969 + 3 ^ 40 * 317106 * 2
def baseEnd_317106 : Nat := 72367909522107357785183

theorem tailTrace_317106 : CollatzResearch.WordTrace tailWord_317106 prefixEnd_317106 72367909522107357785183 := by
  unfold tailWord_317106
  simp only [CollatzResearch.WordTrace]
  refine ⟨2891451497296648559554793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7710537326124396158812781 2891451497296648559554793)
  ·
    refine ⟨2168588622972486419666095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2891451497296648559554793 2168588622972486419666095)
    ·
      refine ⟨3252882934458729629499143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2168588622972486419666095 3252882934458729629499143)
      ·
        refine ⟨4879324401688094444248715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3252882934458729629499143 4879324401688094444248715)
        ·
          refine ⟨7318986602532141666373073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4879324401688094444248715 7318986602532141666373073)
          ·
            refine ⟨5489239951899106249779805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7318986602532141666373073 5489239951899106249779805)
            ·
              refine ⟨2058464981962164843667427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5489239951899106249779805 2058464981962164843667427)
              ·
                refine ⟨3087697472943247265501141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2058464981962164843667427 3087697472943247265501141)
                ·
                  refine ⟨72367909522107357785183, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3087697472943247265501141 72367909522107357785183)
                  ·
                    rfl

theorem cell21_317106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 3, 1, 7].length) (baseStart_317106 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_317106 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_317106 prefixEnd_317106 := by exact prefixLift 317106
  have htrace : WordTrace (prefixWord ++ tailWord_317106) baseStart_317106 baseEnd_317106 := by
    simpa [prefixWord, tailWord_317106, baseEnd_317106] using wordTrace_append hprefix tailTrace_317106
  have hstable : (prefixWord ++ tailWord_317106).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_317106).length < 2 ^ (prefixWord ++ tailWord_317106).sum := by decide
  have hdescent : baseEnd_317106 < baseStart_317106 := by decide
  rcases family_descends (prefixWord ++ tailWord_317106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_317126 : List Nat := [6, 1, 2, 1, 1, 2, 8]
def baseStart_317126 : Nat := 118140960795 + 317126 * 2 ^ 59
def prefixEnd_317126 : Nat := 4983230072969 + 3 ^ 40 * 317126 * 2
def baseEnd_317126 : Nat := 8041385977176863050201

theorem tailTrace_317126 : CollatzResearch.WordTrace tailWord_317126 prefixEnd_317126 8041385977176863050201 := by
  unfold tailWord_317126
  simp only [CollatzResearch.WordTrace]
  refine ⟨361454232784816801685851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 7711023632742758435964821 361454232784816801685851)
  ·
    refine ⟨542181349177225202528777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 361454232784816801685851 542181349177225202528777)
    ·
      refine ⟨406636011882918901896583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 542181349177225202528777 406636011882918901896583)
      ·
        refine ⟨609954017824378352844875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 406636011882918901896583 609954017824378352844875)
        ·
          refine ⟨914931026736567529267313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 609954017824378352844875 914931026736567529267313)
          ·
            refine ⟨686198270052425646950485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 914931026736567529267313 686198270052425646950485)
            ·
              refine ⟨8041385977176863050201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 686198270052425646950485 8041385977176863050201)
              ·
                rfl

theorem cell21_317126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 2, 8].length) (baseStart_317126 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_317126 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_317126 prefixEnd_317126 := by exact prefixLift 317126
  have htrace : WordTrace (prefixWord ++ tailWord_317126) baseStart_317126 baseEnd_317126 := by
    simpa [prefixWord, tailWord_317126, baseEnd_317126] using wordTrace_append hprefix tailTrace_317126
  have hstable : (prefixWord ++ tailWord_317126).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_317126).length < 2 ^ (prefixWord ++ tailWord_317126).sum := by decide
  have hdescent : baseEnd_317126 < baseStart_317126 := by decide
  rcases family_descends (prefixWord ++ tailWord_317126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_317137 : List Nat := [1, 2, 2, 1, 2, 5, 1, 1, 6]
def baseStart_317137 : Nat := 118140960795 + 317137 * 2 ^ 59
def prefixEnd_317137 : Nat := 4983230072969 + 3 ^ 40 * 317137 * 2
def baseEnd_317137 : Nat := 72374984144458192768453

theorem tailTrace_317137 : CollatzResearch.WordTrace tailWord_317137 prefixEnd_317137 72374984144458192768453 := by
  unfold tailWord_317137
  simp only [CollatzResearch.WordTrace]
  refine ⟨11566936652074286532597665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7711291101382857688398443 11566936652074286532597665)
  ·
    refine ⟨8675202489055714899448249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11566936652074286532597665 8675202489055714899448249)
    ·
      refine ⟨6506401866791786174586187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8675202489055714899448249 6506401866791786174586187)
      ·
        refine ⟨9759602800187679261879281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6506401866791786174586187 9759602800187679261879281)
        ·
          refine ⟨7319702100140759446409461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9759602800187679261879281 7319702100140759446409461)
          ·
            refine ⟨686222071888196198100887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 7319702100140759446409461 686222071888196198100887)
            ·
              refine ⟨1029333107832294297151331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 686222071888196198100887 1029333107832294297151331)
              ·
                refine ⟨1543999661748441445726997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1029333107832294297151331 1543999661748441445726997)
                ·
                  refine ⟨72374984144458192768453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1543999661748441445726997 72374984144458192768453)
                  ·
                    rfl

theorem cell21_317137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 5, 1, 1, 6].length) (baseStart_317137 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_317137 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_317137 prefixEnd_317137 := by exact prefixLift 317137
  have htrace : WordTrace (prefixWord ++ tailWord_317137) baseStart_317137 baseEnd_317137 := by
    simpa [prefixWord, tailWord_317137, baseEnd_317137] using wordTrace_append hprefix tailTrace_317137
  have hstable : (prefixWord ++ tailWord_317137).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_317137).length < 2 ^ (prefixWord ++ tailWord_317137).sum := by decide
  have hdescent : baseEnd_317137 < baseStart_317137 := by decide
  rcases family_descends (prefixWord ++ tailWord_317137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_317140 : List Nat := [2, 4, 1, 3, 1, 2, 2, 1, 5]
def baseStart_317140 : Nat := 118140960795 + 317140 * 2 ^ 59
def prefixEnd_317140 : Nat := 4983230072969 + 3 ^ 40 * 317140 * 2
def baseEnd_317140 : Nat := 72375668785330854218447

theorem tailTrace_317140 : CollatzResearch.WordTrace tailWord_317140 prefixEnd_317140 72375668785330854218447 := by
  unfold tailWord_317140
  simp only [CollatzResearch.WordTrace]
  refine ⟨5783523035531709022478437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7711364047375612029971249 5783523035531709022478437)
  ·
    refine ⟨1084410569162195441714707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5783523035531709022478437 1084410569162195441714707)
    ·
      refine ⟨1626615853743293162572061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1084410569162195441714707 1626615853743293162572061)
      ·
        refine ⟨609980945153734935964523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1626615853743293162572061 609980945153734935964523)
        ·
          refine ⟨914971417730602403946785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 609980945153734935964523 914971417730602403946785)
          ·
            refine ⟨686228563297951802960089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 914971417730602403946785 686228563297951802960089)
            ·
              refine ⟨514671422473463852220067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 686228563297951802960089 514671422473463852220067)
              ·
                refine ⟨772007133710195778330101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 514671422473463852220067 772007133710195778330101)
                ·
                  refine ⟨72375668785330854218447, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 772007133710195778330101 72375668785330854218447)
                  ·
                    rfl

theorem cell21_317140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 2, 2, 1, 5].length) (baseStart_317140 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_317140 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_317140 prefixEnd_317140 := by exact prefixLift 317140
  have htrace : WordTrace (prefixWord ++ tailWord_317140) baseStart_317140 baseEnd_317140 := by
    simpa [prefixWord, tailWord_317140, baseEnd_317140] using wordTrace_append hprefix tailTrace_317140
  have hstable : (prefixWord ++ tailWord_317140).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_317140).length < 2 ^ (prefixWord ++ tailWord_317140).sum := by decide
  have hdescent : baseEnd_317140 < baseStart_317140 := by decide
  rcases family_descends (prefixWord ++ tailWord_317140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_317151 : List Nat := [1, 1, 2, 3, 2, 2, 2, 8]
def baseStart_317151 : Nat := 118140960795 + 317151 * 2 ^ 59
def prefixEnd_317151 : Nat := 4983230072969 + 3 ^ 40 * 317151 * 2
def baseEnd_317151 : Nat := 24126059711732426511697

theorem tailTrace_317151 : CollatzResearch.WordTrace tailWord_317151 prefixEnd_317151 24126059711732426511697 := by
  unfold tailWord_317151
  simp only [CollatzResearch.WordTrace]
  refine ⟨11567447274023566923607307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7711631516015711282404871 11567447274023566923607307)
  ·
    refine ⟨17351170911035350385410961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11567447274023566923607307 17351170911035350385410961)
    ·
      refine ⟨13013378183276512789058221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17351170911035350385410961 13013378183276512789058221)
      ·
        refine ⟨4880016818728692295896833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13013378183276512789058221 4880016818728692295896833)
        ·
          refine ⟨3660012614046519221922625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4880016818728692295896833 3660012614046519221922625)
          ·
            refine ⟨2745009460534889416441969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3660012614046519221922625 2745009460534889416441969)
            ·
              refine ⟨2058757095401167062331477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2745009460534889416441969 2058757095401167062331477)
              ·
                refine ⟨24126059711732426511697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2058757095401167062331477 24126059711732426511697)
                ·
                  rfl

theorem cell21_317151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 2, 8].length) (baseStart_317151 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_317151 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_317151 prefixEnd_317151 := by exact prefixLift 317151
  have htrace : WordTrace (prefixWord ++ tailWord_317151) baseStart_317151 baseEnd_317151 := by
    simpa [prefixWord, tailWord_317151, baseEnd_317151] using wordTrace_append hprefix tailTrace_317151
  have hstable : (prefixWord ++ tailWord_317151).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_317151).length < 2 ^ (prefixWord ++ tailWord_317151).sum := by decide
  have hdescent : baseEnd_317151 < baseStart_317151 := by decide
  rcases family_descends (prefixWord ++ tailWord_317151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_317258 : List Nat := [3, 1, 2, 1, 1, 1, 4, 3, 5]
def baseStart_317258 : Nat := 118140960795 + 317258 * 2 ^ 59
def prefixEnd_317258 : Nat := 4983230072969 + 3 ^ 40 * 317258 * 2
def baseEnd_317258 : Nat := 72402597992988871251539

theorem tailTrace_317258 : CollatzResearch.WordTrace tailWord_317258 prefixEnd_317258 72402597992988871251539 := by
  unfold tailWord_317258
  simp only [CollatzResearch.WordTrace]
  refine ⟨2892837471158981049438107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7714233256423949465168285 2892837471158981049438107)
  ·
    refine ⟨4339256206738471574157161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2892837471158981049438107 4339256206738471574157161)
    ·
      refine ⟨3254442155053853680617871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4339256206738471574157161 3254442155053853680617871)
      ·
        refine ⟨4881663232580780520926807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3254442155053853680617871 4881663232580780520926807)
        ·
          refine ⟨7322494848871170781390211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4881663232580780520926807 7322494848871170781390211)
          ·
            refine ⟨10983742273306756172085317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7322494848871170781390211 10983742273306756172085317)
            ·
              refine ⟨2059451676245016782265997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10983742273306756172085317 2059451676245016782265997)
              ·
                refine ⟨772294378591881293349749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2059451676245016782265997 772294378591881293349749)
                ·
                  refine ⟨72402597992988871251539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 772294378591881293349749 72402597992988871251539)
                  ·
                    rfl

theorem cell21_317258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 4, 3, 5].length) (baseStart_317258 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_317258 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_317258 prefixEnd_317258 := by exact prefixLift 317258
  have htrace : WordTrace (prefixWord ++ tailWord_317258) baseStart_317258 baseEnd_317258 := by
    simpa [prefixWord, tailWord_317258, baseEnd_317258] using wordTrace_append hprefix tailTrace_317258
  have hstable : (prefixWord ++ tailWord_317258).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_317258).length < 2 ^ (prefixWord ++ tailWord_317258).sum := by decide
  have hdescent : baseEnd_317258 < baseStart_317258 := by decide
  rcases family_descends (prefixWord ++ tailWord_317258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_317261 : List Nat := [1, 6, 1, 2, 1, 1, 3, 6]
def baseStart_317261 : Nat := 118140960795 + 317261 * 2 ^ 59
def prefixEnd_317261 : Nat := 4983230072969 + 3 ^ 40 * 317261 * 2
def baseEnd_317261 : Nat := 24134427544620510900511

theorem tailTrace_317261 : CollatzResearch.WordTrace tailWord_317261 prefixEnd_317261 24134427544620510900511 := by
  unfold tailWord_317261
  simp only [CollatzResearch.WordTrace]
  refine ⟨11571459303625055710111637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7714306202416703806741091 11571459303625055710111637)
  ·
    refine ⟨542412154857424486411483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 11571459303625055710111637 542412154857424486411483)
    ·
      refine ⟨813618232286136729617225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 542412154857424486411483 813618232286136729617225)
      ·
        refine ⟨610213674214602547212919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 813618232286136729617225 610213674214602547212919)
        ·
          refine ⟨915320511321903820819379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 610213674214602547212919 915320511321903820819379)
          ·
            refine ⟨1372980766982855731229069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 915320511321903820819379 1372980766982855731229069)
            ·
              refine ⟨514867787618570899210901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1372980766982855731229069 514867787618570899210901)
              ·
                refine ⟨24134427544620510900511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 514867787618570899210901 24134427544620510900511)
                ·
                  rfl

theorem cell21_317261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 3, 6].length) (baseStart_317261 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_317261 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_317261 prefixEnd_317261 := by exact prefixLift 317261
  have htrace : WordTrace (prefixWord ++ tailWord_317261) baseStart_317261 baseEnd_317261 := by
    simpa [prefixWord, tailWord_317261, baseEnd_317261] using wordTrace_append hprefix tailTrace_317261
  have hstable : (prefixWord ++ tailWord_317261).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_317261).length < 2 ^ (prefixWord ++ tailWord_317261).sum := by decide
  have hdescent : baseEnd_317261 < baseStart_317261 := by decide
  rcases family_descends (prefixWord ++ tailWord_317261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_317272 : List Nat := [2, 1, 2, 2, 1, 1, 1, 1, 10]
def baseStart_317272 : Nat := 118140960795 + 317272 * 2 ^ 59
def prefixEnd_317272 : Nat := 4983230072969 + 3 ^ 40 * 317272 * 2
def baseEnd_317272 : Nat := 72405792983727958018177

theorem tailTrace_317272 : CollatzResearch.WordTrace tailWord_317272 prefixEnd_317272 72405792983727958018177 := by
  unfold tailWord_317272
  simp only [CollatzResearch.WordTrace]
  refine ⟨5785930253292602294381035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7714573671056803059174713 5785930253292602294381035)
  ·
    refine ⟨8678895379938903441571553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5785930253292602294381035 8678895379938903441571553)
    ·
      refine ⟨6509171534954177581178665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8678895379938903441571553 6509171534954177581178665)
      ·
        refine ⟨4881878651215633185883999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6509171534954177581178665 4881878651215633185883999)
        ·
          refine ⟨7322817976823449778825999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4881878651215633185883999 7322817976823449778825999)
          ·
            refine ⟨10984226965235174668238999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7322817976823449778825999 10984226965235174668238999)
            ·
              refine ⟨16476340447852762002358499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10984226965235174668238999 16476340447852762002358499)
              ·
                refine ⟨24714510671779143003537749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16476340447852762002358499 24714510671779143003537749)
                ·
                  refine ⟨72405792983727958018177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 24714510671779143003537749 72405792983727958018177)
                  ·
                    rfl

theorem cell21_317272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 1, 10].length) (baseStart_317272 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_317272 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_317272 prefixEnd_317272 := by exact prefixLift 317272
  have htrace : WordTrace (prefixWord ++ tailWord_317272) baseStart_317272 baseEnd_317272 := by
    simpa [prefixWord, tailWord_317272, baseEnd_317272] using wordTrace_append hprefix tailTrace_317272
  have hstable : (prefixWord ++ tailWord_317272).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_317272).length < 2 ^ (prefixWord ++ tailWord_317272).sum := by decide
  have hdescent : baseEnd_317272 < baseStart_317272 := by decide
  rcases family_descends (prefixWord ++ tailWord_317272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_317292 : List Nat := [2, 2, 1, 1, 4, 3, 2, 3, 3]
def baseStart_317292 : Nat := 118140960795 + 317292 * 2 ^ 59
def prefixEnd_317292 : Nat := 4983230072969 + 3 ^ 40 * 317292 * 2
def baseEnd_317292 : Nat := 72410357256212367684803

theorem tailTrace_317292 : CollatzResearch.WordTrace tailWord_317292 prefixEnd_317292 72410357256212367684803 := by
  unfold tailWord_317292
  simp only [CollatzResearch.WordTrace]
  refine ⟨5786294983256374002245065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7715059977675165336326753 5786294983256374002245065)
  ·
    refine ⟨4339721237442280501683799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5786294983256374002245065 4339721237442280501683799)
    ·
      refine ⟨6509581856163420752525699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4339721237442280501683799 6509581856163420752525699)
      ·
        refine ⟨9764372784245131128788549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6509581856163420752525699 9764372784245131128788549)
        ·
          refine ⟨1830819897045962086647853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9764372784245131128788549 1830819897045962086647853)
          ·
            refine ⟨686557461392235782492945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1830819897045962086647853 686557461392235782492945)
            ·
              refine ⟨514918096044176836869709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 686557461392235782492945 514918096044176836869709)
              ·
                refine ⟨193094286016566313826141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 514918096044176836869709 193094286016566313826141)
                ·
                  refine ⟨72410357256212367684803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 193094286016566313826141 72410357256212367684803)
                  ·
                    rfl

theorem cell21_317292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 3, 2, 3, 3].length) (baseStart_317292 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_317292 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_317292 prefixEnd_317292 := by exact prefixLift 317292
  have htrace : WordTrace (prefixWord ++ tailWord_317292) baseStart_317292 baseEnd_317292 := by
    simpa [prefixWord, tailWord_317292, baseEnd_317292] using wordTrace_append hprefix tailTrace_317292
  have hstable : (prefixWord ++ tailWord_317292).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_317292).length < 2 ^ (prefixWord ++ tailWord_317292).sum := by decide
  have hdescent : baseEnd_317292 < baseStart_317292 := by decide
  rcases family_descends (prefixWord ++ tailWord_317292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_317365 : List Nat := [1, 3, 3, 2, 1, 2, 2, 1, 6]
def baseStart_317365 : Nat := 118140960795 + 317365 * 2 ^ 59
def prefixEnd_317365 : Nat := 4983230072969 + 3 ^ 40 * 317365 * 2
def baseEnd_317365 : Nat := 72427016850780462967987

theorem tailTrace_317365 : CollatzResearch.WordTrace tailWord_317365 prefixEnd_317365 72427016850780462967987 := by
  unfold tailWord_317365
  simp only [CollatzResearch.WordTrace]
  refine ⟨11575252495248281471897549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7716834996832187647931699 11575252495248281471897549)
  ·
    refine ⟨4340719685718105551961581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11575252495248281471897549 4340719685718105551961581)
    ·
      refine ⟨1627769882144289581985593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4340719685718105551961581 1627769882144289581985593)
      ·
        refine ⟨1220827411608217186489195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1627769882144289581985593 1220827411608217186489195)
        ·
          refine ⟨1831241117412325779733793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1220827411608217186489195 1831241117412325779733793)
          ·
            refine ⟨1373430838059244334800345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1831241117412325779733793 1373430838059244334800345)
            ·
              refine ⟨1030073128544433251100259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1373430838059244334800345 1030073128544433251100259)
              ·
                refine ⟨1545109692816649876650389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1030073128544433251100259 1545109692816649876650389)
                ·
                  refine ⟨72427016850780462967987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1545109692816649876650389 72427016850780462967987)
                  ·
                    rfl

theorem cell21_317365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 2, 1, 6].length) (baseStart_317365 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_317365 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_317365 prefixEnd_317365 := by exact prefixLift 317365
  have htrace : WordTrace (prefixWord ++ tailWord_317365) baseStart_317365 baseEnd_317365 := by
    simpa [prefixWord, tailWord_317365, baseEnd_317365] using wordTrace_append hprefix tailTrace_317365
  have hstable : (prefixWord ++ tailWord_317365).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_317365).length < 2 ^ (prefixWord ++ tailWord_317365).sum := by decide
  have hdescent : baseEnd_317365 < baseStart_317365 := by decide
  rcases family_descends (prefixWord ++ tailWord_317365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_317368 : List Nat := [2, 1, 2, 1, 2, 3, 5, 2, 3]
def baseStart_317368 : Nat := 118140960795 + 317368 * 2 ^ 59
def prefixEnd_317368 : Nat := 4983230072969 + 3 ^ 40 * 317368 * 2
def baseEnd_317368 : Nat := 72427701491653124417981

theorem tailTrace_317368 : CollatzResearch.WordTrace tailWord_317368 prefixEnd_317368 72427701491653124417981 := by
  unfold tailWord_317368
  simp only [CollatzResearch.WordTrace]
  refine ⟨5787680957118706492128379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7716907942824941989504505 5787680957118706492128379)
  ·
    refine ⟨8681521435678059738192569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5787680957118706492128379 8681521435678059738192569)
    ·
      refine ⟨6511141076758544803644427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8681521435678059738192569 6511141076758544803644427)
      ·
        refine ⟨9766711615137817205466641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6511141076758544803644427 9766711615137817205466641)
        ·
          refine ⟨7325033711353362904099981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9766711615137817205466641 7325033711353362904099981)
          ·
            refine ⟨2746887641757511089037493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7325033711353362904099981 2746887641757511089037493)
            ·
              refine ⟨257520716414766664597265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2746887641757511089037493 257520716414766664597265)
              ·
                refine ⟨193140537311074998447949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 257520716414766664597265 193140537311074998447949)
                ·
                  refine ⟨72427701491653124417981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 193140537311074998447949 72427701491653124417981)
                  ·
                    rfl

theorem cell21_317368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 5, 2, 3].length) (baseStart_317368 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_317368 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_317368 prefixEnd_317368 := by exact prefixLift 317368
  have htrace : WordTrace (prefixWord ++ tailWord_317368) baseStart_317368 baseEnd_317368 := by
    simpa [prefixWord, tailWord_317368, baseEnd_317368] using wordTrace_append hprefix tailTrace_317368
  have hstable : (prefixWord ++ tailWord_317368).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_317368).length < 2 ^ (prefixWord ++ tailWord_317368).sum := by decide
  have hdescent : baseEnd_317368 < baseStart_317368 := by decide
  rcases family_descends (prefixWord ++ tailWord_317368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_317424 : List Nat := [2, 1, 1, 1, 3, 2, 2, 3, 6]
def baseStart_317424 : Nat := 118140960795 + 317424 * 2 ^ 59
def prefixEnd_317424 : Nat := 4983230072969 + 3 ^ 40 * 317424 * 2
def baseEnd_317424 : Nat := 72440481454609471484533

theorem tailTrace_317424 : CollatzResearch.WordTrace tailWord_317424 prefixEnd_317424 72440481454609471484533 := by
  unfold tailWord_317424
  simp only [CollatzResearch.WordTrace]
  refine ⟨5788702201017267274147663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7718269601356356365530217 5788702201017267274147663)
  ·
    refine ⟨8683053301525900911221495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5788702201017267274147663 8683053301525900911221495)
    ·
      refine ⟨13024579952288851366832243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8683053301525900911221495 13024579952288851366832243)
      ·
        refine ⟨19536869928433277050248365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13024579952288851366832243 19536869928433277050248365)
        ·
          refine ⟨7326326223162478893843137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19536869928433277050248365 7326326223162478893843137)
          ·
            refine ⟨5494744667371859170382353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7326326223162478893843137 5494744667371859170382353)
            ·
              refine ⟨4121058500528894377786765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5494744667371859170382353 4121058500528894377786765)
              ·
                refine ⟨1545396937698335391670037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4121058500528894377786765 1545396937698335391670037)
                ·
                  refine ⟨72440481454609471484533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1545396937698335391670037 72440481454609471484533)
                  ·
                    rfl

theorem cell21_317424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 2, 3, 6].length) (baseStart_317424 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_317424 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_317424 prefixEnd_317424 := by exact prefixLift 317424
  have htrace : WordTrace (prefixWord ++ tailWord_317424) baseStart_317424 baseEnd_317424 := by
    simpa [prefixWord, tailWord_317424, baseEnd_317424] using wordTrace_append hprefix tailTrace_317424
  have hstable : (prefixWord ++ tailWord_317424).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_317424).length < 2 ^ (prefixWord ++ tailWord_317424).sum := by decide
  have hdescent : baseEnd_317424 < baseStart_317424 := by decide
  rcases family_descends (prefixWord ++ tailWord_317424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_317430 : List Nat := [5, 1, 1, 1, 5, 1, 1, 6]
def baseStart_317430 : Nat := 118140960795 + 317430 * 2 ^ 59
def prefixEnd_317430 : Nat := 4983230072969 + 3 ^ 40 * 317430 * 2
def baseEnd_317430 : Nat := 24147283578784931461507

theorem tailTrace_317430 : CollatzResearch.WordTrace tailWord_317430 prefixEnd_317430 24147283578784931461507 := by
  unfold tailWord_317430
  simp only [CollatzResearch.WordTrace]
  refine ⟨723601452500799848313359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 7718415493341865048675829 723601452500799848313359)
  ·
    refine ⟨1085402178751199772470039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 723601452500799848313359 1085402178751199772470039)
    ·
      refine ⟨1628103268126799658705059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1085402178751199772470039 1628103268126799658705059)
      ·
        refine ⟨2442154902190199488057589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1628103268126799658705059 2442154902190199488057589)
        ·
          refine ⟨228952022080331202005399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 2442154902190199488057589 228952022080331202005399)
          ·
            refine ⟨343428033120496803008099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 228952022080331202005399 343428033120496803008099)
            ·
              refine ⟨515142049680745204512149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 343428033120496803008099 515142049680745204512149)
              ·
                refine ⟨24147283578784931461507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 515142049680745204512149 24147283578784931461507)
                ·
                  rfl

theorem cell21_317430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 5, 1, 1, 6].length) (baseStart_317430 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_317430 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_317430 prefixEnd_317430 := by exact prefixLift 317430
  have htrace : WordTrace (prefixWord ++ tailWord_317430) baseStart_317430 baseEnd_317430 := by
    simpa [prefixWord, tailWord_317430, baseEnd_317430] using wordTrace_append hprefix tailTrace_317430
  have hstable : (prefixWord ++ tailWord_317430).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_317430).length < 2 ^ (prefixWord ++ tailWord_317430).sum := by decide
  have hdescent : baseEnd_317430 < baseStart_317430 := by decide
  rcases family_descends (prefixWord ++ tailWord_317430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_317441 : List Nat := [1, 2, 4, 1, 2, 1, 1, 5, 4]
def baseStart_317441 : Nat := 118140960795 + 317441 * 2 ^ 59
def prefixEnd_317441 : Nat := 4983230072969 + 3 ^ 40 * 317441 * 2
def baseEnd_317441 : Nat := 72444361086221219701165

theorem tailTrace_317441 : CollatzResearch.WordTrace tailWord_317441 prefixEnd_317441 72444361086221219701165 := by
  unfold tailWord_317441
  simp only [CollatzResearch.WordTrace]
  refine ⟨11578024442972946451664177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7718682961981964301109451 11578024442972946451664177)
  ·
    refine ⟨8683518332229709838748133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11578024442972946451664177 8683518332229709838748133)
    ·
      refine ⟨1628159687293070594765275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8683518332229709838748133 1628159687293070594765275)
      ·
        refine ⟨2442239530939605892147913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1628159687293070594765275 2442239530939605892147913)
        ·
          refine ⟨1831679648204704419110935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2442239530939605892147913 1831679648204704419110935)
          ·
            refine ⟨2747519472307056628666403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1831679648204704419110935 2747519472307056628666403)
            ·
              refine ⟨4121279208460584942999605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2747519472307056628666403 4121279208460584942999605)
              ·
                refine ⟨386369925793179838406213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4121279208460584942999605 386369925793179838406213)
                ·
                  refine ⟨72444361086221219701165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 386369925793179838406213 72444361086221219701165)
                  ·
                    rfl

theorem cell21_317441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 1, 5, 4].length) (baseStart_317441 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_317441 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_317441 prefixEnd_317441 := by exact prefixLift 317441
  have htrace : WordTrace (prefixWord ++ tailWord_317441) baseStart_317441 baseEnd_317441 := by
    simpa [prefixWord, tailWord_317441, baseEnd_317441] using wordTrace_append hprefix tailTrace_317441
  have hstable : (prefixWord ++ tailWord_317441).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_317441).length < 2 ^ (prefixWord ++ tailWord_317441).sum := by decide
  have hdescent : baseEnd_317441 < baseStart_317441 := by decide
  rcases family_descends (prefixWord ++ tailWord_317441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_317444 : List Nat := [2, 3, 2, 4, 1, 1, 1, 2, 5]
def baseStart_317444 : Nat := 118140960795 + 317444 * 2 ^ 59
def prefixEnd_317444 : Nat := 4983230072969 + 3 ^ 40 * 317444 * 2
def baseEnd_317444 : Nat := 72445045727093881151159

theorem tailTrace_317444 : CollatzResearch.WordTrace tailWord_317444 prefixEnd_317444 72445045727093881151159 := by
  unfold tailWord_317444
  simp only [CollatzResearch.WordTrace]
  refine ⟨5789066930981038982011693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7718755907974718642682257 5789066930981038982011693)
  ·
    refine ⟨2170900099117889618254385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5789066930981038982011693 2170900099117889618254385)
    ·
      refine ⟨1628175074338417213690789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2170900099117889618254385 1628175074338417213690789)
      ·
        refine ⟨305282826438453227567023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1628175074338417213690789 305282826438453227567023)
        ·
          refine ⟨457924239657679841350535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 305282826438453227567023 457924239657679841350535)
          ·
            refine ⟨686886359486519762025803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 457924239657679841350535 686886359486519762025803)
            ·
              refine ⟨1030329539229779643038705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 686886359486519762025803 1030329539229779643038705)
              ·
                refine ⟨772747154422334732279029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1030329539229779643038705 772747154422334732279029)
                ·
                  refine ⟨72445045727093881151159, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 772747154422334732279029 72445045727093881151159)
                  ·
                    rfl

theorem cell21_317444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 1, 1, 2, 5].length) (baseStart_317444 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_317444 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_317444 prefixEnd_317444 := by exact prefixLift 317444
  have htrace : WordTrace (prefixWord ++ tailWord_317444) baseStart_317444 baseEnd_317444 := by
    simpa [prefixWord, tailWord_317444, baseEnd_317444] using wordTrace_append hprefix tailTrace_317444
  have hstable : (prefixWord ++ tailWord_317444).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_317444).length < 2 ^ (prefixWord ++ tailWord_317444).sum := by decide
  have hdescent : baseEnd_317444 < baseStart_317444 := by decide
  rcases family_descends (prefixWord ++ tailWord_317444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_317492 : List Nat := [2, 5, 1, 2, 2, 1, 3, 1, 4]
def baseStart_317492 : Nat := 118140960795 + 317492 * 2 ^ 59
def prefixEnd_317492 : Nat := 4983230072969 + 3 ^ 40 * 317492 * 2
def baseEnd_317492 : Nat := 72455999981056464351061

theorem tailTrace_317492 : CollatzResearch.WordTrace tailWord_317492 prefixEnd_317492 72455999981056464351061 := by
  unfold tailWord_317492
  simp only [CollatzResearch.WordTrace]
  refine ⟨5789942282894091080885365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7719923043858788107847153 5789942282894091080885365)
  ·
    refine ⟨542807089021321038833003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 5789942282894091080885365 542807089021321038833003)
    ·
      refine ⟨814210633531981558249505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 542807089021321038833003 814210633531981558249505)
      ·
        refine ⟨610657975148986168687129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 814210633531981558249505 610657975148986168687129)
        ·
          refine ⟨457993481361739626515347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 610657975148986168687129 457993481361739626515347)
          ·
            refine ⟨686990222042609439773021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 457993481361739626515347 686990222042609439773021)
            ·
              refine ⟨257621333265978539914883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 686990222042609439773021 257621333265978539914883)
              ·
                refine ⟨386431999898967809872325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 257621333265978539914883 386431999898967809872325)
                ·
                  refine ⟨72455999981056464351061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 386431999898967809872325 72455999981056464351061)
                  ·
                    rfl

theorem cell21_317492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 1, 3, 1, 4].length) (baseStart_317492 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_317492 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_317492 prefixEnd_317492 := by exact prefixLift 317492
  have htrace : WordTrace (prefixWord ++ tailWord_317492) baseStart_317492 baseEnd_317492 := by
    simpa [prefixWord, tailWord_317492, baseEnd_317492] using wordTrace_append hprefix tailTrace_317492
  have hstable : (prefixWord ++ tailWord_317492).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_317492).length < 2 ^ (prefixWord ++ tailWord_317492).sum := by decide
  have hdescent : baseEnd_317492 < baseStart_317492 := by decide
  rcases family_descends (prefixWord ++ tailWord_317492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_317517 : List Nat := [1, 6, 1, 1, 1, 1, 1, 1, 8]
def baseStart_317517 : Nat := 118140960795 + 317517 * 2 ^ 59
def prefixEnd_317517 : Nat := 4983230072969 + 3 ^ 40 * 317517 * 2
def baseEnd_317517 : Nat := 72461705321661976434343

theorem tailTrace_317517 : CollatzResearch.WordTrace tailWord_317517 prefixEnd_317517 72461705321661976434343 := by
  unfold tailWord_317517
  simp only [CollatzResearch.WordTrace]
  refine ⟨11580796390697611431430805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7720530927131740954287203 11580796390697611431430805)
  ·
    refine ⟨542849830813950535848319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 11580796390697611431430805 542849830813950535848319)
    ·
      refine ⟨814274746220925803772479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 542849830813950535848319 814274746220925803772479)
      ·
        refine ⟨1221412119331388705658719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 814274746220925803772479 1221412119331388705658719)
        ·
          refine ⟨1832118178997083058488079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1221412119331388705658719 1832118178997083058488079)
          ·
            refine ⟨2748177268495624587732119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1832118178997083058488079 2748177268495624587732119)
            ·
              refine ⟨4122265902743436881598179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2748177268495624587732119 4122265902743436881598179)
              ·
                refine ⟨6183398854115155322397269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4122265902743436881598179 6183398854115155322397269)
                ·
                  refine ⟨72461705321661976434343, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 6183398854115155322397269 72461705321661976434343)
                  ·
                    rfl

theorem cell21_317517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 1, 1, 8].length) (baseStart_317517 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_317517 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_317517 prefixEnd_317517 := by exact prefixLift 317517
  have htrace : WordTrace (prefixWord ++ tailWord_317517) baseStart_317517 baseEnd_317517 := by
    simpa [prefixWord, tailWord_317517, baseEnd_317517] using wordTrace_append hprefix tailTrace_317517
  have hstable : (prefixWord ++ tailWord_317517).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_317517).length < 2 ^ (prefixWord ++ tailWord_317517).sum := by decide
  have hdescent : baseEnd_317517 < baseStart_317517 := by decide
  rcases family_descends (prefixWord ++ tailWord_317517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_317644 : List Nat := [2, 2, 1, 6, 2, 1, 1, 2, 4]
def baseStart_317644 : Nat := 118140960795 + 317644 * 2 ^ 59
def prefixEnd_317644 : Nat := 4983230072969 + 3 ^ 40 * 317644 * 2
def baseEnd_317644 : Nat := 72490688451937977817417

theorem tailTrace_317644 : CollatzResearch.WordTrace tailWord_317644 prefixEnd_317644 72490688451937977817417 := by
  unfold tailWord_317644
  simp only [CollatzResearch.WordTrace]
  refine ⟨5792714230618756060651993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7723618974158341414202657 5792714230618756060651993)
  ·
    refine ⟨4344535672964067045488995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5792714230618756060651993 4344535672964067045488995)
    ·
      refine ⟨6516803509446100568233493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4344535672964067045488995 6516803509446100568233493)
      ·
        refine ⟨305475164505285964135945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 6516803509446100568233493 305475164505285964135945)
        ·
          refine ⟨229106373378964473101959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 305475164505285964135945 229106373378964473101959)
          ·
            refine ⟨343659560068446709652939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 229106373378964473101959 343659560068446709652939)
            ·
              refine ⟨515489340102670064479409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 343659560068446709652939 515489340102670064479409)
              ·
                refine ⟨386617005077002548359557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 515489340102670064479409 386617005077002548359557)
                ·
                  refine ⟨72490688451937977817417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 386617005077002548359557 72490688451937977817417)
                  ·
                    rfl

theorem cell21_317644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 2, 1, 1, 2, 4].length) (baseStart_317644 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_317644 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_317644 prefixEnd_317644 := by exact prefixLift 317644
  have htrace : WordTrace (prefixWord ++ tailWord_317644) baseStart_317644 baseEnd_317644 := by
    simpa [prefixWord, tailWord_317644, baseEnd_317644] using wordTrace_append hprefix tailTrace_317644
  have hstable : (prefixWord ++ tailWord_317644).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_317644).length < 2 ^ (prefixWord ++ tailWord_317644).sum := by decide
  have hdescent : baseEnd_317644 < baseStart_317644 := by decide
  rcases family_descends (prefixWord ++ tailWord_317644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_317700 : List Nat := [2, 3, 2, 2, 3, 2, 7]
def baseStart_317700 : Nat := 118140960795 + 317700 * 2 ^ 59
def prefixEnd_317700 : Nat := 4983230072969 + 3 ^ 40 * 317700 * 2
def baseEnd_317700 : Nat := 8055940934988258320441

theorem tailTrace_317700 : CollatzResearch.WordTrace tailWord_317700 prefixEnd_317700 8055940934988258320441 := by
  unfold tailWord_317700
  simp only [CollatzResearch.WordTrace]
  refine ⟨5793735474517316842671277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7724980632689755790228369 5793735474517316842671277)
  ·
    refine ⟨2172650802943993816001729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5793735474517316842671277 2172650802943993816001729)
    ·
      refine ⟨1629488102207995362001297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2172650802943993816001729 1629488102207995362001297)
      ·
        refine ⟨1222116076655996521500973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1629488102207995362001297 1222116076655996521500973)
        ·
          refine ⟨458293528745998695562865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1222116076655996521500973 458293528745998695562865)
          ·
            refine ⟨343720146559499021672149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 458293528745998695562865 343720146559499021672149)
            ·
              refine ⟨8055940934988258320441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 343720146559499021672149 8055940934988258320441)
              ·
                rfl

theorem cell21_317700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 2, 7].length) (baseStart_317700 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_317700 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_317700 prefixEnd_317700 := by exact prefixLift 317700
  have htrace : WordTrace (prefixWord ++ tailWord_317700) baseStart_317700 baseEnd_317700 := by
    simpa [prefixWord, tailWord_317700, baseEnd_317700] using wordTrace_append hprefix tailTrace_317700
  have hstable : (prefixWord ++ tailWord_317700).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_317700).length < 2 ^ (prefixWord ++ tailWord_317700).sum := by decide
  have hdescent : baseEnd_317700 < baseStart_317700 := by decide
  rcases family_descends (prefixWord ++ tailWord_317700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_317821 : List Nat := [1, 4, 1, 1, 2, 3, 3, 2, 4]
def baseStart_317821 : Nat := 118140960795 + 317821 * 2 ^ 59
def prefixEnd_317821 : Nat := 4983230072969 + 3 ^ 40 * 317821 * 2
def baseEnd_317821 : Nat := 72531082263425003367055

theorem tailTrace_317821 : CollatzResearch.WordTrace tailWord_317821 prefixEnd_317821 72531082263425003367055 := by
  unfold tailWord_317821
  simp only [CollatzResearch.WordTrace]
  refine ⟨11591884181596271350497317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7727922787730847566998211 11591884181596271350497317)
  ·
    refine ⟨2173478284049300878218247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11591884181596271350497317 2173478284049300878218247)
    ·
      refine ⟨3260217426073951317327371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2173478284049300878218247 3260217426073951317327371)
      ·
        refine ⟨4890326139110926975991057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3260217426073951317327371 4890326139110926975991057)
        ·
          refine ⟨3667744604333195231993293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4890326139110926975991057 3667744604333195231993293)
          ·
            refine ⟨1375404226624948211997485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3667744604333195231993293 1375404226624948211997485)
            ·
              refine ⟨515776584984355579499057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1375404226624948211997485 515776584984355579499057)
              ·
                refine ⟨386832438738266684624293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 515776584984355579499057 386832438738266684624293)
                ·
                  refine ⟨72531082263425003367055, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 386832438738266684624293 72531082263425003367055)
                  ·
                    rfl

theorem cell21_317821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 3, 2, 4].length) (baseStart_317821 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_317821 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_317821 prefixEnd_317821 := by exact prefixLift 317821
  have htrace : WordTrace (prefixWord ++ tailWord_317821) baseStart_317821 baseEnd_317821 := by
    simpa [prefixWord, tailWord_317821, baseEnd_317821] using wordTrace_append hprefix tailTrace_317821
  have hstable : (prefixWord ++ tailWord_317821).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_317821).length < 2 ^ (prefixWord ++ tailWord_317821).sum := by decide
  have hdescent : baseEnd_317821 < baseStart_317821 := by decide
  rcases family_descends (prefixWord ++ tailWord_317821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_317849 : List Nat := [1, 2, 1, 2, 1, 4, 1, 4, 5]
def baseStart_317849 : Nat := 118140960795 + 317849 * 2 ^ 59
def prefixEnd_317849 : Nat := 4983230072969 + 3 ^ 40 * 317849 * 2
def baseEnd_317849 : Nat := 72537472244903176900331

theorem tailTrace_317849 : CollatzResearch.WordTrace tailWord_317849 prefixEnd_317849 72537472244903176900331 := by
  unfold tailWord_317849
  simp only [CollatzResearch.WordTrace]
  refine ⟨11592905425494832132516601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7728603616996554755011067 11592905425494832132516601)
  ·
    refine ⟨8694679069121124099387451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11592905425494832132516601 8694679069121124099387451)
    ·
      refine ⟨13042018603681686149081177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8694679069121124099387451 13042018603681686149081177)
      ·
        refine ⟨9781513952761264611810883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13042018603681686149081177 9781513952761264611810883)
        ·
          refine ⟨14672270929141896917716325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9781513952761264611810883 14672270929141896917716325)
          ·
            refine ⟨2751050799214105672071811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14672270929141896917716325 2751050799214105672071811)
            ·
              refine ⟨4126576198821158508107717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2751050799214105672071811 4126576198821158508107717)
              ·
                refine ⟨773733037278967220270197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4126576198821158508107717 773733037278967220270197)
                ·
                  refine ⟨72537472244903176900331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 773733037278967220270197 72537472244903176900331)
                  ·
                    rfl

theorem cell21_317849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 1, 4, 5].length) (baseStart_317849 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_317849 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_317849 prefixEnd_317849 := by exact prefixLift 317849
  have htrace : WordTrace (prefixWord ++ tailWord_317849) baseStart_317849 baseEnd_317849 := by
    simpa [prefixWord, tailWord_317849, baseEnd_317849] using wordTrace_append hprefix tailTrace_317849
  have hstable : (prefixWord ++ tailWord_317849).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_317849).length < 2 ^ (prefixWord ++ tailWord_317849).sum := by decide
  have hdescent : baseEnd_317849 < baseStart_317849 := by decide
  rcases family_descends (prefixWord ++ tailWord_317849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_317869 : List Nat := [1, 5, 2, 2, 3, 1, 7]
def baseStart_317869 : Nat := 118140960795 + 317869 * 2 ^ 59
def prefixEnd_317869 : Nat := 4983230072969 + 3 ^ 40 * 317869 * 2
def baseEnd_317869 : Nat := 8060226279709731840773

theorem tailTrace_317869 : CollatzResearch.WordTrace tailWord_317869 prefixEnd_317869 8060226279709731840773 := by
  unfold tailWord_317869
  simp only [CollatzResearch.WordTrace]
  refine ⟨11593634885422375548244661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7729089923614917032163107 11593634885422375548244661)
  ·
    refine ⟨1086903270508347707647937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 11593634885422375548244661 1086903270508347707647937)
    ·
      refine ⟨815177452881260780735953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1086903270508347707647937 815177452881260780735953)
      ·
        refine ⟨611383089660945585551965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 815177452881260780735953 611383089660945585551965)
        ·
          refine ⟨229268658622854594581987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 611383089660945585551965 229268658622854594581987)
          ·
            refine ⟨343902987934281891872981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 229268658622854594581987 343902987934281891872981)
            ·
              refine ⟨8060226279709731840773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 343902987934281891872981 8060226279709731840773)
              ·
                rfl

theorem cell21_317869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 3, 1, 7].length) (baseStart_317869 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_317869 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_317869 prefixEnd_317869 := by exact prefixLift 317869
  have htrace : WordTrace (prefixWord ++ tailWord_317869) baseStart_317869 baseEnd_317869 := by
    simpa [prefixWord, tailWord_317869, baseEnd_317869] using wordTrace_append hprefix tailTrace_317869
  have hstable : (prefixWord ++ tailWord_317869).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_317869).length < 2 ^ (prefixWord ++ tailWord_317869).sum := by decide
  have hdescent : baseEnd_317869 < baseStart_317869 := by decide
  rcases family_descends (prefixWord ++ tailWord_317869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_317880 : List Nat := [2, 1, 2, 1, 2, 2, 1, 6, 4]
def baseStart_317880 : Nat := 118140960795 + 317880 * 2 ^ 59
def prefixEnd_317880 : Nat := 4983230072969 + 3 ^ 40 * 317880 * 2
def baseEnd_317880 : Nat := 72544546867254011883601

theorem tailTrace_317880 : CollatzResearch.WordTrace tailWord_317880 prefixEnd_317880 72544546867254011883601 := by
  unfold tailWord_317880
  simp only [CollatzResearch.WordTrace]
  refine ⟨5797018044191262213447547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7729357392255016284596729 5797018044191262213447547)
  ·
    refine ⟨8695527066286893320171321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5797018044191262213447547 8695527066286893320171321)
    ·
      refine ⟨6521645299715169990128491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8695527066286893320171321 6521645299715169990128491)
      ·
        refine ⟨9782467949572754985192737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6521645299715169990128491 9782467949572754985192737)
        ·
          refine ⟨7336850962179566238894553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9782467949572754985192737 7336850962179566238894553)
          ·
            refine ⟨5502638221634674679170915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7336850962179566238894553 5502638221634674679170915)
            ·
              refine ⟨8253957332452012018756373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5502638221634674679170915 8253957332452012018756373)
              ·
                refine ⟨386904249958688063379205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 8253957332452012018756373 386904249958688063379205)
                ·
                  refine ⟨72544546867254011883601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 386904249958688063379205 72544546867254011883601)
                  ·
                    rfl

theorem cell21_317880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 6, 4].length) (baseStart_317880 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_317880 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_317880 prefixEnd_317880 := by exact prefixLift 317880
  have htrace : WordTrace (prefixWord ++ tailWord_317880) baseStart_317880 baseEnd_317880 := by
    simpa [prefixWord, tailWord_317880, baseEnd_317880] using wordTrace_append hprefix tailTrace_317880
  have hstable : (prefixWord ++ tailWord_317880).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_317880).length < 2 ^ (prefixWord ++ tailWord_317880).sum := by decide
  have hdescent : baseEnd_317880 < baseStart_317880 := by decide
  rcases family_descends (prefixWord ++ tailWord_317880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_317889 : List Nat := [1, 2, 7, 1, 1, 2, 2, 1, 4]
def baseStart_317889 : Nat := 118140960795 + 317889 * 2 ^ 59
def prefixEnd_317889 : Nat := 4983230072969 + 3 ^ 40 * 317889 * 2
def baseEnd_317889 : Nat := 72546600789871996233583

theorem tailTrace_317889 : CollatzResearch.WordTrace tailWord_317889 prefixEnd_317889 72546600789871996233583 := by
  unfold tailWord_317889
  simp only [CollatzResearch.WordTrace]
  refine ⟨11594364345349918963972721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7729576230233279309315147 11594364345349918963972721)
  ·
    refine ⟨8695773259012439222979541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11594364345349918963972721 8695773259012439222979541)
    ·
      refine ⟨203807185758104044288583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 8695773259012439222979541 203807185758104044288583)
      ·
        refine ⟨305710778637156066432875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 203807185758104044288583 305710778637156066432875)
        ·
          refine ⟨458566167955734099649313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 305710778637156066432875 458566167955734099649313)
          ·
            refine ⟨343924625966800574736985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 458566167955734099649313 343924625966800574736985)
            ·
              refine ⟨257943469475100431052739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 343924625966800574736985 257943469475100431052739)
              ·
                refine ⟨386915204212650646579109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 257943469475100431052739 386915204212650646579109)
                ·
                  refine ⟨72546600789871996233583, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 386915204212650646579109 72546600789871996233583)
                  ·
                    rfl

theorem cell21_317889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 2, 2, 1, 4].length) (baseStart_317889 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_317889 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_317889 prefixEnd_317889 := by exact prefixLift 317889
  have htrace : WordTrace (prefixWord ++ tailWord_317889) baseStart_317889 baseEnd_317889 := by
    simpa [prefixWord, tailWord_317889, baseEnd_317889] using wordTrace_append hprefix tailTrace_317889
  have hstable : (prefixWord ++ tailWord_317889).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_317889).length < 2 ^ (prefixWord ++ tailWord_317889).sum := by decide
  have hdescent : baseEnd_317889 < baseStart_317889 := by decide
  rcases family_descends (prefixWord ++ tailWord_317889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_317897 : List Nat := [1, 2, 1, 1, 2, 1, 8, 1, 4]
def baseStart_317897 : Nat := 118140960795 + 317897 * 2 ^ 59
def prefixEnd_317897 : Nat := 4983230072969 + 3 ^ 40 * 317897 * 2
def baseEnd_317897 : Nat := 72548426498865760100233

theorem tailTrace_317897 : CollatzResearch.WordTrace tailWord_317897 prefixEnd_317897 72548426498865760100233 := by
  unfold tailWord_317897
  simp only [CollatzResearch.WordTrace]
  refine ⟨11594656129320936330263945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7729770752880624220175963 11594656129320936330263945)
  ·
    refine ⟨8695992096990702247697959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11594656129320936330263945 8695992096990702247697959)
    ·
      refine ⟨13043988145486053371546939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8695992096990702247697959 13043988145486053371546939)
      ·
        refine ⟨19565982218229080057320409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13043988145486053371546939 19565982218229080057320409)
        ·
          refine ⟨14674486663671810042990307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19565982218229080057320409 14674486663671810042990307)
          ·
            refine ⟨22011729995507715064485461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14674486663671810042990307 22011729995507715064485461)
            ·
              refine ⟨257949960884856035911939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 22011729995507715064485461 257949960884856035911939)
              ·
                refine ⟨386924941327284053867909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 257949960884856035911939 386924941327284053867909)
                ·
                  refine ⟨72548426498865760100233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 386924941327284053867909 72548426498865760100233)
                  ·
                    rfl

theorem cell21_317897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 8, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 8, 1, 4].length) (baseStart_317897 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_317897 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_317897 prefixEnd_317897 := by exact prefixLift 317897
  have htrace : WordTrace (prefixWord ++ tailWord_317897) baseStart_317897 baseEnd_317897 := by
    simpa [prefixWord, tailWord_317897, baseEnd_317897] using wordTrace_append hprefix tailTrace_317897
  have hstable : (prefixWord ++ tailWord_317897).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_317897).length < 2 ^ (prefixWord ++ tailWord_317897).sum := by decide
  have hdescent : baseEnd_317897 < baseStart_317897 := by decide
  rcases family_descends (prefixWord ++ tailWord_317897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_317942 : List Nat := [5, 1, 1, 1, 2, 1, 2, 3, 5]
def baseStart_317942 : Nat := 118140960795 + 317942 * 2 ^ 59
def prefixEnd_317942 : Nat := 4983230072969 + 3 ^ 40 * 317942 * 2
def baseEnd_317942 : Nat := 72558696111955681850141

theorem tailTrace_317942 : CollatzResearch.WordTrace tailWord_317942 prefixEnd_317942 72558696111955681850141 := by
  unfold tailWord_317942
  simp only [CollatzResearch.WordTrace]
  refine ⟨724768588384869313478255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 7730864942771939343768053 724768588384869313478255)
  ·
    refine ⟨1087152882577303970217383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 724768588384869313478255 1087152882577303970217383)
    ·
      refine ⟨1630729323865955955326075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1087152882577303970217383 1630729323865955955326075)
      ·
        refine ⟨2446093985798933932989113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1630729323865955955326075 2446093985798933932989113)
        ·
          refine ⟨1834570489349200449741835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2446093985798933932989113 1834570489349200449741835)
          ·
            refine ⟨2751855734023800674612753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1834570489349200449741835 2751855734023800674612753)
            ·
              refine ⟨2063891800517850505959565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2751855734023800674612753 2063891800517850505959565)
              ·
                refine ⟨773959425194193939734837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2063891800517850505959565 773959425194193939734837)
                ·
                  refine ⟨72558696111955681850141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 773959425194193939734837 72558696111955681850141)
                  ·
                    rfl

theorem cell21_317942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 2, 3, 5].length) (baseStart_317942 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_317942 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_317942 prefixEnd_317942 := by exact prefixLift 317942
  have htrace : WordTrace (prefixWord ++ tailWord_317942) baseStart_317942 baseEnd_317942 := by
    simpa [prefixWord, tailWord_317942, baseEnd_317942] using wordTrace_append hprefix tailTrace_317942
  have hstable : (prefixWord ++ tailWord_317942).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_317942).length < 2 ^ (prefixWord ++ tailWord_317942).sum := by decide
  have hdescent : baseEnd_317942 < baseStart_317942 := by decide
  rcases family_descends (prefixWord ++ tailWord_317942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_318001 : List Nat := [1, 2, 2, 3, 1, 1, 3, 3, 5]
def baseStart_318001 : Nat := 118140960795 + 318001 * 2 ^ 59
def prefixEnd_318001 : Nat := 4983230072969 + 3 ^ 40 * 318001 * 2
def baseEnd_318001 : Nat := 72572160715784690366687

theorem tailTrace_318001 : CollatzResearch.WordTrace tailWord_318001 prefixEnd_318001 72572160715784690366687 := by
  unfold tailWord_318001
  simp only [CollatzResearch.WordTrace]
  refine ⟨11598449320944162092049857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7732299547296108061366571 11598449320944162092049857)
  ·
    refine ⟨8698836990708121569037393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11598449320944162092049857 8698836990708121569037393)
    ·
      refine ⟨6524127743031091176778045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8698836990708121569037393 6524127743031091176778045)
      ·
        refine ⟨2446547903636659191291767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6524127743031091176778045 2446547903636659191291767)
        ·
          refine ⟨3669821855454988786937651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2446547903636659191291767 3669821855454988786937651)
          ·
            refine ⟨5504732783182483180406477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3669821855454988786937651 5504732783182483180406477)
            ·
              refine ⟨2064274793693431192652429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5504732783182483180406477 2064274793693431192652429)
              ·
                refine ⟨774103047635036697244661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2064274793693431192652429 774103047635036697244661)
                ·
                  refine ⟨72572160715784690366687, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 774103047635036697244661 72572160715784690366687)
                  ·
                    rfl

theorem cell21_318001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 3, 3, 5].length) (baseStart_318001 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_318001 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_318001 prefixEnd_318001 := by exact prefixLift 318001
  have htrace : WordTrace (prefixWord ++ tailWord_318001) baseStart_318001 baseEnd_318001 := by
    simpa [prefixWord, tailWord_318001, baseEnd_318001] using wordTrace_append hprefix tailTrace_318001
  have hstable : (prefixWord ++ tailWord_318001).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_318001).length < 2 ^ (prefixWord ++ tailWord_318001).sum := by decide
  have hdescent : baseEnd_318001 < baseStart_318001 := by decide
  rcases family_descends (prefixWord ++ tailWord_318001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_318091 : List Nat := [1, 1, 1, 1, 4, 1, 2, 4, 6]
def baseStart_318091 : Nat := 118140960795 + 318091 * 2 ^ 59
def prefixEnd_318091 : Nat := 4983230072969 + 3 ^ 40 * 318091 * 2
def baseEnd_318091 : Nat := 72592699941964533866503

theorem tailTrace_318091 : CollatzResearch.WordTrace tailWord_318091 prefixEnd_318091 72592699941964533866503 := by
  unfold tailWord_318091
  simp only [CollatzResearch.WordTrace]
  refine ⟨11601731890618107462826127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7734487927078738308550751 11601731890618107462826127)
  ·
    refine ⟨17402597835927161194239191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11601731890618107462826127 17402597835927161194239191)
    ·
      refine ⟨26103896753890741791358787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17402597835927161194239191 26103896753890741791358787)
      ·
        refine ⟨39155845130836112687038181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26103896753890741791358787 39155845130836112687038181)
        ·
          refine ⟨7341720962031771128819659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 39155845130836112687038181 7341720962031771128819659)
          ·
            refine ⟨11012581443047656693229489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7341720962031771128819659 11012581443047656693229489)
            ·
              refine ⟨8259436082285742519922117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11012581443047656693229489 8259436082285742519922117)
              ·
                refine ⟨1548644265428576722485397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8259436082285742519922117 1548644265428576722485397)
                ·
                  refine ⟨72592699941964533866503, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1548644265428576722485397 72592699941964533866503)
                  ·
                    rfl

theorem cell21_318091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 4, 6].length) (baseStart_318091 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_318091 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_318091 prefixEnd_318091 := by exact prefixLift 318091
  have htrace : WordTrace (prefixWord ++ tailWord_318091) baseStart_318091 baseEnd_318091 := by
    simpa [prefixWord, tailWord_318091, baseEnd_318091] using wordTrace_append hprefix tailTrace_318091
  have hstable : (prefixWord ++ tailWord_318091).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_318091).length < 2 ^ (prefixWord ++ tailWord_318091).sum := by decide
  have hdescent : baseEnd_318091 < baseStart_318091 := by decide
  rcases family_descends (prefixWord ++ tailWord_318091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_318125 : List Nat := [1, 5, 2, 1, 1, 2, 2, 3, 4]
def baseStart_318125 : Nat := 118140960795 + 318125 * 2 ^ 59
def prefixEnd_318125 : Nat := 4983230072969 + 3 ^ 40 * 318125 * 2
def baseEnd_318125 : Nat := 72600459205188030299767

theorem tailTrace_318125 : CollatzResearch.WordTrace tailWord_318125 prefixEnd_318125 72600459205188030299767 := by
  unfold tailWord_318125
  simp only [CollatzResearch.WordTrace]
  refine ⟨11602971972494931269563829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7735314648329954179709219 11602971972494931269563829)
  ·
    refine ⟨1087778622421399806521609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 11602971972494931269563829 1087778622421399806521609)
    ·
      refine ⟨815833966816049854891207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1087778622421399806521609 815833966816049854891207)
      ·
        refine ⟨1223750950224074782336811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 815833966816049854891207 1223750950224074782336811)
        ·
          refine ⟨1835626425336112173505217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1223750950224074782336811 1835626425336112173505217)
          ·
            refine ⟨1376719819002084130128913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1835626425336112173505217 1376719819002084130128913)
            ·
              refine ⟨1032539864251563097596685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1376719819002084130128913 1032539864251563097596685)
              ·
                refine ⟨387202449094336161598757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1032539864251563097596685 387202449094336161598757)
                ·
                  refine ⟨72600459205188030299767, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 387202449094336161598757 72600459205188030299767)
                  ·
                    rfl

theorem cell21_318125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 2, 3, 4].length) (baseStart_318125 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_318125 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_318125 prefixEnd_318125 := by exact prefixLift 318125
  have htrace : WordTrace (prefixWord ++ tailWord_318125) baseStart_318125 baseEnd_318125 := by
    simpa [prefixWord, tailWord_318125, baseEnd_318125] using wordTrace_append hprefix tailTrace_318125
  have hstable : (prefixWord ++ tailWord_318125).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_318125).length < 2 ^ (prefixWord ++ tailWord_318125).sum := by decide
  have hdescent : baseEnd_318125 < baseStart_318125 := by decide
  rcases family_descends (prefixWord ++ tailWord_318125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_318145 : List Nat := [1, 2, 6, 2, 1, 1, 2, 3, 3]
def baseStart_318145 : Nat := 118140960795 + 318145 * 2 ^ 59
def prefixEnd_318145 : Nat := 4983230072969 + 3 ^ 40 * 318145 * 2
def baseEnd_318145 : Nat := 72605023477672439966393

theorem tailTrace_318145 : CollatzResearch.WordTrace tailWord_318145 prefixEnd_318145 72605023477672439966393 := by
  unfold tailWord_318145
  simp only [CollatzResearch.WordTrace]
  refine ⟨11603701432422474685291889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7735800954948316456861259 11603701432422474685291889)
  ·
    refine ⟨8702776074316856013968917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11603701432422474685291889 8702776074316856013968917)
    ·
      refine ⟨407942628483602625654793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 8702776074316856013968917 407942628483602625654793)
      ·
        refine ⟨305956971362701969241095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 407942628483602625654793 305956971362701969241095)
        ·
          refine ⟨458935457044052953861643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 305956971362701969241095 458935457044052953861643)
          ·
            refine ⟨688403185566079430792465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 458935457044052953861643 688403185566079430792465)
            ·
              refine ⟨516302389174559573094349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 688403185566079430792465 516302389174559573094349)
              ·
                refine ⟨193613395940459839910381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 516302389174559573094349 193613395940459839910381)
                ·
                  refine ⟨72605023477672439966393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 193613395940459839910381 72605023477672439966393)
                  ·
                    rfl

theorem cell21_318145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 1, 2, 3, 3].length) (baseStart_318145 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_318145 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_318145 prefixEnd_318145 := by exact prefixLift 318145
  have htrace : WordTrace (prefixWord ++ tailWord_318145) baseStart_318145 baseEnd_318145 := by
    simpa [prefixWord, tailWord_318145, baseEnd_318145] using wordTrace_append hprefix tailTrace_318145
  have hstable : (prefixWord ++ tailWord_318145).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_318145).length < 2 ^ (prefixWord ++ tailWord_318145).sum := by decide
  have hdescent : baseEnd_318145 < baseStart_318145 := by decide
  rcases family_descends (prefixWord ++ tailWord_318145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_318170 : List Nat := [3, 1, 1, 2, 2, 2, 1, 6, 3]
def baseStart_318170 : Nat := 118140960795 + 318170 * 2 ^ 59
def prefixEnd_318170 : Nat := 4983230072969 + 3 ^ 40 * 318170 * 2
def baseEnd_318170 : Nat := 72610728818277952049675

theorem tailTrace_318170 : CollatzResearch.WordTrace tailWord_318170 prefixEnd_318170 72610728818277952049675 := by
  unfold tailWord_318170
  simp only [CollatzResearch.WordTrace]
  refine ⟨2901153314332975988737991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7736408838221269303301309 2901153314332975988737991)
  ·
    refine ⟨4351729971499463983106987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2901153314332975988737991 4351729971499463983106987)
    ·
      refine ⟨6527594957249195974660481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4351729971499463983106987 6527594957249195974660481)
      ·
        refine ⟨4895696217936896980995361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6527594957249195974660481 4895696217936896980995361)
        ·
          refine ⟨3671772163452672735746521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4895696217936896980995361 3671772163452672735746521)
          ·
            refine ⟨2753829122589504551809891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3671772163452672735746521 2753829122589504551809891)
            ·
              refine ⟨4130743683884256827714837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2753829122589504551809891 4130743683884256827714837)
              ·
                refine ⟨193628610182074538799133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 4130743683884256827714837 193628610182074538799133)
                ·
                  refine ⟨72610728818277952049675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 193628610182074538799133 72610728818277952049675)
                  ·
                    rfl

theorem cell21_318170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 1, 6, 3].length) (baseStart_318170 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_318170 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_318170 prefixEnd_318170 := by exact prefixLift 318170
  have htrace : WordTrace (prefixWord ++ tailWord_318170) baseStart_318170 baseEnd_318170 := by
    simpa [prefixWord, tailWord_318170, baseEnd_318170] using wordTrace_append hprefix tailTrace_318170
  have hstable : (prefixWord ++ tailWord_318170).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_318170).length < 2 ^ (prefixWord ++ tailWord_318170).sum := by decide
  have hdescent : baseEnd_318170 < baseStart_318170 := by decide
  rcases family_descends (prefixWord ++ tailWord_318170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_318215 : List Nat := [1, 1, 4, 4, 1, 3, 7]
def baseStart_318215 : Nat := 118140960795 + 318215 * 2 ^ 59
def prefixEnd_318215 : Nat := 4983230072969 + 3 ^ 40 * 318215 * 2
def baseEnd_318215 : Nat := 8068999825707541533287

theorem tailTrace_318215 : CollatzResearch.WordTrace tailWord_318215 prefixEnd_318215 8068999825707541533287 := by
  unfold tailWord_318215
  simp only [CollatzResearch.WordTrace]
  refine ⟨11606254542168876640340099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7737503028112584426893399 11606254542168876640340099)
  ·
    refine ⟨17409381813253314960510149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11606254542168876640340099 17409381813253314960510149)
    ·
      refine ⟨3264259089984996555095653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17409381813253314960510149 3264259089984996555095653)
      ·
        refine ⟨612048579372186854080435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3264259089984996555095653 612048579372186854080435)
        ·
          refine ⟨918072869058280281120653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 612048579372186854080435 918072869058280281120653)
          ·
            refine ⟨344277325896855105420245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 918072869058280281120653 344277325896855105420245)
            ·
              refine ⟨8068999825707541533287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 344277325896855105420245 8068999825707541533287)
              ·
                rfl

theorem cell21_318215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 3, 7].length) (baseStart_318215 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_318215 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_318215 prefixEnd_318215 := by exact prefixLift 318215
  have htrace : WordTrace (prefixWord ++ tailWord_318215) baseStart_318215 baseEnd_318215 := by
    simpa [prefixWord, tailWord_318215, baseEnd_318215] using wordTrace_append hprefix tailTrace_318215
  have hstable : (prefixWord ++ tailWord_318215).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_318215).length < 2 ^ (prefixWord ++ tailWord_318215).sum := by decide
  have hdescent : baseEnd_318215 < baseStart_318215 := by decide
  rcases family_descends (prefixWord ++ tailWord_318215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_318322 : List Nat := [3, 2, 1, 2, 1, 1, 3, 5, 3]
def baseStart_318322 : Nat := 118140960795 + 318322 * 2 ^ 59
def prefixEnd_318322 : Nat := 4983230072969 + 3 ^ 40 * 318322 * 2
def baseEnd_318322 : Nat := 72645417289159465516031

theorem tailTrace_318322 : CollatzResearch.WordTrace tailWord_318322 prefixEnd_318322 72645417289159465516031 := by
  unfold tailWord_318322
  simp only [CollatzResearch.WordTrace]
  refine ⟨2902539288195308478621305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7740104768520822609656813 2902539288195308478621305)
  ·
    refine ⟨2176904466146481358965979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2902539288195308478621305 2176904466146481358965979)
    ·
      refine ⟨3265356699219722038448969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2176904466146481358965979 3265356699219722038448969)
      ·
        refine ⟨2449017524414791528836727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3265356699219722038448969 2449017524414791528836727)
        ·
          refine ⟨3673526286622187293255091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2449017524414791528836727 3673526286622187293255091)
          ·
            refine ⟨5510289429933280939882637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3673526286622187293255091 5510289429933280939882637)
            ·
              refine ⟨2066358536224980352455989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5510289429933280939882637 2066358536224980352455989)
              ·
                refine ⟨193721112771091908042749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2066358536224980352455989 193721112771091908042749)
                ·
                  refine ⟨72645417289159465516031, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 193721112771091908042749 72645417289159465516031)
                  ·
                    rfl

theorem cell21_318322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 3, 5, 3].length) (baseStart_318322 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_318322 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_318322 prefixEnd_318322 := by exact prefixLift 318322
  have htrace : WordTrace (prefixWord ++ tailWord_318322) baseStart_318322 baseEnd_318322 := by
    simpa [prefixWord, tailWord_318322, baseEnd_318322] using wordTrace_append hprefix tailTrace_318322
  have hstable : (prefixWord ++ tailWord_318322).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_318322).length < 2 ^ (prefixWord ++ tailWord_318322).sum := by decide
  have hdescent : baseEnd_318322 < baseStart_318322 := by decide
  rcases family_descends (prefixWord ++ tailWord_318322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_318367 : List Nat := [1, 1, 2, 5, 2, 1, 4, 5]
def baseStart_318367 : Nat := 118140960795 + 318367 * 2 ^ 59
def prefixEnd_318367 : Nat := 4983230072969 + 3 ^ 40 * 318367 * 2
def baseEnd_318367 : Nat := 24218562300749795755313

theorem tailTrace_318367 : CollatzResearch.WordTrace tailWord_318367 prefixEnd_318367 24218562300749795755313 := by
  unfold tailWord_318367
  simp only [CollatzResearch.WordTrace]
  refine ⟨11611798437618206599873355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7741198958412137733248903 11611798437618206599873355)
  ·
    refine ⟨17417697656427309899810033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11611798437618206599873355 17417697656427309899810033)
    ·
      refine ⟨13063273242320482424857525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17417697656427309899810033 13063273242320482424857525)
      ·
        refine ⟨1224681866467545227330393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 13063273242320482424857525 1224681866467545227330393)
        ·
          refine ⟨918511399850658920497795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1224681866467545227330393 918511399850658920497795)
          ·
            refine ⟨1377767099775988380746693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 918511399850658920497795 1377767099775988380746693)
            ·
              refine ⟨258331331207997821390005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1377767099775988380746693 258331331207997821390005)
              ·
                refine ⟨24218562300749795755313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 258331331207997821390005 24218562300749795755313)
                ·
                  rfl

theorem cell21_318367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 4, 5].length) (baseStart_318367 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_318367 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_318367 prefixEnd_318367 := by exact prefixLift 318367
  have htrace : WordTrace (prefixWord ++ tailWord_318367) baseStart_318367 baseEnd_318367 := by
    simpa [prefixWord, tailWord_318367, baseEnd_318367] using wordTrace_append hprefix tailTrace_318367
  have hstable : (prefixWord ++ tailWord_318367).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_318367).length < 2 ^ (prefixWord ++ tailWord_318367).sum := by decide
  have hdescent : baseEnd_318367 < baseStart_318367 := by decide
  rcases family_descends (prefixWord ++ tailWord_318367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_318390 : List Nat := [5, 1, 4, 1, 2, 1, 1, 1, 5]
def baseStart_318390 : Nat := 118140960795 + 318390 * 2 ^ 59
def prefixEnd_318390 : Nat := 4983230072969 + 3 ^ 40 * 318390 * 2
def baseEnd_318390 : Nat := 72660935815606458382559

theorem tailTrace_318390 : CollatzResearch.WordTrace tailWord_318390 prefixEnd_318390 72660935815606458382559 := by
  unfold tailWord_318390
  simp only [CollatzResearch.WordTrace]
  refine ⟨725789832283430095497539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 7741758211023254351973749 725789832283430095497539)
  ·
    refine ⟨1088684748425145143246309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 725789832283430095497539 1088684748425145143246309)
    ·
      refine ⟨204128390329714714358683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1088684748425145143246309 204128390329714714358683)
      ·
        refine ⟨306192585494572071538025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 204128390329714714358683 306192585494572071538025)
        ·
          refine ⟨229644439120929053653519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 306192585494572071538025 229644439120929053653519)
          ·
            refine ⟨344466658681393580480279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 229644439120929053653519 344466658681393580480279)
            ·
              refine ⟨516699988022090370720419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 344466658681393580480279 516699988022090370720419)
              ·
                refine ⟨775049982033135556080629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 516699988022090370720419 775049982033135556080629)
                ·
                  refine ⟨72660935815606458382559, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 775049982033135556080629 72660935815606458382559)
                  ·
                    rfl

theorem cell21_318390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 2, 1, 1, 1, 5].length) (baseStart_318390 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_318390 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_318390 prefixEnd_318390 := by exact prefixLift 318390
  have htrace : WordTrace (prefixWord ++ tailWord_318390) baseStart_318390 baseEnd_318390 := by
    simpa [prefixWord, tailWord_318390, baseEnd_318390] using wordTrace_append hprefix tailTrace_318390
  have hstable : (prefixWord ++ tailWord_318390).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_318390).length < 2 ^ (prefixWord ++ tailWord_318390).sum := by decide
  have hdescent : baseEnd_318390 < baseStart_318390 := by decide
  rcases family_descends (prefixWord ++ tailWord_318390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_318404 : List Nat := [2, 3, 3, 3, 2, 1, 2, 1, 4]
def baseStart_318404 : Nat := 118140960795 + 318404 * 2 ^ 59
def prefixEnd_318404 : Nat := 4983230072969 + 3 ^ 40 * 318404 * 2
def baseEnd_318404 : Nat := 72664130806345545149197

theorem tailTrace_318404 : CollatzResearch.WordTrace tailWord_318404 prefixEnd_318404 72664130806345545149197 := by
  unfold tailWord_318404
  simp only [CollatzResearch.WordTrace]
  refine ⟨5806573969242080959485133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7742098625656107945980177 5806573969242080959485133)
  ·
    refine ⟨2177465238465780359806925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5806573969242080959485133 2177465238465780359806925)
    ·
      refine ⟨816549464424667634927597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2177465238465780359806925 816549464424667634927597)
      ·
        refine ⟨306206049159250363097849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 816549464424667634927597 306206049159250363097849)
        ·
          refine ⟨229654536869437772323387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 306206049159250363097849 229654536869437772323387)
          ·
            refine ⟨344481805304156658485081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 229654536869437772323387 344481805304156658485081)
            ·
              refine ⟨258361353978117493863811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 344481805304156658485081 258361353978117493863811)
              ·
                refine ⟨387542030967176240795717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 258361353978117493863811 387542030967176240795717)
                ·
                  refine ⟨72664130806345545149197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 387542030967176240795717 72664130806345545149197)
                  ·
                    rfl

theorem cell21_318404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 2, 1, 2, 1, 4].length) (baseStart_318404 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_318404 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_318404 prefixEnd_318404 := by exact prefixLift 318404
  have htrace : WordTrace (prefixWord ++ tailWord_318404) baseStart_318404 baseEnd_318404 := by
    simpa [prefixWord, tailWord_318404, baseEnd_318404] using wordTrace_append hprefix tailTrace_318404
  have hstable : (prefixWord ++ tailWord_318404).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_318404).length < 2 ^ (prefixWord ++ tailWord_318404).sum := by decide
  have hdescent : baseEnd_318404 < baseStart_318404 := by decide
  rcases family_descends (prefixWord ++ tailWord_318404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_318412 : List Nat := [2, 2, 1, 4, 1, 1, 3, 3, 4]
def baseStart_318412 : Nat := 118140960795 + 318412 * 2 ^ 59
def prefixEnd_318412 : Nat := 4983230072969 + 3 ^ 40 * 318412 * 2
def baseEnd_318412 : Nat := 72665956515339309015847

theorem tailTrace_318412 : CollatzResearch.WordTrace tailWord_318412 prefixEnd_318412 72665956515339309015847 := by
  unfold tailWord_318412
  simp only [CollatzResearch.WordTrace]
  refine ⟨5806719861227589642630745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7742293148303452856840993 5806719861227589642630745)
  ·
    refine ⟨4355039895920692231973059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5806719861227589642630745 4355039895920692231973059)
    ·
      refine ⟨6532559843881038347959589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4355039895920692231973059 6532559843881038347959589)
      ·
        refine ⟨1224854970727694690242423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6532559843881038347959589 1224854970727694690242423)
        ·
          refine ⟨1837282456091542035363635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1224854970727694690242423 1837282456091542035363635)
          ·
            refine ⟨2755923684137313053045453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1837282456091542035363635 2755923684137313053045453)
            ·
              refine ⟨1033471381551492394892045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2755923684137313053045453 1033471381551492394892045)
              ·
                refine ⟨387551768081809648084517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1033471381551492394892045 387551768081809648084517)
                ·
                  refine ⟨72665956515339309015847, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 387551768081809648084517 72665956515339309015847)
                  ·
                    rfl

theorem cell21_318412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 3, 3, 4].length) (baseStart_318412 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_318412 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_318412 prefixEnd_318412 := by exact prefixLift 318412
  have htrace : WordTrace (prefixWord ++ tailWord_318412) baseStart_318412 baseEnd_318412 := by
    simpa [prefixWord, tailWord_318412, baseEnd_318412] using wordTrace_append hprefix tailTrace_318412
  have hstable : (prefixWord ++ tailWord_318412).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_318412).length < 2 ^ (prefixWord ++ tailWord_318412).sum := by decide
  have hdescent : baseEnd_318412 < baseStart_318412 := by decide
  rcases family_descends (prefixWord ++ tailWord_318412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_318426 : List Nat := [3, 1, 1, 2, 4, 1, 2, 7]
def baseStart_318426 : Nat := 118140960795 + 318426 * 2 ^ 59
def prefixEnd_318426 : Nat := 4983230072969 + 3 ^ 40 * 318426 * 2
def baseEnd_318426 : Nat := 24223050502026131927495

theorem tailTrace_318426 : CollatzResearch.WordTrace tailWord_318426 prefixEnd_318426 24223050502026131927495 := by
  unfold tailWord_318426
  simp only [CollatzResearch.WordTrace]
  refine ⟨2903487586101114919067783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7742633562936306450847421 2903487586101114919067783)
  ·
    refine ⟨4355231379151672378601675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2903487586101114919067783 4355231379151672378601675)
    ·
      refine ⟨6532847068727508567902513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4355231379151672378601675 6532847068727508567902513)
      ·
        refine ⟨4899635301545631425926885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6532847068727508567902513 4899635301545631425926885)
        ·
          refine ⟨918681619039805892361291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4899635301545631425926885 918681619039805892361291)
          ·
            refine ⟨1378022428559708838541937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 918681619039805892361291 1378022428559708838541937)
            ·
              refine ⟨1033516821419781628906453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1378022428559708838541937 1033516821419781628906453)
              ·
                refine ⟨24223050502026131927495, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1033516821419781628906453 24223050502026131927495)
                ·
                  rfl

theorem cell21_318426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 2, 7].length) (baseStart_318426 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_318426 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_318426 prefixEnd_318426 := by exact prefixLift 318426
  have htrace : WordTrace (prefixWord ++ tailWord_318426) baseStart_318426 baseEnd_318426 := by
    simpa [prefixWord, tailWord_318426, baseEnd_318426] using wordTrace_append hprefix tailTrace_318426
  have hstable : (prefixWord ++ tailWord_318426).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_318426).length < 2 ^ (prefixWord ++ tailWord_318426).sum := by decide
  have hdescent : baseEnd_318426 < baseStart_318426 := by decide
  rcases family_descends (prefixWord ++ tailWord_318426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_318561 : List Nat := [1, 2, 3, 1, 1, 2, 11]
def baseStart_318561 : Nat := 118140960795 + 318561 * 2 ^ 59
def prefixEnd_318561 : Nat := 4983230072969 + 3 ^ 40 * 318561 * 2
def baseEnd_318561 : Nat := 8077773371705351225801

theorem tailTrace_318561 : CollatzResearch.WordTrace tailWord_318561 prefixEnd_318561 8077773371705351225801 := by
  unfold tailWord_318561
  simp only [CollatzResearch.WordTrace]
  refine ⟨11618874198915377732435537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7745916132610251821623691 11618874198915377732435537)
  ·
    refine ⟨8714155649186533299326653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11618874198915377732435537 8714155649186533299326653)
    ·
      refine ⟨3267808368444949987247495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8714155649186533299326653 3267808368444949987247495)
      ·
        refine ⟨4901712552667424980871243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3267808368444949987247495 4901712552667424980871243)
        ·
          refine ⟨7352568829001137471306865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4901712552667424980871243 7352568829001137471306865)
          ·
            refine ⟨5514426621750853103480149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7352568829001137471306865 5514426621750853103480149)
            ·
              refine ⟨8077773371705351225801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 5514426621750853103480149 8077773371705351225801)
              ·
                rfl

theorem cell21_318561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 11].length) (baseStart_318561 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_318561 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_318561 prefixEnd_318561 := by exact prefixLift 318561
  have htrace : WordTrace (prefixWord ++ tailWord_318561) baseStart_318561 baseEnd_318561 := by
    simpa [prefixWord, tailWord_318561, baseEnd_318561] using wordTrace_append hprefix tailTrace_318561
  have hstable : (prefixWord ++ tailWord_318561).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_318561).length < 2 ^ (prefixWord ++ tailWord_318561).sum := by decide
  have hdescent : baseEnd_318561 < baseStart_318561 := by decide
  rcases family_descends (prefixWord ++ tailWord_318561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_318567 : List Nat := [1, 1, 5, 1, 1, 4, 3, 2, 3]
def baseStart_318567 : Nat := 118140960795 + 318567 * 2 ^ 59
def prefixEnd_318567 : Nat := 4983230072969 + 3 ^ 40 * 318567 * 2
def baseEnd_318567 : Nat := 72701329627093483932197

theorem tailTrace_318567 : CollatzResearch.WordTrace tailWord_318567 prefixEnd_318567 72701329627093483932197 := by
  unfold tailWord_318567
  simp only [CollatzResearch.WordTrace]
  refine ⟨11619093036893640757153955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7746062024595760504769303 11619093036893640757153955)
  ·
    refine ⟨17428639555340461135730933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11619093036893640757153955 17428639555340461135730933)
    ·
      refine ⟨1633934958313168231474775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 17428639555340461135730933 1633934958313168231474775)
      ·
        refine ⟨2450902437469752347212163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1633934958313168231474775 2450902437469752347212163)
        ·
          refine ⟨3676353656204628520818245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2450902437469752347212163 3676353656204628520818245)
          ·
            refine ⟨689316310538367847653421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3676353656204628520818245 689316310538367847653421)
            ·
              refine ⟨258493616451887942870033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 689316310538367847653421 258493616451887942870033)
              ·
                refine ⟨193870212338915957152525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 258493616451887942870033 193870212338915957152525)
                ·
                  refine ⟨72701329627093483932197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 193870212338915957152525 72701329627093483932197)
                  ·
                    rfl

theorem cell21_318567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 4, 3, 2, 3].length) (baseStart_318567 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_318567 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_318567 prefixEnd_318567 := by exact prefixLift 318567
  have htrace : WordTrace (prefixWord ++ tailWord_318567) baseStart_318567 baseEnd_318567 := by
    simpa [prefixWord, tailWord_318567, baseEnd_318567] using wordTrace_append hprefix tailTrace_318567
  have hstable : (prefixWord ++ tailWord_318567).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_318567).length < 2 ^ (prefixWord ++ tailWord_318567).sum := by decide
  have hdescent : baseEnd_318567 < baseStart_318567 := by decide
  rcases family_descends (prefixWord ++ tailWord_318567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_318578 : List Nat := [3, 2, 1, 2, 2, 1, 4, 6]
def baseStart_318578 : Nat := 118140960795 + 318578 * 2 ^ 59
def prefixEnd_318578 : Nat := 4983230072969 + 3 ^ 40 * 318578 * 2
def baseEnd_318578 : Nat := 24234613325653303082947

theorem tailTrace_318578 : CollatzResearch.WordTrace tailWord_318578 prefixEnd_318578 24234613325653303082947 := by
  unfold tailWord_318578
  simp only [CollatzResearch.WordTrace]
  refine ⟨2904873559963447408951097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7746329493235859757202925 2904873559963447408951097)
  ·
    refine ⟨2178655169972585556713323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2904873559963447408951097 2178655169972585556713323)
    ·
      refine ⟨3267982754958878335069985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2178655169972585556713323 3267982754958878335069985)
      ·
        refine ⟨2450987066219158751302489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3267982754958878335069985 2450987066219158751302489)
        ·
          refine ⟨1838240299664369063476867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2450987066219158751302489 1838240299664369063476867)
          ·
            refine ⟨2757360449496553595215301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1838240299664369063476867 2757360449496553595215301)
            ·
              refine ⟨517005084280603799102869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2757360449496553595215301 517005084280603799102869)
              ·
                refine ⟨24234613325653303082947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 517005084280603799102869 24234613325653303082947)
                ·
                  rfl

theorem cell21_318578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 4, 6].length) (baseStart_318578 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_318578 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_318578 prefixEnd_318578 := by exact prefixLift 318578
  have htrace : WordTrace (prefixWord ++ tailWord_318578) baseStart_318578 baseEnd_318578 := by
    simpa [prefixWord, tailWord_318578, baseEnd_318578] using wordTrace_append hprefix tailTrace_318578
  have hstable : (prefixWord ++ tailWord_318578).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_318578).length < 2 ^ (prefixWord ++ tailWord_318578).sum := by decide
  have hdescent : baseEnd_318578 < baseStart_318578 := by decide
  rcases family_descends (prefixWord ++ tailWord_318578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_318592 : List Nat := [2, 1, 1, 2, 1, 3, 2, 4, 5]
def baseStart_318592 : Nat := 118140960795 + 318592 * 2 ^ 59
def prefixEnd_318592 : Nat := 4983230072969 + 3 ^ 40 * 318592 * 2
def baseEnd_318592 : Nat := 72707034967698996015479

theorem tailTrace_318592 : CollatzResearch.WordTrace tailWord_318592 prefixEnd_318592 72707034967698996015479 := by
  unfold tailWord_318592
  simp only [CollatzResearch.WordTrace]
  refine ⟨5810002430901535013407015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7746669907868713351209353 5810002430901535013407015)
  ·
    refine ⟨8715003646352302520110523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5810002430901535013407015 8715003646352302520110523)
    ·
      refine ⟨13072505469528453780165785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8715003646352302520110523 13072505469528453780165785)
      ·
        refine ⟨9804379102146340335124339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13072505469528453780165785 9804379102146340335124339)
        ·
          refine ⟨14706568653219510502686509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9804379102146340335124339 14706568653219510502686509)
          ·
            refine ⟨5514963244957316438507441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14706568653219510502686509 5514963244957316438507441)
            ·
              refine ⟨4136222433717987328880581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5514963244957316438507441 4136222433717987328880581)
              ·
                refine ⟨775541706322122624165109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4136222433717987328880581 775541706322122624165109)
                ·
                  refine ⟨72707034967698996015479, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 775541706322122624165109 72707034967698996015479)
                  ·
                    rfl

theorem cell21_318592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 2, 4, 5].length) (baseStart_318592 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_318592 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_318592 prefixEnd_318592 := by exact prefixLift 318592
  have htrace : WordTrace (prefixWord ++ tailWord_318592) baseStart_318592 baseEnd_318592 := by
    simpa [prefixWord, tailWord_318592, baseEnd_318592] using wordTrace_append hprefix tailTrace_318592
  have hstable : (prefixWord ++ tailWord_318592).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_318592).length < 2 ^ (prefixWord ++ tailWord_318592).sum := by decide
  have hdescent : baseEnd_318592 < baseStart_318592 := by decide
  rcases family_descends (prefixWord ++ tailWord_318592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_318713 : List Nat := [1, 2, 1, 3, 1, 1, 5, 7]
def baseStart_318713 : Nat := 118140960795 + 318713 * 2 ^ 59
def prefixEnd_318713 : Nat := 4983230072969 + 3 ^ 40 * 318713 * 2
def baseEnd_318713 : Nat := 24244882938743224832855

theorem tailTrace_318713 : CollatzResearch.WordTrace tailWord_318713 prefixEnd_318713 24244882938743224832855 := by
  unfold tailWord_318713
  simp only [CollatzResearch.WordTrace]
  refine ⟨11624418094364707691968793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7749612062909805127979195 11624418094364707691968793)
  ·
    refine ⟨8718313570773530768976595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11624418094364707691968793 8718313570773530768976595)
    ·
      refine ⟨13077470356160296153464893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8718313570773530768976595 13077470356160296153464893)
      ·
        refine ⟨4904051383560111057549335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13077470356160296153464893 4904051383560111057549335)
        ·
          refine ⟨7356077075340166586324003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4904051383560111057549335 7356077075340166586324003)
          ·
            refine ⟨11034115613010249879486005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7356077075340166586324003 11034115613010249879486005)
            ·
              refine ⟨1034448338719710926201813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 11034115613010249879486005 1034448338719710926201813)
              ·
                refine ⟨24244882938743224832855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1034448338719710926201813 24244882938743224832855)
                ·
                  rfl

theorem cell21_318713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 5, 7].length) (baseStart_318713 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_318713 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_318713 prefixEnd_318713 := by exact prefixLift 318713
  have htrace : WordTrace (prefixWord ++ tailWord_318713) baseStart_318713 baseEnd_318713 := by
    simpa [prefixWord, tailWord_318713, baseEnd_318713] using wordTrace_append hprefix tailTrace_318713
  have hstable : (prefixWord ++ tailWord_318713).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_318713).length < 2 ^ (prefixWord ++ tailWord_318713).sum := by decide
  have hdescent : baseEnd_318713 < baseStart_318713 := by decide
  rcases family_descends (prefixWord ++ tailWord_318713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_318750 : List Nat := [4, 3, 2, 1, 2, 1, 1, 3, 4]
def baseStart_318750 : Nat := 118140960795 + 318750 * 2 ^ 59
def prefixEnd_318750 : Nat := 4983230072969 + 3 ^ 40 * 318750 * 2
def baseEnd_318750 : Nat := 72743092720325832381823

theorem tailTrace_318750 : CollatzResearch.WordTrace tailWord_318750 prefixEnd_318750 72743092720325832381823 := by
  unfold tailWord_318750
  simp only [CollatzResearch.WordTrace]
  refine ⟨1453220949403832876383213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7750511730153775340710469 1453220949403832876383213)
  ·
    refine ⟨544957856026437328643705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1453220949403832876383213 544957856026437328643705)
    ·
      refine ⟨408718392019827996482779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 544957856026437328643705 408718392019827996482779)
      ·
        refine ⟨613077588029741994724169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 408718392019827996482779 613077588029741994724169)
        ·
          refine ⟨459808191022306496043127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 613077588029741994724169 459808191022306496043127)
          ·
            refine ⟨689712286533459744064691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 459808191022306496043127 689712286533459744064691)
            ·
              refine ⟨1034568429800189616097037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 689712286533459744064691 1034568429800189616097037)
              ·
                refine ⟨387963161175071106036389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1034568429800189616097037 387963161175071106036389)
                ·
                  refine ⟨72743092720325832381823, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 387963161175071106036389 72743092720325832381823)
                  ·
                    rfl

theorem cell21_318750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 1, 1, 3, 4].length) (baseStart_318750 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_318750 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_318750 prefixEnd_318750 := by exact prefixLift 318750
  have htrace : WordTrace (prefixWord ++ tailWord_318750) baseStart_318750 baseEnd_318750 := by
    simpa [prefixWord, tailWord_318750, baseEnd_318750] using wordTrace_append hprefix tailTrace_318750
  have hstable : (prefixWord ++ tailWord_318750).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_318750).length < 2 ^ (prefixWord ++ tailWord_318750).sum := by decide
  have hdescent : baseEnd_318750 < baseStart_318750 := by decide
  rcases family_descends (prefixWord ++ tailWord_318750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_318820 : List Nat := [2, 3, 1, 1, 3, 2, 1, 1, 7]
def baseStart_318820 : Nat := 118140960795 + 318820 * 2 ^ 59
def prefixEnd_318820 : Nat := 4983230072969 + 3 ^ 40 * 318820 * 2
def baseEnd_318820 : Nat := 72759067674021266215013

theorem tailTrace_318820 : CollatzResearch.WordTrace tailWord_318820 prefixEnd_318820 72759067674021266215013 := by
  unfold tailWord_318820
  simp only [CollatzResearch.WordTrace]
  refine ⟨5814160352488532483056957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7752213803318043310742609 5814160352488532483056957)
  ·
    refine ⟨2180310132183199681146359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5814160352488532483056957 2180310132183199681146359)
    ·
      refine ⟨3270465198274799521719539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2180310132183199681146359 3270465198274799521719539)
      ·
        refine ⟨4905697797412199282579309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3270465198274799521719539 4905697797412199282579309)
        ·
          refine ⟨1839636674029574730967241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4905697797412199282579309 1839636674029574730967241)
          ·
            refine ⟨1379727505522181048225431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1839636674029574730967241 1379727505522181048225431)
            ·
              refine ⟨2069591258283271572338147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1379727505522181048225431 2069591258283271572338147)
              ·
                refine ⟨3104386887424907358507221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2069591258283271572338147 3104386887424907358507221)
                ·
                  refine ⟨72759067674021266215013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3104386887424907358507221 72759067674021266215013)
                  ·
                    rfl

theorem cell21_318820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 1, 1, 7].length) (baseStart_318820 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_318820 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_318820 prefixEnd_318820 := by exact prefixLift 318820
  have htrace : WordTrace (prefixWord ++ tailWord_318820) baseStart_318820 baseEnd_318820 := by
    simpa [prefixWord, tailWord_318820, baseEnd_318820] using wordTrace_append hprefix tailTrace_318820
  have hstable : (prefixWord ++ tailWord_318820).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_318820).length < 2 ^ (prefixWord ++ tailWord_318820).sum := by decide
  have hdescent : baseEnd_318820 < baseStart_318820 := by decide
  rcases family_descends (prefixWord ++ tailWord_318820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_318823 : List Nat := [1, 1, 5, 1, 4, 1, 3, 5]
def baseStart_318823 : Nat := 118140960795 + 318823 * 2 ^ 59
def prefixEnd_318823 : Nat := 4983230072969 + 3 ^ 40 * 318823 * 2
def baseEnd_318823 : Nat := 24253250771631309221669

theorem tailTrace_318823 : CollatzResearch.WordTrace tailWord_318823 prefixEnd_318823 24253250771631309221669 := by
  unfold tailWord_318823
  simp only [CollatzResearch.WordTrace]
  refine ⟨11628430123966196478473123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7752286749310797652315415 11628430123966196478473123)
  ·
    refine ⟨17442645185949294717709685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11628430123966196478473123 17442645185949294717709685)
    ·
      refine ⟨1635247986182746379785283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 17442645185949294717709685 1635247986182746379785283)
      ·
        refine ⟨2452871979274119569677925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1635247986182746379785283 2452871979274119569677925)
        ·
          refine ⟨459913496113897419314611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2452871979274119569677925 459913496113897419314611)
          ·
            refine ⟨689870244170846128971917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 459913496113897419314611 689870244170846128971917)
            ·
              refine ⟨258701341564067298364469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 689870244170846128971917 258701341564067298364469)
              ·
                refine ⟨24253250771631309221669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 258701341564067298364469 24253250771631309221669)
                ·
                  rfl

theorem cell21_318823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 1, 3, 5].length) (baseStart_318823 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_318823 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_318823 prefixEnd_318823 := by exact prefixLift 318823
  have htrace : WordTrace (prefixWord ++ tailWord_318823) baseStart_318823 baseEnd_318823 := by
    simpa [prefixWord, tailWord_318823, baseEnd_318823] using wordTrace_append hprefix tailTrace_318823
  have hstable : (prefixWord ++ tailWord_318823).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_318823).length < 2 ^ (prefixWord ++ tailWord_318823).sum := by decide
  have hdescent : baseEnd_318823 < baseStart_318823 := by decide
  rcases family_descends (prefixWord ++ tailWord_318823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_318851 : List Nat := [1, 1, 1, 3, 5, 2, 1, 1, 6]
def baseStart_318851 : Nat := 118140960795 + 318851 * 2 ^ 59
def prefixEnd_318851 : Nat := 4983230072969 + 3 ^ 40 * 318851 * 2
def baseEnd_318851 : Nat := 72766142296372101198283

theorem tailTrace_318851 : CollatzResearch.WordTrace tailWord_318851 prefixEnd_318851 72766142296372101198283 := by
  unfold tailWord_318851
  simp only [CollatzResearch.WordTrace]
  refine ⟨11629451367864757260492407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7752967578576504840328271 11629451367864757260492407)
  ·
    refine ⟨17444177051797135890738611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11629451367864757260492407 17444177051797135890738611)
    ·
      refine ⟨26166265577695703836107917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17444177051797135890738611 26166265577695703836107917)
      ·
        refine ⟨9812349591635888938540469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26166265577695703836107917 9812349591635888938540469)
        ·
          refine ⟨919907774215864587988169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 9812349591635888938540469 919907774215864587988169)
          ·
            refine ⟨689930830661898440991127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 919907774215864587988169 689930830661898440991127)
            ·
              refine ⟨1034896245992847661486691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 689930830661898440991127 1034896245992847661486691)
              ·
                refine ⟨1552344368989271492230037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1034896245992847661486691 1552344368989271492230037)
                ·
                  refine ⟨72766142296372101198283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1552344368989271492230037 72766142296372101198283)
                  ·
                    rfl

theorem cell21_318851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 2, 1, 1, 6].length) (baseStart_318851 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_318851 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_318851 prefixEnd_318851 := by exact prefixLift 318851
  have htrace : WordTrace (prefixWord ++ tailWord_318851) baseStart_318851 baseEnd_318851 := by
    simpa [prefixWord, tailWord_318851, baseEnd_318851] using wordTrace_append hprefix tailTrace_318851
  have hstable : (prefixWord ++ tailWord_318851).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_318851).length < 2 ^ (prefixWord ++ tailWord_318851).sum := by decide
  have hdescent : baseEnd_318851 < baseStart_318851 := by decide
  rcases family_descends (prefixWord ++ tailWord_318851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_318882 : List Nat := [3, 3, 1, 2, 1, 3, 1, 7]
def baseStart_318882 : Nat := 118140960795 + 318882 * 2 ^ 59
def prefixEnd_318882 : Nat := 4983230072969 + 3 ^ 40 * 318882 * 2
def baseEnd_318882 : Nat := 24257738972907645393851

theorem tailTrace_318882 : CollatzResearch.WordTrace tailWord_318882 prefixEnd_318882 24257738972907645393851 := by
  unfold tailWord_318882
  simp only [CollatzResearch.WordTrace]
  refine ⟨2907645507688112388717725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7753721353834966369913933 2907645507688112388717725)
  ·
    refine ⟨1090367065383042145769147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2907645507688112388717725 1090367065383042145769147)
    ·
      refine ⟨1635550598074563218653721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1090367065383042145769147 1635550598074563218653721)
      ·
        refine ⟨1226662948555922413990291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1635550598074563218653721 1226662948555922413990291)
        ·
          refine ⟨1839994422833883620985437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1226662948555922413990291 1839994422833883620985437)
          ·
            refine ⟨689997908562706357869539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1839994422833883620985437 689997908562706357869539)
            ·
              refine ⟨1034996862844059536804309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 689997908562706357869539 1034996862844059536804309)
              ·
                refine ⟨24257738972907645393851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1034996862844059536804309 24257738972907645393851)
                ·
                  rfl

theorem cell21_318882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 3, 1, 7].length) (baseStart_318882 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_318882 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_318882 prefixEnd_318882 := by exact prefixLift 318882
  have htrace : WordTrace (prefixWord ++ tailWord_318882) baseStart_318882 baseEnd_318882 := by
    simpa [prefixWord, tailWord_318882, baseEnd_318882] using wordTrace_append hprefix tailTrace_318882
  have hstable : (prefixWord ++ tailWord_318882).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_318882).length < 2 ^ (prefixWord ++ tailWord_318882).sum := by decide
  have hdescent : baseEnd_318882 < baseStart_318882 := by decide
  rcases family_descends (prefixWord ++ tailWord_318882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_318888 : List Nat := [2, 1, 6, 1, 2, 2, 1, 3, 3]
def baseStart_318888 : Nat := 118140960795 + 318888 * 2 ^ 59
def prefixEnd_318888 : Nat := 4983230072969 + 3 ^ 40 * 318888 * 2
def baseEnd_318888 : Nat := 72774586200468259081541

theorem tailTrace_318888 : CollatzResearch.WordTrace tailWord_318888 prefixEnd_318888 72774586200468259081541 := by
  unfold tailWord_318888
  simp only [CollatzResearch.WordTrace]
  refine ⟨5815400434365356289794659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7753867245820475053059545 5815400434365356289794659)
  ·
    refine ⟨8723100651548034434691989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5815400434365356289794659 8723100651548034434691989)
    ·
      refine ⟨408895343041314114126187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 8723100651548034434691989 408895343041314114126187)
      ·
        refine ⟨613343014561971171189281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 408895343041314114126187 613343014561971171189281)
        ·
          refine ⟨460007260921478378391961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 613343014561971171189281 460007260921478378391961)
          ·
            refine ⟨345005445691108783793971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 460007260921478378391961 345005445691108783793971)
            ·
              refine ⟨517508168536663175690957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 345005445691108783793971 517508168536663175690957)
              ·
                refine ⟨194065563201248690884109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 517508168536663175690957 194065563201248690884109)
                ·
                  refine ⟨72774586200468259081541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 194065563201248690884109 72774586200468259081541)
                  ·
                    rfl

theorem cell21_318888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 2, 1, 3, 3].length) (baseStart_318888 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_318888 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_318888 prefixEnd_318888 := by exact prefixLift 318888
  have htrace : WordTrace (prefixWord ++ tailWord_318888) baseStart_318888 baseEnd_318888 := by
    simpa [prefixWord, tailWord_318888, baseEnd_318888] using wordTrace_append hprefix tailTrace_318888
  have hstable : (prefixWord ++ tailWord_318888).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_318888).length < 2 ^ (prefixWord ++ tailWord_318888).sum := by decide
  have hdescent : baseEnd_318888 < baseStart_318888 := by decide
  rcases family_descends (prefixWord ++ tailWord_318888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_318955 : List Nat := [1, 1, 1, 1, 2, 3, 2, 1, 9]
def baseStart_318955 : Nat := 118140960795 + 318955 * 2 ^ 59
def prefixEnd_318955 : Nat := 4983230072969 + 3 ^ 40 * 318955 * 2
def baseEnd_318955 : Nat := 72789876513291031464737

theorem tailTrace_318955 : CollatzResearch.WordTrace tailWord_318955 prefixEnd_318955 72789876513291031464737 := by
  unfold tailWord_318955
  simp only [CollatzResearch.WordTrace]
  refine ⟨11633244559487983022278319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7755496372991988681518879 11633244559487983022278319)
  ·
    refine ⟨17449866839231974533417479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11633244559487983022278319 17449866839231974533417479)
    ·
      refine ⟨26174800258847961800126219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17449866839231974533417479 26174800258847961800126219)
      ·
        refine ⟨39262200388271942700189329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26174800258847961800126219 39262200388271942700189329)
        ·
          refine ⟨29446650291203957025141997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39262200388271942700189329 29446650291203957025141997)
          ·
            refine ⟨11042493859201483884428249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29446650291203957025141997 11042493859201483884428249)
            ·
              refine ⟨8281870394401112913321187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11042493859201483884428249 8281870394401112913321187)
              ·
                refine ⟨12422805591601669369981781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8281870394401112913321187 12422805591601669369981781)
                ·
                  refine ⟨72789876513291031464737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 12422805591601669369981781 72789876513291031464737)
                  ·
                    rfl

theorem cell21_318955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 1, 9].length) (baseStart_318955 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_318955 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_318955 prefixEnd_318955 := by exact prefixLift 318955
  have htrace : WordTrace (prefixWord ++ tailWord_318955) baseStart_318955 baseEnd_318955 := by
    simpa [prefixWord, tailWord_318955, baseEnd_318955] using wordTrace_append hprefix tailTrace_318955
  have hstable : (prefixWord ++ tailWord_318955).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_318955).length < 2 ^ (prefixWord ++ tailWord_318955).sum := by decide
  have hdescent : baseEnd_318955 < baseStart_318955 := by decide
  rcases family_descends (prefixWord ++ tailWord_318955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_319037 : List Nat := [1, 4, 1, 3, 3, 1, 3, 1, 4]
def baseStart_319037 : Nat := 118140960795 + 319037 * 2 ^ 59
def prefixEnd_319037 : Nat := 4983230072969 + 3 ^ 40 * 319037 * 2
def baseEnd_319037 : Nat := 72808590030477111097903

theorem tailTrace_319037 : CollatzResearch.WordTrace tailWord_319037 prefixEnd_319037 72808590030477111097903 := by
  unfold tailWord_319037
  simp only [CollatzResearch.WordTrace]
  refine ⟨11636235345190911026763365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7757490230127274017842243 11636235345190911026763365)
  ·
    refine ⟨2181794127223295817518131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11636235345190911026763365 2181794127223295817518131)
    ·
      refine ⟨3272691190834943726277197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2181794127223295817518131 3272691190834943726277197)
      ·
        refine ⟨1227259196563103897353949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3272691190834943726277197 1227259196563103897353949)
        ·
          refine ⟨460222198711163961507731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1227259196563103897353949 460222198711163961507731)
          ·
            refine ⟨690333298066745942261597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 460222198711163961507731 690333298066745942261597)
            ·
              refine ⟨258874986775029728348099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 690333298066745942261597 258874986775029728348099)
              ·
                refine ⟨388312480162544592522149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 258874986775029728348099 388312480162544592522149)
                ·
                  refine ⟨72808590030477111097903, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 388312480162544592522149 72808590030477111097903)
                  ·
                    rfl

theorem cell21_319037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 1, 3, 1, 4].length) (baseStart_319037 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_319037 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_319037 prefixEnd_319037 := by exact prefixLift 319037
  have htrace : WordTrace (prefixWord ++ tailWord_319037) baseStart_319037 baseEnd_319037 := by
    simpa [prefixWord, tailWord_319037, baseEnd_319037] using wordTrace_append hprefix tailTrace_319037
  have hstable : (prefixWord ++ tailWord_319037).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_319037).length < 2 ^ (prefixWord ++ tailWord_319037).sum := by decide
  have hdescent : baseEnd_319037 < baseStart_319037 := by decide
  rcases family_descends (prefixWord ++ tailWord_319037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_319107 : List Nat := [1, 1, 1, 3, 3, 1, 1, 3, 7]
def baseStart_319107 : Nat := 118140960795 + 319107 * 2 ^ 59
def prefixEnd_319107 : Nat := 4983230072969 + 3 ^ 40 * 319107 * 2
def baseEnd_319107 : Nat := 72824564984172544931093

theorem tailTrace_319107 : CollatzResearch.WordTrace tailWord_319107 prefixEnd_319107 72824564984172544931093 := by
  unfold tailWord_319107
  simp only [CollatzResearch.WordTrace]
  refine ⟨11638788454937312981811575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7759192303291541987874383 11638788454937312981811575)
  ·
    refine ⟨17458182682405969472717363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11638788454937312981811575 17458182682405969472717363)
    ·
      refine ⟨26187274023608954209076045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17458182682405969472717363 26187274023608954209076045)
      ·
        refine ⟨9820227758853357828403517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26187274023608954209076045 9820227758853357828403517)
        ·
          refine ⟨3682585409570009185651319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9820227758853357828403517 3682585409570009185651319)
          ·
            refine ⟨5523878114355013778476979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3682585409570009185651319 5523878114355013778476979)
            ·
              refine ⟨8285817171532520667715469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5523878114355013778476979 8285817171532520667715469)
              ·
                refine ⟨3107181439324695250393301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8285817171532520667715469 3107181439324695250393301)
                ·
                  refine ⟨72824564984172544931093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3107181439324695250393301 72824564984172544931093)
                  ·
                    rfl

theorem cell21_319107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 3, 7].length) (baseStart_319107 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_319107 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_319107 prefixEnd_319107 := by exact prefixLift 319107
  have htrace : WordTrace (prefixWord ++ tailWord_319107) baseStart_319107 baseEnd_319107 := by
    simpa [prefixWord, tailWord_319107, baseEnd_319107] using wordTrace_append hprefix tailTrace_319107
  have hstable : (prefixWord ++ tailWord_319107).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_319107).length < 2 ^ (prefixWord ++ tailWord_319107).sum := by decide
  have hdescent : baseEnd_319107 < baseStart_319107 := by decide
  rcases family_descends (prefixWord ++ tailWord_319107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_319158 : List Nat := [5, 1, 3, 1, 1, 2, 1, 2, 5]
def baseStart_319158 : Nat := 118140960795 + 319158 * 2 ^ 59
def prefixEnd_319158 : Nat := 4983230072969 + 3 ^ 40 * 319158 * 2
def baseEnd_319158 : Nat := 72836203879007789580989

theorem tailTrace_319158 : CollatzResearch.WordTrace tailWord_319158 prefixEnd_319158 72836203879007789580989 := by
  unfold tailWord_319158
  simp only [CollatzResearch.WordTrace]
  refine ⟨727540536109534293244883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 7760432385168365794612085 727540536109534293244883)
  ·
    refine ⟨1091310804164301439867325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 727540536109534293244883 1091310804164301439867325)
    ·
      refine ⟨409241551561613039950247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1091310804164301439867325 409241551561613039950247)
      ·
        refine ⟨613862327342419559925371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 409241551561613039950247 613862327342419559925371)
        ·
          refine ⟨920793491013629339888057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 613862327342419559925371 920793491013629339888057)
          ·
            refine ⟨690595118260222004916043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 920793491013629339888057 690595118260222004916043)
            ·
              refine ⟨1035892677390333007374065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 690595118260222004916043 1035892677390333007374065)
              ·
                refine ⟨776919508042749755530549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1035892677390333007374065 776919508042749755530549)
                ·
                  refine ⟨72836203879007789580989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 776919508042749755530549 72836203879007789580989)
                  ·
                    rfl

theorem cell21_319158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 2, 1, 2, 5].length) (baseStart_319158 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_319158 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_319158 prefixEnd_319158 := by exact prefixLift 319158
  have htrace : WordTrace (prefixWord ++ tailWord_319158) baseStart_319158 baseEnd_319158 := by
    simpa [prefixWord, tailWord_319158, baseEnd_319158] using wordTrace_append hprefix tailTrace_319158
  have hstable : (prefixWord ++ tailWord_319158).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_319158).length < 2 ^ (prefixWord ++ tailWord_319158).sum := by decide
  have hdescent : baseEnd_319158 < baseStart_319158 := by decide
  rcases family_descends (prefixWord ++ tailWord_319158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_319220 : List Nat := [2, 6, 1, 1, 1, 1, 4, 5]
def baseStart_319220 : Nat := 118140960795 + 319220 * 2 ^ 59
def prefixEnd_319220 : Nat := 4983230072969 + 3 ^ 40 * 319220 * 2
def baseEnd_319220 : Nat := 24283451041236486515843

theorem tailTrace_319220 : CollatzResearch.WordTrace tailWord_319220 prefixEnd_319220 24283451041236486515843 := by
  unfold tailWord_319220
  simp only [CollatzResearch.WordTrace]
  refine ⟨5821454951763966640337557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7761939935685288853783409 5821454951763966640337557)
  ·
    refine ⟨272880700863935936265823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 5821454951763966640337557 272880700863935936265823)
    ·
      refine ⟨409321051295903904398735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 272880700863935936265823 409321051295903904398735)
      ·
        refine ⟨613981576943855856598103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 409321051295903904398735 613981576943855856598103)
        ·
          refine ⟨920972365415783784897155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 613981576943855856598103 920972365415783784897155)
          ·
            refine ⟨1381458548123675677345733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 920972365415783784897155 1381458548123675677345733)
            ·
              refine ⟨259023477773189189502325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1381458548123675677345733 259023477773189189502325)
              ·
                refine ⟨24283451041236486515843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 259023477773189189502325 24283451041236486515843)
                ·
                  rfl

theorem cell21_319220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 4, 5].length) (baseStart_319220 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_319220 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_319220 prefixEnd_319220 := by exact prefixLift 319220
  have htrace : WordTrace (prefixWord ++ tailWord_319220) baseStart_319220 baseEnd_319220 := by
    simpa [prefixWord, tailWord_319220, baseEnd_319220] using wordTrace_append hprefix tailTrace_319220
  have hstable : (prefixWord ++ tailWord_319220).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_319220).length < 2 ^ (prefixWord ++ tailWord_319220).sum := by decide
  have hdescent : baseEnd_319220 < baseStart_319220 := by decide
  rcases family_descends (prefixWord ++ tailWord_319220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_319304 : List Nat := [2, 1, 3, 1, 1, 13]
def baseStart_319304 : Nat := 118140960795 + 319304 * 2 ^ 59
def prefixEnd_319304 : Nat := 4983230072969 + 3 ^ 40 * 319304 * 2
def baseEnd_319304 : Nat := 2698871224746073338791

theorem tailTrace_319304 : CollatzResearch.WordTrace tailWord_319304 prefixEnd_319304 2698871224746073338791 := by
  unfold tailWord_319304
  simp only [CollatzResearch.WordTrace]
  refine ⟨5822986817611807813366483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7763982423482410417821977 5822986817611807813366483)
  ·
    refine ⟨8734480226417711720049725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5822986817611807813366483 8734480226417711720049725)
    ·
      refine ⟨3275430084906641895018647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8734480226417711720049725 3275430084906641895018647)
      ·
        refine ⟨4913145127359962842527971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3275430084906641895018647 4913145127359962842527971)
        ·
          refine ⟨7369717691039944263791957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4913145127359962842527971 7369717691039944263791957)
          ·
            refine ⟨2698871224746073338791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 13 7369717691039944263791957 2698871224746073338791)
            ·
              rfl

theorem cell21_319304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 13].length) (baseStart_319304 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_319304 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_319304 prefixEnd_319304 := by exact prefixLift 319304
  have htrace : WordTrace (prefixWord ++ tailWord_319304) baseStart_319304 baseEnd_319304 := by
    simpa [prefixWord, tailWord_319304, baseEnd_319304] using wordTrace_append hprefix tailTrace_319304
  have hstable : (prefixWord ++ tailWord_319304).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_319304).length < 2 ^ (prefixWord ++ tailWord_319304).sum := by decide
  have hdescent : baseEnd_319304 < baseStart_319304 := by decide
  rcases family_descends (prefixWord ++ tailWord_319304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_319473 : List Nat := [1, 2, 2, 2, 6, 8]
def baseStart_319473 : Nat := 118140960795 + 319473 * 2 ^ 59
def prefixEnd_319473 : Nat := 4983230072969 + 3 ^ 40 * 319473 * 2
def baseEnd_319473 : Nat := 2700299672986564512235

theorem tailTrace_319473 : CollatzResearch.WordTrace tailWord_319473 prefixEnd_319473 2700299672986564512235 := by
  unfold tailWord_319473
  simp only [CollatzResearch.WordTrace]
  refine ⟨11652137571611357489635073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7768091714407571659756715 11652137571611357489635073)
  ·
    refine ⟨8739103178708518117226305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11652137571611357489635073 8739103178708518117226305)
    ·
      refine ⟨6554327384031388587919729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8739103178708518117226305 6554327384031388587919729)
      ·
        refine ⟨4915745538023541440939797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6554327384031388587919729 4915745538023541440939797)
        ·
          refine ⟨230425572094853505044053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 4915745538023541440939797 230425572094853505044053)
          ·
            refine ⟨2700299672986564512235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 230425572094853505044053 2700299672986564512235)
            ·
              rfl

theorem cell21_319473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 6, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 6, 8].length) (baseStart_319473 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_319473 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_319473 prefixEnd_319473 := by exact prefixLift 319473
  have htrace : WordTrace (prefixWord ++ tailWord_319473) baseStart_319473 baseEnd_319473 := by
    simpa [prefixWord, tailWord_319473, baseEnd_319473] using wordTrace_append hprefix tailTrace_319473
  have hstable : (prefixWord ++ tailWord_319473).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_319473).length < 2 ^ (prefixWord ++ tailWord_319473).sum := by decide
  have hdescent : baseEnd_319473 < baseStart_319473 := by decide
  rcases family_descends (prefixWord ++ tailWord_319473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_319566 : List Nat := [4, 1, 1, 1, 1, 6, 2, 5]
def baseStart_319566 : Nat := 118140960795 + 319566 * 2 ^ 59
def prefixEnd_319566 : Nat := 4983230072969 + 3 ^ 40 * 319566 * 2
def baseEnd_319566 : Nat := 24309771679229915593385

theorem tailTrace_319566 : CollatzResearch.WordTrace tailWord_319566 prefixEnd_319566 24309771679229915593385 := by
  unfold tailWord_319566
  simp only [CollatzResearch.WordTrace]
  refine ⟨1456941195034304296596319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7770353040182956248513701 1456941195034304296596319)
  ·
    refine ⟨2185411792551456444894479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1456941195034304296596319 2185411792551456444894479)
    ·
      refine ⟨3278117688827184667341719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2185411792551456444894479 3278117688827184667341719)
      ·
        refine ⟨4917176533240777001012579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3278117688827184667341719 4917176533240777001012579)
        ·
          refine ⟨7375764799861165501518869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4917176533240777001012579 7375764799861165501518869)
          ·
            refine ⟨345738974993492132883697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 7375764799861165501518869 345738974993492132883697)
            ·
              refine ⟨259304231245119099662773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 345738974993492132883697 259304231245119099662773)
              ·
                refine ⟨24309771679229915593385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 259304231245119099662773 24309771679229915593385)
                ·
                  rfl

theorem cell21_319566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 6, 2, 5].length) (baseStart_319566 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_319566 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_319566 prefixEnd_319566 := by exact prefixLift 319566
  have htrace : WordTrace (prefixWord ++ tailWord_319566) baseStart_319566 baseEnd_319566 := by
    simpa [prefixWord, tailWord_319566, baseEnd_319566] using wordTrace_append hprefix tailTrace_319566
  have hstable : (prefixWord ++ tailWord_319566).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_319566).length < 2 ^ (prefixWord ++ tailWord_319566).sum := by decide
  have hdescent : baseEnd_319566 < baseStart_319566 := by decide
  rcases family_descends (prefixWord ++ tailWord_319566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_319577 : List Nat := [1, 2, 1, 2, 2, 1, 3, 1, 8]
def baseStart_319577 : Nat := 118140960795 + 319577 * 2 ^ 59
def prefixEnd_319577 : Nat := 4983230072969 + 3 ^ 40 * 319577 * 2
def baseEnd_319577 : Nat := 72931825387556172096799

theorem tailTrace_319577 : CollatzResearch.WordTrace tailWord_319577 prefixEnd_319577 72931825387556172096799 := by
  unfold tailWord_319577
  simp only [CollatzResearch.WordTrace]
  refine ⟨11655930763234583251420985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7770620508823055500947323 11655930763234583251420985)
  ·
    refine ⟨8741948072425937438565739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11655930763234583251420985 8741948072425937438565739)
    ·
      refine ⟨13112922108638906157848609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8741948072425937438565739 13112922108638906157848609)
      ·
        refine ⟨9834691581479179618386457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13112922108638906157848609 9834691581479179618386457)
        ·
          refine ⟨7376018686109384713789843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9834691581479179618386457 7376018686109384713789843)
          ·
            refine ⟨11064028029164077070684765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7376018686109384713789843 11064028029164077070684765)
            ·
              refine ⟨4149010510936528901506787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11064028029164077070684765 4149010510936528901506787)
              ·
                refine ⟨6223515766404793352260181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4149010510936528901506787 6223515766404793352260181)
                ·
                  refine ⟨72931825387556172096799, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 6223515766404793352260181 72931825387556172096799)
                  ·
                    rfl

theorem cell21_319577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 3, 1, 8].length) (baseStart_319577 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_319577 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_319577 prefixEnd_319577 := by exact prefixLift 319577
  have htrace : WordTrace (prefixWord ++ tailWord_319577) baseStart_319577 baseEnd_319577 := by
    simpa [prefixWord, tailWord_319577, baseEnd_319577] using wordTrace_append hprefix tailTrace_319577
  have hstable : (prefixWord ++ tailWord_319577).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_319577).length < 2 ^ (prefixWord ++ tailWord_319577).sum := by decide
  have hdescent : baseEnd_319577 < baseStart_319577 := by decide
  rcases family_descends (prefixWord ++ tailWord_319577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_319701 : List Nat := [1, 3, 2, 4, 2, 1, 8]
def baseStart_319701 : Nat := 118140960795 + 319701 * 2 ^ 59
def prefixEnd_319701 : Nat := 4983230072969 + 3 ^ 40 * 319701 * 2
def baseEnd_319701 : Nat := 8106680430773279114431

theorem tailTrace_319701 : CollatzResearch.WordTrace tailWord_319701 prefixEnd_319701 8106680430773279114431 := by
  unfold tailWord_319701
  simp only [CollatzResearch.WordTrace]
  refine ⟨11660453414785352428934957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7773635609856901619289971 11660453414785352428934957)
  ·
    refine ⟨4372670030544507160850609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11660453414785352428934957 4372670030544507160850609)
    ·
      refine ⟨3279502522908380370637957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4372670030544507160850609 3279502522908380370637957)
      ·
        refine ⟨614906723045321319494617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3279502522908380370637957 614906723045321319494617)
        ·
          refine ⟨461180042283990989620963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 614906723045321319494617 461180042283990989620963)
          ·
            refine ⟨691770063425986484431445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 461180042283990989620963 691770063425986484431445)
            ·
              refine ⟨8106680430773279114431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 691770063425986484431445 8106680430773279114431)
              ·
                rfl

theorem cell21_319701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 1, 8].length) (baseStart_319701 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_319701 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_319701 prefixEnd_319701 := by exact prefixLift 319701
  have htrace : WordTrace (prefixWord ++ tailWord_319701) baseStart_319701 baseEnd_319701 := by
    simpa [prefixWord, tailWord_319701, baseEnd_319701] using wordTrace_append hprefix tailTrace_319701
  have hstable : (prefixWord ++ tailWord_319701).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_319701).length < 2 ^ (prefixWord ++ tailWord_319701).sum := by decide
  have hdescent : baseEnd_319701 < baseStart_319701 := by decide
  rcases family_descends (prefixWord ++ tailWord_319701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_319780 : List Nat := [2, 3, 1, 3, 1, 4, 2, 1, 4]
def baseStart_319780 : Nat := 118140960795 + 319780 * 2 ^ 59
def prefixEnd_319780 : Nat := 4983230072969 + 3 ^ 40 * 319780 * 2
def baseEnd_319780 : Nat := 72978152753272930213051

theorem tailTrace_319780 : CollatzResearch.WordTrace tailWord_319780 prefixEnd_319780 72978152753272930213051 := by
  unfold tailWord_319780
  simp only [CollatzResearch.WordTrace]
  refine ⟨5831667390749574460530397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7775556520999432614040529 5831667390749574460530397)
  ·
    refine ⟨2186875271531090422698899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5831667390749574460530397 2186875271531090422698899)
    ·
      refine ⟨3280312907296635634048349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2186875271531090422698899 3280312907296635634048349)
      ·
        refine ⟨1230117340236238362768131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3280312907296635634048349 1230117340236238362768131)
        ·
          refine ⟨1845176010354357544152197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1230117340236238362768131 1845176010354357544152197)
          ·
            refine ⟨345970501941442039528537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1845176010354357544152197 345970501941442039528537)
            ·
              refine ⟨259477876456081529646403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 345970501941442039528537 259477876456081529646403)
              ·
                refine ⟨389216814684122294469605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 259477876456081529646403 389216814684122294469605)
                ·
                  refine ⟨72978152753272930213051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 389216814684122294469605 72978152753272930213051)
                  ·
                    rfl

theorem cell21_319780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 4, 2, 1, 4].length) (baseStart_319780 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_319780 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_319780 prefixEnd_319780 := by exact prefixLift 319780
  have htrace : WordTrace (prefixWord ++ tailWord_319780) baseStart_319780 baseEnd_319780 := by
    simpa [prefixWord, tailWord_319780, baseEnd_319780] using wordTrace_append hprefix tailTrace_319780
  have hstable : (prefixWord ++ tailWord_319780).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_319780).length < 2 ^ (prefixWord ++ tailWord_319780).sum := by decide
  have hdescent : baseEnd_319780 < baseStart_319780 := by decide
  rcases family_descends (prefixWord ++ tailWord_319780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_319825 : List Nat := [1, 2, 2, 1, 4, 2, 4, 2, 3]
def baseStart_319825 : Nat := 118140960795 + 319825 * 2 ^ 59
def prefixEnd_319825 : Nat := 4983230072969 + 3 ^ 40 * 319825 * 2
def baseEnd_319825 : Nat := 72988422366362851962959

theorem tailTrace_319825 : CollatzResearch.WordTrace tailWord_319825 prefixEnd_319825 72988422366362851962959 := by
  unfold tailWord_319825
  simp only [CollatzResearch.WordTrace]
  refine ⟨11664976066336121606448929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7776650710890747737632619 11664976066336121606448929)
  ·
    refine ⟨8748732049752091204836697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11664976066336121606448929 8748732049752091204836697)
    ·
      refine ⟨6561549037314068403627523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8748732049752091204836697 6561549037314068403627523)
      ·
        refine ⟨9842323555971102605441285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6561549037314068403627523 9842323555971102605441285)
        ·
          refine ⟨1845435666744581738520241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9842323555971102605441285 1845435666744581738520241)
          ·
            refine ⟨1384076750058436303890181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1845435666744581738520241 1384076750058436303890181)
            ·
              refine ⟨259514390635956806979409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1384076750058436303890181 259514390635956806979409)
              ·
                refine ⟨194635792976967605234557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 259514390635956806979409 194635792976967605234557)
                ·
                  refine ⟨72988422366362851962959, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 194635792976967605234557 72988422366362851962959)
                  ·
                    rfl

theorem cell21_319825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 4, 2, 3].length) (baseStart_319825 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_319825 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_319825 prefixEnd_319825 := by exact prefixLift 319825
  have htrace : WordTrace (prefixWord ++ tailWord_319825) baseStart_319825 baseEnd_319825 := by
    simpa [prefixWord, tailWord_319825, baseEnd_319825] using wordTrace_append hprefix tailTrace_319825
  have hstable : (prefixWord ++ tailWord_319825).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_319825).length < 2 ^ (prefixWord ++ tailWord_319825).sum := by decide
  have hdescent : baseEnd_319825 < baseStart_319825 := by decide
  rcases family_descends (prefixWord ++ tailWord_319825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_319853 : List Nat := [1, 5, 1, 1, 1, 2, 5, 5]
def baseStart_319853 : Nat := 118140960795 + 319853 * 2 ^ 59
def prefixEnd_319853 : Nat := 4983230072969 + 3 ^ 40 * 319853 * 2
def baseEnd_319853 : Nat := 24331604115947008498745

theorem tailTrace_319853 : CollatzResearch.WordTrace tailWord_319853 prefixEnd_319853 24331604115947008498745 := by
  unfold tailWord_319853
  simp only [CollatzResearch.WordTrace]
  refine ⟨11665997310234682388468213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7777331540156454925645475 11665997310234682388468213)
  ·
    refine ⟨1093687247834501473918895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 11665997310234682388468213 1093687247834501473918895)
    ·
      refine ⟨1640530871751752210878343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1093687247834501473918895 1640530871751752210878343)
      ·
        refine ⟨2460796307627628316317515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1640530871751752210878343 2460796307627628316317515)
        ·
          refine ⟨3691194461441442474476273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2460796307627628316317515 3691194461441442474476273)
          ·
            refine ⟨2768395846081081855857205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3691194461441442474476273 2768395846081081855857205)
            ·
              refine ⟨259537110570101423986613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2768395846081081855857205 259537110570101423986613)
              ·
                refine ⟨24331604115947008498745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 259537110570101423986613 24331604115947008498745)
                ·
                  rfl

theorem cell21_319853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 5, 5].length) (baseStart_319853 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_319853 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_319853 prefixEnd_319853 := by exact prefixLift 319853
  have htrace : WordTrace (prefixWord ++ tailWord_319853) baseStart_319853 baseEnd_319853 := by
    simpa [prefixWord, tailWord_319853, baseEnd_319853] using wordTrace_append hprefix tailTrace_319853
  have hstable : (prefixWord ++ tailWord_319853).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_319853).length < 2 ^ (prefixWord ++ tailWord_319853).sum := by decide
  have hdescent : baseEnd_319853 < baseStart_319853 := by decide
  rcases family_descends (prefixWord ++ tailWord_319853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_319884 : List Nat := [2, 2, 1, 2, 1, 4, 2, 4, 3]
def baseStart_319884 : Nat := 118140960795 + 319884 * 2 ^ 59
def prefixEnd_319884 : Nat := 4983230072969 + 3 ^ 40 * 319884 * 2
def baseEnd_319884 : Nat := 73001886970191860479505

theorem tailTrace_319884 : CollatzResearch.WordTrace tailWord_319884 prefixEnd_319884 73001886970191860479505 := by
  unfold tailWord_319884
  simp only [CollatzResearch.WordTrace]
  refine ⟨5833563986561187341423353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7778085315414916455231137 5833563986561187341423353)
  ·
    refine ⟨4375172989920890506067515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5833563986561187341423353 4375172989920890506067515)
    ·
      refine ⟨6562759484881335759101273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4375172989920890506067515 6562759484881335759101273)
      ·
        refine ⟨4922069613661001819325955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6562759484881335759101273 4922069613661001819325955)
        ·
          refine ⟨7383104420491502728988933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4922069613661001819325955 7383104420491502728988933)
          ·
            refine ⟨1384332078842156761685425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7383104420491502728988933 1384332078842156761685425)
            ·
              refine ⟨1038249059131617571264069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1384332078842156761685425 1038249059131617571264069)
              ·
                refine ⟨194671698587178294612013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1038249059131617571264069 194671698587178294612013)
                ·
                  refine ⟨73001886970191860479505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 194671698587178294612013 73001886970191860479505)
                  ·
                    rfl

theorem cell21_319884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 2, 4, 3].length) (baseStart_319884 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_319884 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_319884 prefixEnd_319884 := by exact prefixLift 319884
  have htrace : WordTrace (prefixWord ++ tailWord_319884) baseStart_319884 baseEnd_319884 := by
    simpa [prefixWord, tailWord_319884, baseEnd_319884] using wordTrace_append hprefix tailTrace_319884
  have hstable : (prefixWord ++ tailWord_319884).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_319884).length < 2 ^ (prefixWord ++ tailWord_319884).sum := by decide
  have hdescent : baseEnd_319884 < baseStart_319884 := by decide
  rcases family_descends (prefixWord ++ tailWord_319884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_319943 : List Nat := [1, 1, 4, 1, 1, 4, 3, 1, 5]
def baseStart_319943 : Nat := 118140960795 + 319943 * 2 ^ 59
def prefixEnd_319943 : Nat := 4983230072969 + 3 ^ 40 * 319943 * 2
def baseEnd_319943 : Nat := 73015351574020868996051

theorem tailTrace_319943 : CollatzResearch.WordTrace tailWord_319943 prefixEnd_319943 73015351574020868996051 := by
  unfold tailWord_319943
  simp only [CollatzResearch.WordTrace]
  refine ⟨11669279879908627759244483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7779519919939085172829655 11669279879908627759244483)
  ·
    refine ⟨17503919819862941638866725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11669279879908627759244483 17503919819862941638866725)
    ·
      refine ⟨3281984966224301557287511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17503919819862941638866725 3281984966224301557287511)
      ·
        refine ⟨4922977449336452335931267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3281984966224301557287511 4922977449336452335931267)
        ·
          refine ⟨7384466174004678503896901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4922977449336452335931267 7384466174004678503896901)
          ·
            refine ⟨1384587407625877219480669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7384466174004678503896901 1384587407625877219480669)
            ·
              refine ⟨519220277859703957305251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1384587407625877219480669 519220277859703957305251)
              ·
                refine ⟨778830416789555935957877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 519220277859703957305251 778830416789555935957877)
                ·
                  refine ⟨73015351574020868996051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 778830416789555935957877 73015351574020868996051)
                  ·
                    rfl

theorem cell21_319943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 3, 1, 5].length) (baseStart_319943 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_319943 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_319943 prefixEnd_319943 := by exact prefixLift 319943
  have htrace : WordTrace (prefixWord ++ tailWord_319943) baseStart_319943 baseEnd_319943 := by
    simpa [prefixWord, tailWord_319943, baseEnd_319943] using wordTrace_append hprefix tailTrace_319943
  have hstable : (prefixWord ++ tailWord_319943).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_319943).length < 2 ^ (prefixWord ++ tailWord_319943).sum := by decide
  have hdescent : baseEnd_319943 < baseStart_319943 := by decide
  rcases family_descends (prefixWord ++ tailWord_319943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_319988 : List Nat := [2, 6, 13]
def baseStart_319988 : Nat := 118140960795 + 319988 * 2 ^ 59
def prefixEnd_319988 : Nat := 4983230072969 + 3 ^ 40 * 319988 * 2
def baseEnd_319988 : Nat := 100172319872579959871

theorem tailTrace_319988 : CollatzResearch.WordTrace tailWord_319988 prefixEnd_319988 100172319872579959871 := by
  unfold tailWord_319988
  simp only [CollatzResearch.WordTrace]
  refine ⟨5835460582372800222316309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7780614109830400296421745 5835460582372800222316309)
  ·
    refine ⟨273537214798725010421077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 5835460582372800222316309 273537214798725010421077)
    ·
      refine ⟨100172319872579959871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 13 273537214798725010421077 100172319872579959871)
      ·
        rfl

theorem cell21_319988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 13].length) (baseStart_319988 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_319988 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_319988 prefixEnd_319988 := by exact prefixLift 319988
  have htrace : WordTrace (prefixWord ++ tailWord_319988) baseStart_319988 baseEnd_319988 := by
    simpa [prefixWord, tailWord_319988, baseEnd_319988] using wordTrace_append hprefix tailTrace_319988
  have hstable : (prefixWord ++ tailWord_319988).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_319988).length < 2 ^ (prefixWord ++ tailWord_319988).sum := by decide
  have hdescent : baseEnd_319988 < baseStart_319988 := by decide
  rcases family_descends (prefixWord ++ tailWord_319988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_320033 : List Nat := [1, 2, 3, 2, 2, 1, 2, 2, 6]
def baseStart_320033 : Nat := 118140960795 + 320033 * 2 ^ 59
def prefixEnd_320033 : Nat := 4983230072969 + 3 ^ 40 * 320033 * 2
def baseEnd_320033 : Nat := 73035890800200712495867

theorem tailTrace_320033 : CollatzResearch.WordTrace tailWord_320033 prefixEnd_320033 73035890800200712495867 := by
  unfold tailWord_320033
  simp only [CollatzResearch.WordTrace]
  refine ⟨11672562449582573130020753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7781708299721715420013835 11672562449582573130020753)
  ·
    refine ⟨8754421837186929847515565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11672562449582573130020753 8754421837186929847515565)
    ·
      refine ⟨3282908188945098692818337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8754421837186929847515565 3282908188945098692818337)
      ·
        refine ⟨2462181141708824019613753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3282908188945098692818337 2462181141708824019613753)
        ·
          refine ⟨1846635856281618014710315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2462181141708824019613753 1846635856281618014710315)
          ·
            refine ⟨2769953784422427022065473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1846635856281618014710315 2769953784422427022065473)
            ·
              refine ⟨2077465338316820266549105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2769953784422427022065473 2077465338316820266549105)
              ·
                refine ⟨1558099003737615199911829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2077465338316820266549105 1558099003737615199911829)
                ·
                  refine ⟨73035890800200712495867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1558099003737615199911829 73035890800200712495867)
                  ·
                    rfl

theorem cell21_320033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 2, 2, 6].length) (baseStart_320033 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_320033 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_320033 prefixEnd_320033 := by exact prefixLift 320033
  have htrace : WordTrace (prefixWord ++ tailWord_320033) baseStart_320033 baseEnd_320033 := by
    simpa [prefixWord, tailWord_320033, baseEnd_320033] using wordTrace_append hprefix tailTrace_320033
  have hstable : (prefixWord ++ tailWord_320033).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_320033).length < 2 ^ (prefixWord ++ tailWord_320033).sum := by decide
  have hdescent : baseEnd_320033 < baseStart_320033 := by decide
  rcases family_descends (prefixWord ++ tailWord_320033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_320050 : List Nat := [3, 2, 1, 1, 2, 1, 5, 2, 4]
def baseStart_320050 : Nat := 118140960795 + 320050 * 2 ^ 59
def prefixEnd_320050 : Nat := 4983230072969 + 3 ^ 40 * 320050 * 2
def baseEnd_320050 : Nat := 73039770431812460712499

theorem tailTrace_320050 : CollatzResearch.WordTrace tailWord_320050 prefixEnd_320050 73039770431812460712499 := by
  unfold tailWord_320050
  simp only [CollatzResearch.WordTrace]
  refine ⟨2918295622630246258347401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7782121660347323355593069 2918295622630246258347401)
  ·
    refine ⟨2188721716972684693760551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2918295622630246258347401 2188721716972684693760551)
    ·
      refine ⟨3283082575459027040640827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2188721716972684693760551 3283082575459027040640827)
      ·
        refine ⟨4924623863188540560961241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3283082575459027040640827 4924623863188540560961241)
        ·
          refine ⟨3693467897391405420720931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4924623863188540560961241 3693467897391405420720931)
          ·
            refine ⟨5540201846087108131081397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3693467897391405420720931 5540201846087108131081397)
            ·
              refine ⟨519393923070666387288881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5540201846087108131081397 519393923070666387288881)
              ·
                refine ⟨389545442302999790466661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 519393923070666387288881 389545442302999790466661)
                ·
                  refine ⟨73039770431812460712499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 389545442302999790466661 73039770431812460712499)
                  ·
                    rfl

theorem cell21_320050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 5, 2, 4].length) (baseStart_320050 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_320050 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_320050 prefixEnd_320050 := by exact prefixLift 320050
  have htrace : WordTrace (prefixWord ++ tailWord_320050) baseStart_320050 baseEnd_320050 := by
    simpa [prefixWord, tailWord_320050, baseEnd_320050] using wordTrace_append hprefix tailTrace_320050
  have hstable : (prefixWord ++ tailWord_320050).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_320050).length < 2 ^ (prefixWord ++ tailWord_320050).sum := by decide
  have hdescent : baseEnd_320050 < baseStart_320050 := by decide
  rcases family_descends (prefixWord ++ tailWord_320050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_320081 : List Nat := [1, 2, 2, 1, 3, 5, 2, 5]
def baseStart_320081 : Nat := 118140960795 + 320081 * 2 ^ 59
def prefixEnd_320081 : Nat := 4983230072969 + 3 ^ 40 * 320081 * 2
def baseEnd_320081 : Nat := 24348948351387765231923

theorem tailTrace_320081 : CollatzResearch.WordTrace tailWord_320081 prefixEnd_320081 24348948351387765231923 := by
  unfold tailWord_320081
  simp only [CollatzResearch.WordTrace]
  refine ⟨11674313153408677327768097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7782875435605784885178731 11674313153408677327768097)
  ·
    refine ⟨8755734865056507995826073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11674313153408677327768097 8755734865056507995826073)
    ·
      refine ⟨6566801148792380996869555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8755734865056507995826073 6566801148792380996869555)
      ·
        refine ⟨9850201723188571495304333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6566801148792380996869555 9850201723188571495304333)
        ·
          refine ⟨3693825646195714310739125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9850201723188571495304333 3693825646195714310739125)
          ·
            refine ⟨346296154330848216631793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 3693825646195714310739125 346296154330848216631793)
            ·
              refine ⟨259722115748136162473845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 346296154330848216631793 259722115748136162473845)
              ·
                refine ⟨24348948351387765231923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 259722115748136162473845 24348948351387765231923)
                ·
                  rfl

theorem cell21_320081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 5, 2, 5].length) (baseStart_320081 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_320081 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_320081 prefixEnd_320081 := by exact prefixLift 320081
  have htrace : WordTrace (prefixWord ++ tailWord_320081) baseStart_320081 baseEnd_320081 := by
    simpa [prefixWord, tailWord_320081, baseEnd_320081] using wordTrace_append hprefix tailTrace_320081
  have hstable : (prefixWord ++ tailWord_320081).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_320081).length < 2 ^ (prefixWord ++ tailWord_320081).sum := by decide
  have hdescent : baseEnd_320081 < baseStart_320081 := by decide
  rcases family_descends (prefixWord ++ tailWord_320081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_320098 : List Nat := [3, 3, 2, 3, 1, 2, 7]
def baseStart_320098 : Nat := 118140960795 + 320098 * 2 ^ 59
def prefixEnd_320098 : Nat := 4983230072969 + 3 ^ 40 * 320098 * 2
def baseEnd_320098 : Nat := 8116747187308338212489

theorem tailTrace_320098 : CollatzResearch.WordTrace tailWord_320098 prefixEnd_320098 8116747187308338212489 := by
  unfold tailWord_320098
  simp only [CollatzResearch.WordTrace]
  refine ⟨2918733298586772307784237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7783288796231392820757965 2918733298586772307784237)
  ·
    refine ⟨1094524986970039615419089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2918733298586772307784237 1094524986970039615419089)
    ·
      refine ⟨820893740227529711564317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1094524986970039615419089 820893740227529711564317)
      ·
        refine ⟨307835152585323641836619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 820893740227529711564317 307835152585323641836619)
        ·
          refine ⟨461752728877985462754929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 307835152585323641836619 461752728877985462754929)
          ·
            refine ⟨346314546658489097066197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 461752728877985462754929 346314546658489097066197)
            ·
              refine ⟨8116747187308338212489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 346314546658489097066197 8116747187308338212489)
              ·
                rfl

theorem cell21_320098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 2, 7].length) (baseStart_320098 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_320098 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_320098 prefixEnd_320098 := by exact prefixLift 320098
  have htrace : WordTrace (prefixWord ++ tailWord_320098) baseStart_320098 baseEnd_320098 := by
    simpa [prefixWord, tailWord_320098, baseEnd_320098] using wordTrace_append hprefix tailTrace_320098
  have hstable : (prefixWord ++ tailWord_320098).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_320098).length < 2 ^ (prefixWord ++ tailWord_320098).sum := by decide
  have hdescent : baseEnd_320098 < baseStart_320098 := by decide
  rcases family_descends (prefixWord ++ tailWord_320098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_320112 : List Nat := [2, 1, 1, 1, 7, 2, 1, 1, 5]
def baseStart_320112 : Nat := 118140960795 + 320112 * 2 ^ 59
def prefixEnd_320112 : Nat := 4983230072969 + 3 ^ 40 * 320112 * 2
def baseEnd_320112 : Nat := 73053919676514130679039

theorem tailTrace_320112 : CollatzResearch.WordTrace tailWord_320112 prefixEnd_320112 73053919676514130679039 := by
  unfold tailWord_320112
  simp only [CollatzResearch.WordTrace]
  refine ⟨5837721908148184811073295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7783629210864246414764393 5837721908148184811073295)
  ·
    refine ⟨8756582862222277216609943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5837721908148184811073295 8756582862222277216609943)
    ·
      refine ⟨13134874293333415824914915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8756582862222277216609943 13134874293333415824914915)
      ·
        refine ⟨19702311440000123737372373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13134874293333415824914915 19702311440000123737372373)
        ·
          refine ⟨461772924375002900094665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 19702311440000123737372373 461772924375002900094665)
          ·
            refine ⟨346329693281252175070999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 461772924375002900094665 346329693281252175070999)
            ·
              refine ⟨519494539921878262606499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 346329693281252175070999 519494539921878262606499)
              ·
                refine ⟨779241809882817393909749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 519494539921878262606499 779241809882817393909749)
                ·
                  refine ⟨73053919676514130679039, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 779241809882817393909749 73053919676514130679039)
                  ·
                    rfl

theorem cell21_320112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 2, 1, 1, 5].length) (baseStart_320112 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_320112 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_320112 prefixEnd_320112 := by exact prefixLift 320112
  have htrace : WordTrace (prefixWord ++ tailWord_320112) baseStart_320112 baseEnd_320112 := by
    simpa [prefixWord, tailWord_320112, baseEnd_320112] using wordTrace_append hprefix tailTrace_320112
  have hstable : (prefixWord ++ tailWord_320112).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_320112).length < 2 ^ (prefixWord ++ tailWord_320112).sum := by decide
  have hdescent : baseEnd_320112 < baseStart_320112 := by decide
  rcases family_descends (prefixWord ++ tailWord_320112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_320174 : List Nat := [4, 1, 4, 1, 1, 3, 1, 6]
def baseStart_320174 : Nat := 118140960795 + 320174 * 2 ^ 59
def prefixEnd_320174 : Nat := 4983230072969 + 3 ^ 40 * 320174 * 2
def baseEnd_320174 : Nat := 24356022973738600215193

theorem tailTrace_320174 : CollatzResearch.WordTrace tailWord_320174 prefixEnd_320174 24356022973738600215193 := by
  unfold tailWord_320174
  simp only [CollatzResearch.WordTrace]
  refine ⟨1459713142758969276362947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7785136761381169473935717 1459713142758969276362947)
  ·
    refine ⟨2189569714138453914544421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1459713142758969276362947 2189569714138453914544421)
    ·
      refine ⟨410544321400960108977079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2189569714138453914544421 410544321400960108977079)
      ·
        refine ⟨615816482101440163465619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 410544321400960108977079 615816482101440163465619)
        ·
          refine ⟨923724723152160245198429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 615816482101440163465619 923724723152160245198429)
          ·
            refine ⟨346396771182060091949411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 923724723152160245198429 346396771182060091949411)
            ·
              refine ⟨519595156773090137924117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 346396771182060091949411 519595156773090137924117)
              ·
                refine ⟨24356022973738600215193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 519595156773090137924117 24356022973738600215193)
                ·
                  rfl

theorem cell21_320174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 3, 1, 6].length) (baseStart_320174 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_320174 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_320174 prefixEnd_320174 := by exact prefixLift 320174
  have htrace : WordTrace (prefixWord ++ tailWord_320174) baseStart_320174 baseEnd_320174 := by
    simpa [prefixWord, tailWord_320174, baseEnd_320174] using wordTrace_append hprefix tailTrace_320174
  have hstable : (prefixWord ++ tailWord_320174).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_320174).length < 2 ^ (prefixWord ++ tailWord_320174).sum := by decide
  have hdescent : baseEnd_320174 < baseStart_320174 := by decide
  rcases family_descends (prefixWord ++ tailWord_320174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_320264 : List Nat := [2, 1, 3, 2, 2, 2, 3, 3, 3]
def baseStart_320264 : Nat := 118140960795 + 320264 * 2 ^ 59
def prefixEnd_320264 : Nat := 4983230072969 + 3 ^ 40 * 320264 * 2
def baseEnd_320264 : Nat := 73088608147395644145395

theorem tailTrace_320264 : CollatzResearch.WordTrace tailWord_320264 prefixEnd_320264 73088608147395644145395 := by
  unfold tailWord_320264
  simp only [CollatzResearch.WordTrace]
  refine ⟨5840493855872849790839923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7787325141163799721119897 5840493855872849790839923)
  ·
    refine ⟨8760740783809274686259885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5840493855872849790839923 8760740783809274686259885)
    ·
      refine ⟨3285277793928478007347457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8760740783809274686259885 3285277793928478007347457)
      ·
        refine ⟨2463958345446358505510593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3285277793928478007347457 2463958345446358505510593)
        ·
          refine ⟨1847968759084768879132945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2463958345446358505510593 1847968759084768879132945)
          ·
            refine ⟨1385976569313576659349709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1847968759084768879132945 1385976569313576659349709)
            ·
              refine ⟨519741213492591247256141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1385976569313576659349709 519741213492591247256141)
              ·
                refine ⟨194902955059721717721053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 519741213492591247256141 194902955059721717721053)
                ·
                  refine ⟨73088608147395644145395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 194902955059721717721053 73088608147395644145395)
                  ·
                    rfl

theorem cell21_320264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 3, 3, 3].length) (baseStart_320264 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_320264 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_320264 prefixEnd_320264 := by exact prefixLift 320264
  have htrace : WordTrace (prefixWord ++ tailWord_320264) baseStart_320264 baseEnd_320264 := by
    simpa [prefixWord, tailWord_320264, baseEnd_320264] using wordTrace_append hprefix tailTrace_320264
  have hstable : (prefixWord ++ tailWord_320264).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_320264).length < 2 ^ (prefixWord ++ tailWord_320264).sum := by decide
  have hdescent : baseEnd_320264 < baseStart_320264 := by decide
  rcases family_descends (prefixWord ++ tailWord_320264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_320306 : List Nat := [3, 2, 1, 1, 3, 1, 2, 1, 7]
def baseStart_320306 : Nat := 118140960795 + 320306 * 2 ^ 59
def prefixEnd_320306 : Nat := 4983230072969 + 3 ^ 40 * 320306 * 2
def baseEnd_320306 : Nat := 73098193119612904445309

theorem tailTrace_320306 : CollatzResearch.WordTrace tailWord_320306 prefixEnd_320306 73098193119612904445309 := by
  unfold tailWord_320306
  simp only [CollatzResearch.WordTrace]
  refine ⟨2920629894398385188677193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7788346385062360503139181 2920629894398385188677193)
  ·
    refine ⟨2190472420798788891507895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2920629894398385188677193 2190472420798788891507895)
    ·
      refine ⟨3285708631198183337261843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2190472420798788891507895 3285708631198183337261843)
      ·
        refine ⟨4928562946797275005892765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3285708631198183337261843 4928562946797275005892765)
        ·
          refine ⟨1848211105048978127209787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4928562946797275005892765 1848211105048978127209787)
          ·
            refine ⟨2772316657573467190814681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1848211105048978127209787 2772316657573467190814681)
            ·
              refine ⟨2079237493180100393111011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2772316657573467190814681 2079237493180100393111011)
              ·
                refine ⟨3118856239770150589666517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2079237493180100393111011 3118856239770150589666517)
                ·
                  refine ⟨73098193119612904445309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3118856239770150589666517 73098193119612904445309)
                  ·
                    rfl

theorem cell21_320306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 2, 1, 7].length) (baseStart_320306 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_320306 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_320306 prefixEnd_320306 := by exact prefixLift 320306
  have htrace : WordTrace (prefixWord ++ tailWord_320306) baseStart_320306 baseEnd_320306 := by
    simpa [prefixWord, tailWord_320306, baseEnd_320306] using wordTrace_append hprefix tailTrace_320306
  have hstable : (prefixWord ++ tailWord_320306).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_320306).length < 2 ^ (prefixWord ++ tailWord_320306).sum := by decide
  have hdescent : baseEnd_320306 < baseStart_320306 := by decide
  rcases family_descends (prefixWord ++ tailWord_320306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_320320 : List Nat := [2, 1, 1, 2, 2, 1, 1, 3, 8]
def baseStart_320320 : Nat := 118140960795 + 320320 * 2 ^ 59
def prefixEnd_320320 : Nat := 4983230072969 + 3 ^ 40 * 320320 * 2
def baseEnd_320320 : Nat := 73101388110351991211947

theorem tailTrace_320320 : CollatzResearch.WordTrace tailWord_320320 prefixEnd_320320 73101388110351991211947 := by
  unfold tailWord_320320
  simp only [CollatzResearch.WordTrace]
  refine ⟨5841515099771410572859207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7788686799695214097145609 5841515099771410572859207)
  ·
    refine ⟨8762272649657115859288811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5841515099771410572859207 8762272649657115859288811)
    ·
      refine ⟨13143408974485673788933217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8762272649657115859288811 13143408974485673788933217)
      ·
        refine ⟨9857556730864255341699913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13143408974485673788933217 9857556730864255341699913)
        ·
          refine ⟨7393167548148191506274935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9857556730864255341699913 7393167548148191506274935)
          ·
            refine ⟨11089751322222287259412403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7393167548148191506274935 11089751322222287259412403)
            ·
              refine ⟨16634626983333430889118605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11089751322222287259412403 16634626983333430889118605)
              ·
                refine ⟨6237985118750036583419477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16634626983333430889118605 6237985118750036583419477)
                ·
                  refine ⟨73101388110351991211947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 6237985118750036583419477 73101388110351991211947)
                  ·
                    rfl

theorem cell21_320320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 3, 8].length) (baseStart_320320 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_320320 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_320320 prefixEnd_320320 := by exact prefixLift 320320
  have htrace : WordTrace (prefixWord ++ tailWord_320320) baseStart_320320 baseEnd_320320 := by
    simpa [prefixWord, tailWord_320320, baseEnd_320320] using wordTrace_append hprefix tailTrace_320320
  have hstable : (prefixWord ++ tailWord_320320).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_320320).length < 2 ^ (prefixWord ++ tailWord_320320).sum := by decide
  have hdescent : baseEnd_320320 < baseStart_320320 := by decide
  rcases family_descends (prefixWord ++ tailWord_320320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_320323 : List Nat := [1, 1, 1, 3, 1, 4, 2, 5, 3]
def baseStart_320323 : Nat := 118140960795 + 320323 * 2 ^ 59
def prefixEnd_320323 : Nat := 4983230072969 + 3 ^ 40 * 320323 * 2
def baseEnd_320323 : Nat := 73102072751224652661941

theorem tailTrace_320323 : CollatzResearch.WordTrace tailWord_320323 prefixEnd_320323 73102072751224652661941 := by
  unfold tailWord_320323
  simp only [CollatzResearch.WordTrace]
  refine ⟨11683139618531952658077623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7788759745687968438718415 11683139618531952658077623)
  ·
    refine ⟨17524709427797928987116435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11683139618531952658077623 17524709427797928987116435)
    ·
      refine ⟨26287064141696893480674653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17524709427797928987116435 26287064141696893480674653)
      ·
        refine ⟨9857649053136335055252995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26287064141696893480674653 9857649053136335055252995)
        ·
          refine ⟨14786473579704502582879493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9857649053136335055252995 14786473579704502582879493)
          ·
            refine ⟨2772463796194594234289905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14786473579704502582879493 2772463796194594234289905)
            ·
              refine ⟨2079347847145945675717429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2772463796194594234289905 2079347847145945675717429)
              ·
                refine ⟨194938860669932407098509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2079347847145945675717429 194938860669932407098509)
                ·
                  refine ⟨73102072751224652661941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 194938860669932407098509 73102072751224652661941)
                  ·
                    rfl

theorem cell21_320323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 2, 5, 3].length) (baseStart_320323 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_320323 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_320323 prefixEnd_320323 := by exact prefixLift 320323
  have htrace : WordTrace (prefixWord ++ tailWord_320323) baseStart_320323 baseEnd_320323 := by
    simpa [prefixWord, tailWord_320323, baseEnd_320323] using wordTrace_append hprefix tailTrace_320323
  have hstable : (prefixWord ++ tailWord_320323).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_320323).length < 2 ^ (prefixWord ++ tailWord_320323).sum := by decide
  have hdescent : baseEnd_320323 < baseStart_320323 := by decide
  rcases family_descends (prefixWord ++ tailWord_320323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_320326 : List Nat := [6, 1, 1, 2, 3, 8]
def baseStart_320326 : Nat := 118140960795 + 320326 * 2 ^ 59
def prefixEnd_320326 : Nat := 4983230072969 + 3 ^ 40 * 320326 * 2
def baseEnd_320326 : Nat := 2707509533040641263405

theorem tailTrace_320326 : CollatzResearch.WordTrace tailWord_320326 prefixEnd_320326 2707509533040641263405 := by
  unfold tailWord_320326
  simp only [CollatzResearch.WordTrace]
  refine ⟨365101532422533880326151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 7788832691680722780291221 365101532422533880326151)
  ·
    refine ⟨547652298633800820489227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 365101532422533880326151 547652298633800820489227)
    ·
      refine ⟨821478447950701230733841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 547652298633800820489227 821478447950701230733841)
      ·
        refine ⟨616108835963025923050381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 821478447950701230733841 616108835963025923050381)
        ·
          refine ⟨231040813486134721143893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 616108835963025923050381 231040813486134721143893)
          ·
            refine ⟨2707509533040641263405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 231040813486134721143893 2707509533040641263405)
            ·
              rfl

theorem cell21_320326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 3, 8].length) (baseStart_320326 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_320326 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_320326 prefixEnd_320326 := by exact prefixLift 320326
  have htrace : WordTrace (prefixWord ++ tailWord_320326) baseStart_320326 baseEnd_320326 := by
    simpa [prefixWord, tailWord_320326, baseEnd_320326] using wordTrace_append hprefix tailTrace_320326
  have hstable : (prefixWord ++ tailWord_320326).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_320326).length < 2 ^ (prefixWord ++ tailWord_320326).sum := by decide
  have hdescent : baseEnd_320326 < baseStart_320326 := by decide
  rcases family_descends (prefixWord ++ tailWord_320326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_320433 : List Nat := [1, 2, 2, 4, 3, 2, 1, 3, 3]
def baseStart_320433 : Nat := 118140960795 + 320433 * 2 ^ 59
def prefixEnd_320433 : Nat := 4983230072969 + 3 ^ 40 * 320433 * 2
def baseEnd_320433 : Nat := 73127176249888905828383

theorem tailTrace_320433 : CollatzResearch.WordTrace tailWord_320433 prefixEnd_320433 73127176249888905828383 := by
  unfold tailWord_320433
  simp only [CollatzResearch.WordTrace]
  refine ⟨11687151648133441444581953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7791434432088960963054635 11687151648133441444581953)
  ·
    refine ⟨8765363736100081083436465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11687151648133441444581953 8765363736100081083436465)
    ·
      refine ⟨6574022802075060812577349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8765363736100081083436465 6574022802075060812577349)
      ·
        refine ⟨1232629275389073902358253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6574022802075060812577349 1232629275389073902358253)
        ·
          refine ⟨462235978270902713384345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1232629275389073902358253 462235978270902713384345)
          ·
            refine ⟨346676983703177035038259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 462235978270902713384345 346676983703177035038259)
            ·
              refine ⟨520015475554765552557389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 346676983703177035038259 520015475554765552557389)
              ·
                refine ⟨195005803333037082209021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 520015475554765552557389 195005803333037082209021)
                ·
                  refine ⟨73127176249888905828383, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 195005803333037082209021 73127176249888905828383)
                  ·
                    rfl

theorem cell21_320433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 2, 1, 3, 3].length) (baseStart_320433 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_320433 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_320433 prefixEnd_320433 := by exact prefixLift 320433
  have htrace : WordTrace (prefixWord ++ tailWord_320433) baseStart_320433 baseEnd_320433 := by
    simpa [prefixWord, tailWord_320433, baseEnd_320433] using wordTrace_append hprefix tailTrace_320433
  have hstable : (prefixWord ++ tailWord_320433).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_320433).length < 2 ^ (prefixWord ++ tailWord_320433).sum := by decide
  have hdescent : baseEnd_320433 < baseStart_320433 := by decide
  rcases family_descends (prefixWord ++ tailWord_320433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_320520 : List Nat := [2, 1, 3, 2, 1, 5, 1, 6]
def baseStart_320520 : Nat := 118140960795 + 320520 * 2 ^ 59
def prefixEnd_320520 : Nat := 4983230072969 + 3 ^ 40 * 320520 * 2
def baseEnd_320520 : Nat := 24382343611732029292735

theorem tailTrace_320520 : CollatzResearch.WordTrace tailWord_320520 prefixEnd_320520 24382343611732029292735 := by
  unfold tailWord_320520
  simp only [CollatzResearch.WordTrace]
  refine ⟨5845162399409127651499507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7793549865878836868666009 5845162399409127651499507)
  ·
    refine ⟨8767743599113691477249261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5845162399409127651499507 8767743599113691477249261)
    ·
      refine ⟨3287903849667634303968473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8767743599113691477249261 3287903849667634303968473)
      ·
        refine ⟨2465927887250725727976355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3287903849667634303968473 2465927887250725727976355)
        ·
          refine ⟨3698891830876088591964533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2465927887250725727976355 3698891830876088591964533)
          ·
            refine ⟨346771109144633305496675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 3698891830876088591964533 346771109144633305496675)
            ·
              refine ⟨520156663716949958245013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 346771109144633305496675 520156663716949958245013)
              ·
                refine ⟨24382343611732029292735, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 520156663716949958245013 24382343611732029292735)
                ·
                  rfl

theorem cell21_320520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 5, 1, 6].length) (baseStart_320520 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_320520 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_320520 prefixEnd_320520 := by exact prefixLift 320520
  have htrace : WordTrace (prefixWord ++ tailWord_320520) baseStart_320520 baseEnd_320520 := by
    simpa [prefixWord, tailWord_320520, baseEnd_320520] using wordTrace_append hprefix tailTrace_320520
  have hstable : (prefixWord ++ tailWord_320520).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_320520).length < 2 ^ (prefixWord ++ tailWord_320520).sum := by decide
  have hdescent : baseEnd_320520 < baseStart_320520 := by decide
  rcases family_descends (prefixWord ++ tailWord_320520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_320596 : List Nat := [2, 4, 1, 1, 1, 1, 6, 5]
def baseStart_320596 : Nat := 118140960795 + 320596 * 2 ^ 59
def prefixEnd_320596 : Nat := 4983230072969 + 3 ^ 40 * 320596 * 2
def baseEnd_320596 : Nat := 24388125023545614870461

theorem tailTrace_320596 : CollatzResearch.WordTrace tailWord_320596 prefixEnd_320596 24388125023545614870461 := by
  unfold tailWord_320596
  simp only [CollatzResearch.WordTrace]
  refine ⟨5846548373271460141382821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7795397831028613521843761 5846548373271460141382821)
  ·
    refine ⟨1096227819988398776509279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5846548373271460141382821 1096227819988398776509279)
    ·
      refine ⟨1644341729982598164763919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1096227819988398776509279 1644341729982598164763919)
      ·
        refine ⟨2466512594973897247145879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1644341729982598164763919 2466512594973897247145879)
        ·
          refine ⟨3699768892460845870718819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2466512594973897247145879 3699768892460845870718819)
          ·
            refine ⟨5549653338691268806078229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3699768892460845870718819 5549653338691268806078229)
            ·
              refine ⟨260140000251153225284917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 5549653338691268806078229 260140000251153225284917)
              ·
                refine ⟨24388125023545614870461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 260140000251153225284917 24388125023545614870461)
                ·
                  rfl

theorem cell21_320596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 6, 5].length) (baseStart_320596 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_320596 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_320596 prefixEnd_320596 := by exact prefixLift 320596
  have htrace : WordTrace (prefixWord ++ tailWord_320596) baseStart_320596 baseEnd_320596 := by
    simpa [prefixWord, tailWord_320596, baseEnd_320596] using wordTrace_append hprefix tailTrace_320596
  have hstable : (prefixWord ++ tailWord_320596).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_320596).length < 2 ^ (prefixWord ++ tailWord_320596).sum := by decide
  have hdescent : baseEnd_320596 < baseStart_320596 := by decide
  rcases family_descends (prefixWord ++ tailWord_320596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_320624 : List Nat := [2, 1, 1, 1, 5, 1, 1, 3, 6]
def baseStart_320624 : Nat := 118140960795 + 320624 * 2 ^ 59
def prefixEnd_320624 : Nat := 4983230072969 + 3 ^ 40 * 320624 * 2
def baseEnd_320624 : Nat := 73170765052115018144659

theorem tailTrace_320624 : CollatzResearch.WordTrace tailWord_320624 prefixEnd_320624 73170765052115018144659 := by
  unfold tailWord_320624
  simp only [CollatzResearch.WordTrace]
  refine ⟨5847058995220740532392463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7796078660294320709856617 5847058995220740532392463)
  ·
    refine ⟨8770588492831110798588695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5847058995220740532392463 8770588492831110798588695)
    ·
      refine ⟨13155882739246666197883043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8770588492831110798588695 13155882739246666197883043)
      ·
        refine ⟨19733824108869999296824565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13155882739246666197883043 19733824108869999296824565)
        ·
          refine ⟨1850046010206562434077303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 19733824108869999296824565 1850046010206562434077303)
          ·
            refine ⟨2775069015309843651115955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1850046010206562434077303 2775069015309843651115955)
            ·
              refine ⟨4162603522964765476673933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2775069015309843651115955 4162603522964765476673933)
              ·
                refine ⟨1560976321111787053752725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4162603522964765476673933 1560976321111787053752725)
                ·
                  refine ⟨73170765052115018144659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1560976321111787053752725 73170765052115018144659)
                  ·
                    rfl

theorem cell21_320624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 1, 3, 6].length) (baseStart_320624 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_320624 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_320624 prefixEnd_320624 := by exact prefixLift 320624
  have htrace : WordTrace (prefixWord ++ tailWord_320624) baseStart_320624 baseEnd_320624 := by
    simpa [prefixWord, tailWord_320624, baseEnd_320624] using wordTrace_append hprefix tailTrace_320624
  have hstable : (prefixWord ++ tailWord_320624).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_320624).length < 2 ^ (prefixWord ++ tailWord_320624).sum := by decide
  have hdescent : baseEnd_320624 < baseStart_320624 := by decide
  rcases family_descends (prefixWord ++ tailWord_320624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_320779 : List Nat := [1, 1, 1, 1, 5, 3, 3, 3, 3]
def baseStart_320779 : Nat := 118140960795 + 320779 * 2 ^ 59
def prefixEnd_320779 : Nat := 4983230072969 + 3 ^ 40 * 320779 * 2
def baseEnd_320779 : Nat := 73206138163869193061009

theorem tailTrace_320779 : CollatzResearch.WordTrace tailWord_320779 prefixEnd_320779 73206138163869193061009 := by
  unfold tailWord_320779
  simp only [CollatzResearch.WordTrace]
  refine ⟨11699771304879942536677391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7799847536586628357784927 11699771304879942536677391)
  ·
    refine ⟨17549656957319913805016087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11699771304879942536677391 17549656957319913805016087)
    ·
      refine ⟨26324485435979870707524131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17549656957319913805016087 26324485435979870707524131)
      ·
        refine ⟨39486728153969806061286197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26324485435979870707524131 39486728153969806061286197)
        ·
          refine ⟨3701880764434669318245581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 39486728153969806061286197 3701880764434669318245581)
          ·
            refine ⟨1388205286663000994342093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3701880764434669318245581 1388205286663000994342093)
            ·
              refine ⟨520576982498625372878285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1388205286663000994342093 520576982498625372878285)
              ·
                refine ⟨195216368436984514829357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 520576982498625372878285 195216368436984514829357)
                ·
                  refine ⟨73206138163869193061009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 195216368436984514829357 73206138163869193061009)
                  ·
                    rfl

theorem cell21_320779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 3, 3, 3].length) (baseStart_320779 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_320779 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_320779 prefixEnd_320779 := by exact prefixLift 320779
  have htrace : WordTrace (prefixWord ++ tailWord_320779) baseStart_320779 baseEnd_320779 := by
    simpa [prefixWord, tailWord_320779, baseEnd_320779] using wordTrace_append hprefix tailTrace_320779
  have hstable : (prefixWord ++ tailWord_320779).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_320779).length < 2 ^ (prefixWord ++ tailWord_320779).sum := by decide
  have hdescent : baseEnd_320779 < baseStart_320779 := by decide
  rcases family_descends (prefixWord ++ tailWord_320779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_320810 : List Nat := [3, 1, 4, 2, 1, 2, 1, 3, 4]
def baseStart_320810 : Nat := 118140960795 + 320810 * 2 ^ 59
def prefixEnd_320810 : Nat := 4983230072969 + 3 ^ 40 * 320810 * 2
def baseEnd_320810 : Nat := 73213212786220028044279

theorem tailTrace_320810 : CollatzResearch.WordTrace tailWord_320810 prefixEnd_320810 73213212786220028044279 := by
  unfold tailWord_320810
  simp only [CollatzResearch.WordTrace]
  refine ⟨2925225491941908707763971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7800601311845089887370589 2925225491941908707763971)
  ·
    refine ⟨4387838237912863061645957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2925225491941908707763971 4387838237912863061645957)
    ·
      refine ⟨822719669608661824058617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4387838237912863061645957 822719669608661824058617)
      ·
        refine ⟨617039752206496368043963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 822719669608661824058617 617039752206496368043963)
        ·
          refine ⟨925559628309744552065945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 617039752206496368043963 925559628309744552065945)
          ·
            refine ⟨694169721232308414049459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 925559628309744552065945 694169721232308414049459)
            ·
              refine ⟨1041254581848462621074189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 694169721232308414049459 1041254581848462621074189)
              ·
                refine ⟨390470468193173482902821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1041254581848462621074189 390470468193173482902821)
                ·
                  refine ⟨73213212786220028044279, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 390470468193173482902821 73213212786220028044279)
                  ·
                    rfl

theorem cell21_320810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 2, 1, 3, 4].length) (baseStart_320810 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_320810 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_320810 prefixEnd_320810 := by exact prefixLift 320810
  have htrace : WordTrace (prefixWord ++ tailWord_320810) baseStart_320810 baseEnd_320810 := by
    simpa [prefixWord, tailWord_320810, baseEnd_320810] using wordTrace_append hprefix tailTrace_320810
  have hstable : (prefixWord ++ tailWord_320810).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_320810).length < 2 ^ (prefixWord ++ tailWord_320810).sum := by decide
  have hdescent : baseEnd_320810 < baseStart_320810 := by decide
  rcases family_descends (prefixWord ++ tailWord_320810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_320855 : List Nat := [1, 1, 3, 2, 3, 3, 1, 4, 3]
def baseStart_320855 : Nat := 118140960795 + 320855 * 2 ^ 59
def prefixEnd_320855 : Nat := 4983230072969 + 3 ^ 40 * 320855 * 2
def baseEnd_320855 : Nat := 73223482399309949794187

theorem tailTrace_320855 : CollatzResearch.WordTrace tailWord_320855 prefixEnd_320855 73223482399309949794187 := by
  unfold tailWord_320855
  simp only [CollatzResearch.WordTrace]
  refine ⟨11702543252604607516444019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7801695501736405010962679 11702543252604607516444019)
  ·
    refine ⟨17553814878906911274666029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11702543252604607516444019 17553814878906911274666029)
    ·
      refine ⟨6582680579590091727999761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17553814878906911274666029 6582680579590091727999761)
      ·
        refine ⟨4937010434692568795999821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6582680579590091727999761 4937010434692568795999821)
        ·
          refine ⟨1851378913009713298499933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4937010434692568795999821 1851378913009713298499933)
          ·
            refine ⟨694267092378642486937475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1851378913009713298499933 694267092378642486937475)
            ·
              refine ⟨1041400638567963730406213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 694267092378642486937475 1041400638567963730406213)
              ·
                refine ⟨195262619731493199451165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1041400638567963730406213 195262619731493199451165)
                ·
                  refine ⟨73223482399309949794187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 195262619731493199451165 73223482399309949794187)
                  ·
                    rfl

theorem cell21_320855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 3, 1, 4, 3].length) (baseStart_320855 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_320855 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_320855 prefixEnd_320855 := by exact prefixLift 320855
  have htrace : WordTrace (prefixWord ++ tailWord_320855) baseStart_320855 baseEnd_320855 := by
    simpa [prefixWord, tailWord_320855, baseEnd_320855] using wordTrace_append hprefix tailTrace_320855
  have hstable : (prefixWord ++ tailWord_320855).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_320855).length < 2 ^ (prefixWord ++ tailWord_320855).sum := by decide
  have hdescent : baseEnd_320855 < baseStart_320855 := by decide
  rcases family_descends (prefixWord ++ tailWord_320855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_321021 : List Nat := [1, 4, 1, 1, 1, 5, 2, 2, 4]
def baseStart_321021 : Nat := 118140960795 + 321021 * 2 ^ 59
def prefixEnd_321021 : Nat := 4983230072969 + 3 ^ 40 * 321021 * 2
def baseEnd_321021 : Nat := 73261365860930550027181

theorem tailTrace_321021 : CollatzResearch.WordTrace tailWord_321021 prefixEnd_321021 73261365860930550027181 := by
  unfold tailWord_321021
  simp only [CollatzResearch.WordTrace]
  refine ⟨11708597770003217866986917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7805731846668811911324611 11708597770003217866986917)
  ·
    refine ⟨2195362081875603350060047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11708597770003217866986917 2195362081875603350060047)
    ·
      refine ⟨3293043122813405025090071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2195362081875603350060047 3293043122813405025090071)
      ·
        refine ⟨4939564684220107537635107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3293043122813405025090071 4939564684220107537635107)
        ·
          refine ⟨7409347026330161306452661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4939564684220107537635107 7409347026330161306452661)
          ·
            refine ⟨694626283718452622479937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 7409347026330161306452661 694626283718452622479937)
            ·
              refine ⟨520969712788839466859953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 694626283718452622479937 520969712788839466859953)
              ·
                refine ⟨390727284591629600144965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 520969712788839466859953 390727284591629600144965)
                ·
                  refine ⟨73261365860930550027181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 390727284591629600144965 73261365860930550027181)
                  ·
                    rfl

theorem cell21_321021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 5, 2, 2, 4].length) (baseStart_321021 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_321021 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_321021 prefixEnd_321021 := by exact prefixLift 321021
  have htrace : WordTrace (prefixWord ++ tailWord_321021) baseStart_321021 baseEnd_321021 := by
    simpa [prefixWord, tailWord_321021, baseEnd_321021] using wordTrace_append hprefix tailTrace_321021
  have hstable : (prefixWord ++ tailWord_321021).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_321021).length < 2 ^ (prefixWord ++ tailWord_321021).sum := by decide
  have hdescent : baseEnd_321021 < baseStart_321021 := by decide
  rcases family_descends (prefixWord ++ tailWord_321021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_321080 : List Nat := [2, 1, 2, 1, 4, 3, 1, 1, 6]
def baseStart_321080 : Nat := 118140960795 + 321080 * 2 ^ 59
def prefixEnd_321080 : Nat := 4983230072969 + 3 ^ 40 * 321080 * 2
def baseEnd_321080 : Nat := 73274830464759558543727

theorem tailTrace_321080 : CollatzResearch.WordTrace tailWord_321080 prefixEnd_321080 73274830464759558543727 := by
  unfold tailWord_321080
  simp only [CollatzResearch.WordTrace]
  refine ⟨5855374838394735471692347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7807166451192980628923129 5855374838394735471692347)
  ·
    refine ⟨8783062257592103207538521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5855374838394735471692347 8783062257592103207538521)
    ·
      refine ⟨6587296693194077405653891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8783062257592103207538521 6587296693194077405653891)
      ·
        refine ⟨9880945039791116108480837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6587296693194077405653891 9880945039791116108480837)
        ·
          refine ⟨1852677194960834270340157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9880945039791116108480837 1852677194960834270340157)
          ·
            refine ⟨694753948110312851377559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1852677194960834270340157 694753948110312851377559)
            ·
              refine ⟨1042130922165469277066339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 694753948110312851377559 1042130922165469277066339)
              ·
                refine ⟨1563196383248203915599509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1042130922165469277066339 1563196383248203915599509)
                ·
                  refine ⟨73274830464759558543727, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1563196383248203915599509 73274830464759558543727)
                  ·
                    rfl

theorem cell21_321080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 3, 1, 1, 6].length) (baseStart_321080 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_321080 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_321080 prefixEnd_321080 := by exact prefixLift 321080
  have htrace : WordTrace (prefixWord ++ tailWord_321080) baseStart_321080 baseEnd_321080 := by
    simpa [prefixWord, tailWord_321080, baseEnd_321080] using wordTrace_append hprefix tailTrace_321080
  have hstable : (prefixWord ++ tailWord_321080).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_321080).length < 2 ^ (prefixWord ++ tailWord_321080).sum := by decide
  have hdescent : baseEnd_321080 < baseStart_321080 := by decide
  rcases family_descends (prefixWord ++ tailWord_321080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_321111 : List Nat := [1, 1, 3, 2, 2, 3, 4, 5]
def baseStart_321111 : Nat := 118140960795 + 321111 * 2 ^ 59
def prefixEnd_321111 : Nat := 4983230072969 + 3 ^ 40 * 321111 * 2
def baseEnd_321111 : Nat := 24427301695703464508999

theorem tailTrace_321111 : CollatzResearch.WordTrace tailWord_321111 prefixEnd_321111 24427301695703464508999 := by
  unfold tailWord_321111
  simp only [CollatzResearch.WordTrace]
  refine ⟨11711880339677163237763187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7807920226451442158508791 11711880339677163237763187)
  ·
    refine ⟨17567820509515744856644781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11711880339677163237763187 17567820509515744856644781)
    ·
      refine ⟨6587932691068404321241793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17567820509515744856644781 6587932691068404321241793)
      ·
        refine ⟨4940949518301303240931345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6587932691068404321241793 4940949518301303240931345)
        ·
          refine ⟨3705712138725977430698509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4940949518301303240931345 3705712138725977430698509)
          ·
            refine ⟨1389642052022241536511941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3705712138725977430698509 1389642052022241536511941)
            ·
              refine ⟨260557884754170288095989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1389642052022241536511941 260557884754170288095989)
              ·
                refine ⟨24427301695703464508999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 260557884754170288095989 24427301695703464508999)
                ·
                  rfl

theorem cell21_321111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 4, 5].length) (baseStart_321111 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_321111 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_321111 prefixEnd_321111 := by exact prefixLift 321111
  have htrace : WordTrace (prefixWord ++ tailWord_321111) baseStart_321111 baseEnd_321111 := by
    simpa [prefixWord, tailWord_321111, baseEnd_321111] using wordTrace_append hprefix tailTrace_321111
  have hstable : (prefixWord ++ tailWord_321111).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_321111).length < 2 ^ (prefixWord ++ tailWord_321111).sum := by decide
  have hdescent : baseEnd_321111 < baseStart_321111 := by decide
  rcases family_descends (prefixWord ++ tailWord_321111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_321291 : List Nat := [1, 1, 1, 1, 5, 1, 3, 2, 6]
def baseStart_321291 : Nat := 118140960795 + 321291 * 2 ^ 59
def prefixEnd_321291 : Nat := 4983230072969 + 3 ^ 40 * 321291 * 2
def baseEnd_321291 : Nat := 73322983539470080526629

theorem tailTrace_321291 : CollatzResearch.WordTrace tailWord_321291 prefixEnd_321291 73322983539470080526629 := by
  unfold tailWord_321291
  simp only [CollatzResearch.WordTrace]
  refine ⟨11718445479025053979315727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7812296986016702652877151 11718445479025053979315727)
  ·
    refine ⟨17577668218537580968973591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11718445479025053979315727 17577668218537580968973591)
    ·
      refine ⟨26366502327806371453460387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17577668218537580968973591 26366502327806371453460387)
      ·
        refine ⟨39549753491709557180190581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26366502327806371453460387 39549753491709557180190581)
        ·
          refine ⟨3707789389847770985642867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 39549753491709557180190581 3707789389847770985642867)
          ·
            refine ⟨5561684084771656478464301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3707789389847770985642867 5561684084771656478464301)
            ·
              refine ⟨2085631531789371179424113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5561684084771656478464301 2085631531789371179424113)
              ·
                refine ⟨1564223648842028384568085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2085631531789371179424113 1564223648842028384568085)
                ·
                  refine ⟨73322983539470080526629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1564223648842028384568085 73322983539470080526629)
                  ·
                    rfl

theorem cell21_321291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 3, 2, 6].length) (baseStart_321291 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_321291 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_321291 prefixEnd_321291 := by exact prefixLift 321291
  have htrace : WordTrace (prefixWord ++ tailWord_321291) baseStart_321291 baseEnd_321291 := by
    simpa [prefixWord, tailWord_321291, baseEnd_321291] using wordTrace_append hprefix tailTrace_321291
  have hstable : (prefixWord ++ tailWord_321291).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_321291).length < 2 ^ (prefixWord ++ tailWord_321291).sum := by decide
  have hdescent : baseEnd_321291 < baseStart_321291 := by decide
  rcases family_descends (prefixWord ++ tailWord_321291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_321308 : List Nat := [2, 2, 3, 1, 1, 2, 2, 4, 4]
def baseStart_321308 : Nat := 118140960795 + 321308 * 2 ^ 59
def prefixEnd_321308 : Nat := 4983230072969 + 3 ^ 40 * 321308 * 2
def baseEnd_321308 : Nat := 73326863171081828743261

theorem tailTrace_321308 : CollatzResearch.WordTrace tailWord_321308 prefixEnd_321308 73326863171081828743261 := by
  unfold tailWord_321308
  simp only [CollatzResearch.WordTrace]
  refine ⟨5859532759981732941342289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7812710346642310588456385 5859532759981732941342289)
  ·
    refine ⟨4394649569986299706006717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5859532759981732941342289 4394649569986299706006717)
    ·
      refine ⟨1647993588744862389752519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4394649569986299706006717 1647993588744862389752519)
      ·
        refine ⟨2471990383117293584628779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1647993588744862389752519 2471990383117293584628779)
        ·
          refine ⟨3707985574675940376943169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2471990383117293584628779 3707985574675940376943169)
          ·
            refine ⟨2780989181006955282707377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3707985574675940376943169 2780989181006955282707377)
            ·
              refine ⟨2085741885755216462030533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2780989181006955282707377 2085741885755216462030533)
              ·
                refine ⟨391076603579103086630725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2085741885755216462030533 391076603579103086630725)
                ·
                  refine ⟨73326863171081828743261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 391076603579103086630725 73326863171081828743261)
                  ·
                    rfl

theorem cell21_321308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 2, 4, 4].length) (baseStart_321308 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_321308 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_321308 prefixEnd_321308 := by exact prefixLift 321308
  have htrace : WordTrace (prefixWord ++ tailWord_321308) baseStart_321308 baseEnd_321308 := by
    simpa [prefixWord, tailWord_321308, baseEnd_321308] using wordTrace_append hprefix tailTrace_321308
  have hstable : (prefixWord ++ tailWord_321308).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_321308).length < 2 ^ (prefixWord ++ tailWord_321308).sum := by decide
  have hdescent : baseEnd_321308 < baseStart_321308 := by decide
  rcases family_descends (prefixWord ++ tailWord_321308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_321311 : List Nat := [1, 1, 2, 4, 2, 1, 5, 2, 3]
def baseStart_321311 : Nat := 118140960795 + 321311 * 2 ^ 59
def prefixEnd_321311 : Nat := 4983230072969 + 3 ^ 40 * 321311 * 2
def baseEnd_321311 : Nat := 73327547811954490193255

theorem tailTrace_321311 : CollatzResearch.WordTrace tailWord_321311 prefixEnd_321311 73327547811954490193255 := by
  unfold tailWord_321311
  simp only [CollatzResearch.WordTrace]
  refine ⟨11719174938952597395043787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7812783292635064930029191 11719174938952597395043787)
  ·
    refine ⟨17578762408428896092565681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11719174938952597395043787 17578762408428896092565681)
    ·
      refine ⟨13184071806321672069424261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17578762408428896092565681 13184071806321672069424261)
      ·
        refine ⟨2472013463685313513017049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13184071806321672069424261 2472013463685313513017049)
        ·
          refine ⟨1854010097763985134762787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2472013463685313513017049 1854010097763985134762787)
          ·
            refine ⟨2781015146645977702144181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1854010097763985134762787 2781015146645977702144181)
            ·
              refine ⟨260720169998060409576017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2781015146645977702144181 260720169998060409576017)
              ·
                refine ⟨195540127498545307182013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 260720169998060409576017 195540127498545307182013)
                ·
                  refine ⟨73327547811954490193255, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 195540127498545307182013 73327547811954490193255)
                  ·
                    rfl

theorem cell21_321311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 5, 2, 3].length) (baseStart_321311 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_321311 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_321311 prefixEnd_321311 := by exact prefixLift 321311
  have htrace : WordTrace (prefixWord ++ tailWord_321311) baseStart_321311 baseEnd_321311 := by
    simpa [prefixWord, tailWord_321311, baseEnd_321311] using wordTrace_append hprefix tailTrace_321311
  have hstable : (prefixWord ++ tailWord_321311).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_321311).length < 2 ^ (prefixWord ++ tailWord_321311).sum := by decide
  have hdescent : baseEnd_321311 < baseStart_321311 := by decide
  rcases family_descends (prefixWord ++ tailWord_321311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_321370 : List Nat := [3, 1, 1, 2, 1, 3, 3, 4, 3]
def baseStart_321370 : Nat := 118140960795 + 321370 * 2 ^ 59
def prefixEnd_321370 : Nat := 4983230072969 + 3 ^ 40 * 321370 * 2
def baseEnd_321370 : Nat := 73341012415783498709801

theorem tailTrace_321370 : CollatzResearch.WordTrace tailWord_321370 prefixEnd_321370 73341012415783498709801 := by
  unfold tailWord_321370
  simp only [CollatzResearch.WordTrace]
  refine ⟨2930331711434712617860391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7814217897159233647627709 2930331711434712617860391)
  ·
    refine ⟨4395497567152068926790587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2930331711434712617860391 4395497567152068926790587)
    ·
      refine ⟨6593246350728103390185881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4395497567152068926790587 6593246350728103390185881)
      ·
        refine ⟨4944934763046077542639411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6593246350728103390185881 4944934763046077542639411)
        ·
          refine ⟨7417402144569116313959117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4944934763046077542639411 7417402144569116313959117)
          ·
            refine ⟨2781525804213418617734669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7417402144569116313959117 2781525804213418617734669)
            ·
              refine ⟨1043072176580031981650501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2781525804213418617734669 1043072176580031981650501)
              ·
                refine ⟨195576033108755996559469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1043072176580031981650501 195576033108755996559469)
                ·
                  refine ⟨73341012415783498709801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 195576033108755996559469 73341012415783498709801)
                  ·
                    rfl

theorem cell21_321370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 3, 4, 3].length) (baseStart_321370 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_321370 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_321370 prefixEnd_321370 := by exact prefixLift 321370
  have htrace : WordTrace (prefixWord ++ tailWord_321370) baseStart_321370 baseEnd_321370 := by
    simpa [prefixWord, tailWord_321370, baseEnd_321370] using wordTrace_append hprefix tailTrace_321370
  have hstable : (prefixWord ++ tailWord_321370).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_321370).length < 2 ^ (prefixWord ++ tailWord_321370).sum := by decide
  have hdescent : baseEnd_321370 < baseStart_321370 := by decide
  rcases family_descends (prefixWord ++ tailWord_321370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_321384 : List Nat := [2, 1, 4, 2, 1, 1, 1, 5, 4]
def baseStart_321384 : Nat := 118140960795 + 321384 * 2 ^ 59
def prefixEnd_321384 : Nat := 4983230072969 + 3 ^ 40 * 321384 * 2
def baseEnd_321384 : Nat := 73344207406522585476439

theorem tailTrace_321384 : CollatzResearch.WordTrace tailWord_321384 prefixEnd_321384 73344207406522585476439 := by
  unfold tailWord_321384
  simp only [CollatzResearch.WordTrace]
  refine ⟨5860918733844065431225603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7814558311792087241634137 5860918733844065431225603)
  ·
    refine ⟨8791378100766098146838405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5860918733844065431225603 8791378100766098146838405)
    ·
      refine ⟨1648383393893643402532201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8791378100766098146838405 1648383393893643402532201)
      ·
        refine ⟨1236287545420232551899151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1648383393893643402532201 1236287545420232551899151)
        ·
          refine ⟨1854431318130348827848727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1236287545420232551899151 1854431318130348827848727)
          ·
            refine ⟨2781646977195523241773091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1854431318130348827848727 2781646977195523241773091)
            ·
              refine ⟨4172470465793284862659637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2781646977195523241773091 4172470465793284862659637)
              ·
                refine ⟨391169106168120455874341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4172470465793284862659637 391169106168120455874341)
                ·
                  refine ⟨73344207406522585476439, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 391169106168120455874341 73344207406522585476439)
                  ·
                    rfl

theorem cell21_321384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 1, 5, 4].length) (baseStart_321384 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_321384 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_321384 prefixEnd_321384 := by exact prefixLift 321384
  have htrace : WordTrace (prefixWord ++ tailWord_321384) baseStart_321384 baseEnd_321384 := by
    simpa [prefixWord, tailWord_321384, baseEnd_321384] using wordTrace_append hprefix tailTrace_321384
  have hstable : (prefixWord ++ tailWord_321384).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_321384).length < 2 ^ (prefixWord ++ tailWord_321384).sum := by decide
  have hdescent : baseEnd_321384 < baseStart_321384 := by decide
  rcases family_descends (prefixWord ++ tailWord_321384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_321418 : List Nat := [3, 1, 2, 4, 2, 2, 1, 2, 4]
def baseStart_321418 : Nat := 118140960795 + 321418 * 2 ^ 59
def prefixEnd_321418 : Nat := 4983230072969 + 3 ^ 40 * 321418 * 2
def baseEnd_321418 : Nat := 73351966669746081909703

theorem tailTrace_321418 : CollatzResearch.WordTrace tailWord_321418 prefixEnd_321418 73351966669746081909703 := by
  unfold tailWord_321418
  simp only [CollatzResearch.WordTrace]
  refine ⟨2930769387391238667297227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7815385033043303112792605 2930769387391238667297227)
  ·
    refine ⟨4396154081086858000945841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2930769387391238667297227 4396154081086858000945841)
    ·
      refine ⟨3297115560815143500709381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4396154081086858000945841 3297115560815143500709381)
      ·
        refine ⟨618209167652839406383009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3297115560815143500709381 618209167652839406383009)
        ·
          refine ⟨463656875739629554787257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 618209167652839406383009 463656875739629554787257)
          ·
            refine ⟨347742656804722166090443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 463656875739629554787257 347742656804722166090443)
            ·
              refine ⟨521613985207083249135665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 347742656804722166090443 521613985207083249135665)
              ·
                refine ⟨391210488905312436851749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 521613985207083249135665 391210488905312436851749)
                ·
                  refine ⟨73351966669746081909703, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 391210488905312436851749 73351966669746081909703)
                  ·
                    rfl

theorem cell21_321418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 2, 1, 2, 4].length) (baseStart_321418 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_321418 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_321418 prefixEnd_321418 := by exact prefixLift 321418
  have htrace : WordTrace (prefixWord ++ tailWord_321418) baseStart_321418 baseEnd_321418 := by
    simpa [prefixWord, tailWord_321418, baseEnd_321418] using wordTrace_append hprefix tailTrace_321418
  have hstable : (prefixWord ++ tailWord_321418).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_321418).length < 2 ^ (prefixWord ++ tailWord_321418).sum := by decide
  have hdescent : baseEnd_321418 < baseStart_321418 := by decide
  rcases family_descends (prefixWord ++ tailWord_321418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_321429 : List Nat := [1, 3, 2, 1, 1, 3, 4, 1, 5]
def baseStart_321429 : Nat := 118140960795 + 321429 * 2 ^ 59
def prefixEnd_321429 : Nat := 4983230072969 + 3 ^ 40 * 321429 * 2
def baseEnd_321429 : Nat := 73354477019612507226347

theorem tailTrace_321429 : CollatzResearch.WordTrace tailWord_321429 prefixEnd_321429 73354477019612507226347 := by
  unfold tailWord_321429
  simp only [CollatzResearch.WordTrace]
  refine ⟨11723478752525103547839341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7815652501683402365226227 11723478752525103547839341)
  ·
    refine ⟨4396304532196913830439753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11723478752525103547839341 4396304532196913830439753)
    ·
      refine ⟨3297228399147685372829815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4396304532196913830439753 3297228399147685372829815)
      ·
        refine ⟨4945842598721528059244723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3297228399147685372829815 4945842598721528059244723)
        ·
          refine ⟨7418763898082292088867085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4945842598721528059244723 7418763898082292088867085)
          ·
            refine ⟨2782036461780859533325157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7418763898082292088867085 2782036461780859533325157)
            ·
              refine ⟨521631836583911162498467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2782036461780859533325157 521631836583911162498467)
              ·
                refine ⟨782447754875866743747701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 521631836583911162498467 782447754875866743747701)
                ·
                  refine ⟨73354477019612507226347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 782447754875866743747701 73354477019612507226347)
                  ·
                    rfl

theorem cell21_321429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 4, 1, 5].length) (baseStart_321429 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_321429 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_321429 prefixEnd_321429 := by exact prefixLift 321429
  have htrace : WordTrace (prefixWord ++ tailWord_321429) baseStart_321429 baseEnd_321429 := by
    simpa [prefixWord, tailWord_321429, baseEnd_321429] using wordTrace_append hprefix tailTrace_321429
  have hstable : (prefixWord ++ tailWord_321429).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_321429).length < 2 ^ (prefixWord ++ tailWord_321429).sum := by decide
  have hdescent : baseEnd_321429 < baseStart_321429 := by decide
  rcases family_descends (prefixWord ++ tailWord_321429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_321494 : List Nat := [5, 2, 1, 1, 3, 1, 1, 3, 4]
def baseStart_321494 : Nat := 118140960795 + 321494 * 2 ^ 59
def prefixEnd_321494 : Nat := 4983230072969 + 3 ^ 40 * 321494 * 2
def baseEnd_321494 : Nat := 73369310905186838642881

theorem tailTrace_321494 : CollatzResearch.WordTrace tailWord_321494 prefixEnd_321494 73369310905186838642881 := by
  unfold tailWord_321494
  simp only [CollatzResearch.WordTrace]
  refine ⟨732865593580601228059721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 7817232998193079765970357 732865593580601228059721)
  ·
    refine ⟨549649195185450921044791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 732865593580601228059721 549649195185450921044791)
    ·
      refine ⟨824473792778176381567187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 549649195185450921044791 824473792778176381567187)
      ·
        refine ⟨1236710689167264572350781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 824473792778176381567187 1236710689167264572350781)
        ·
          refine ⟨463766508437724214631543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1236710689167264572350781 463766508437724214631543)
          ·
            refine ⟨695649762656586321947315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 463766508437724214631543 695649762656586321947315)
            ·
              refine ⟨1043474643984879482920973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 695649762656586321947315 1043474643984879482920973)
              ·
                refine ⟨391302991494329806095365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1043474643984879482920973 391302991494329806095365)
                ·
                  refine ⟨73369310905186838642881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 391302991494329806095365 73369310905186838642881)
                  ·
                    rfl

theorem cell21_321494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 1, 1, 3, 4].length) (baseStart_321494 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_321494 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_321494 prefixEnd_321494 := by exact prefixLift 321494
  have htrace : WordTrace (prefixWord ++ tailWord_321494) baseStart_321494 baseEnd_321494 := by
    simpa [prefixWord, tailWord_321494, baseEnd_321494] using wordTrace_append hprefix tailTrace_321494
  have hstable : (prefixWord ++ tailWord_321494).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_321494).length < 2 ^ (prefixWord ++ tailWord_321494).sum := by decide
  have hdescent : baseEnd_321494 < baseStart_321494 := by decide
  rcases family_descends (prefixWord ++ tailWord_321494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_321609 : List Nat := [1, 2, 1, 1, 2, 2, 4, 8]
def baseStart_321609 : Nat := 118140960795 + 321609 * 2 ^ 59
def prefixEnd_321609 : Nat := 4983230072969 + 3 ^ 40 * 321609 * 2
def baseEnd_321609 : Nat := 24465185157324064741993

theorem tailTrace_321609 : CollatzResearch.WordTrace tailWord_321609 prefixEnd_321609 24465185157324064741993 := by
  unfold tailWord_321609
  simp only [CollatzResearch.WordTrace]
  refine ⟨11730043891872994289391881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7820029261248662859594587 11730043891872994289391881)
  ·
    refine ⟨8797532918904745717043911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11730043891872994289391881 8797532918904745717043911)
    ·
      refine ⟨13196299378357118575565867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8797532918904745717043911 13196299378357118575565867)
      ·
        refine ⟨19794449067535677863348801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13196299378357118575565867 19794449067535677863348801)
        ·
          refine ⟨14845836800651758397511601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19794449067535677863348801 14845836800651758397511601)
          ·
            refine ⟨11134377600488818798133701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14845836800651758397511601 11134377600488818798133701)
            ·
              refine ⟨2087695800091653524650069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11134377600488818798133701 2087695800091653524650069)
              ·
                refine ⟨24465185157324064741993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2087695800091653524650069 24465185157324064741993)
                ·
                  rfl

theorem cell21_321609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 4, 8].length) (baseStart_321609 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_321609 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_321609 prefixEnd_321609 := by exact prefixLift 321609
  have htrace : WordTrace (prefixWord ++ tailWord_321609) baseStart_321609 baseEnd_321609 := by
    simpa [prefixWord, tailWord_321609, baseEnd_321609] using wordTrace_append hprefix tailTrace_321609
  have hstable : (prefixWord ++ tailWord_321609).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_321609).length < 2 ^ (prefixWord ++ tailWord_321609).sum := by decide
  have hdescent : baseEnd_321609 < baseStart_321609 := by decide
  rcases family_descends (prefixWord ++ tailWord_321609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_321657 : List Nat := [1, 2, 1, 3, 4, 1, 3, 1, 5]
def baseStart_321657 : Nat := 118140960795 + 321657 * 2 ^ 59
def prefixEnd_321657 : Nat := 4983230072969 + 3 ^ 40 * 321657 * 2
def baseEnd_321657 : Nat := 73406509725934777425881

theorem tailTrace_321657 : CollatzResearch.WordTrace tailWord_321657 prefixEnd_321657 73406509725934777425881 := by
  unfold tailWord_321657
  simp only [CollatzResearch.WordTrace]
  refine ⟨11731794595699098487139225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7821196397132732324759483 11731794595699098487139225)
  ·
    refine ⟨8798845946774323865354419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11731794595699098487139225 8798845946774323865354419)
    ·
      refine ⟨13198268920161485798031629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8798845946774323865354419 13198268920161485798031629)
      ·
        refine ⟨4949350845060557174261861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13198268920161485798031629 4949350845060557174261861)
        ·
          refine ⟨928003283448854470174099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4949350845060557174261861 928003283448854470174099)
          ·
            refine ⟨1392004925173281705261149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 928003283448854470174099 1392004925173281705261149)
            ·
              refine ⟨522001846939980639472931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1392004925173281705261149 522001846939980639472931)
              ·
                refine ⟨783002770409970959209397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 522001846939980639472931 783002770409970959209397)
                ·
                  refine ⟨73406509725934777425881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 783002770409970959209397 73406509725934777425881)
                  ·
                    rfl

theorem cell21_321657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 3, 1, 5].length) (baseStart_321657 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_321657 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_321657 prefixEnd_321657 := by exact prefixLift 321657
  have htrace : WordTrace (prefixWord ++ tailWord_321657) baseStart_321657 baseEnd_321657 := by
    simpa [prefixWord, tailWord_321657, baseEnd_321657] using wordTrace_append hprefix tailTrace_321657
  have hstable : (prefixWord ++ tailWord_321657).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_321657).length < 2 ^ (prefixWord ++ tailWord_321657).sum := by decide
  have hdescent : baseEnd_321657 < baseStart_321657 := by decide
  rcases family_descends (prefixWord ++ tailWord_321657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_321685 : List Nat := [1, 3, 2, 1, 1, 1, 3, 9]
def baseStart_321685 : Nat := 118140960795 + 321685 * 2 ^ 59
def prefixEnd_321685 : Nat := 4983230072969 + 3 ^ 40 * 321685 * 2
def baseEnd_321685 : Nat := 24470966569137650319719

theorem tailTrace_321685 : CollatzResearch.WordTrace tailWord_321685 prefixEnd_321685 24470966569137650319719 := by
  unfold tailWord_321685
  simp only [CollatzResearch.WordTrace]
  refine ⟨11732815839597659269158509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7821877226398439512772339 11732815839597659269158509)
  ·
    refine ⟨4399805939849122225934441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11732815839597659269158509 4399805939849122225934441)
    ·
      refine ⟨3299854454886841669450831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4399805939849122225934441 3299854454886841669450831)
      ·
        refine ⟨4949781682330262504176247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3299854454886841669450831 4949781682330262504176247)
        ·
          refine ⟨7424672523495393756264371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4949781682330262504176247 7424672523495393756264371)
          ·
            refine ⟨11137008785243090634396557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7424672523495393756264371 11137008785243090634396557)
            ·
              refine ⟨4176378294466158987898709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11137008785243090634396557 4176378294466158987898709)
              ·
                refine ⟨24470966569137650319719, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 4176378294466158987898709 24470966569137650319719)
                ·
                  rfl

theorem cell21_321685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 3, 9].length) (baseStart_321685 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_321685 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_321685 prefixEnd_321685 := by exact prefixLift 321685
  have htrace : WordTrace (prefixWord ++ tailWord_321685) baseStart_321685 baseEnd_321685 := by
    simpa [prefixWord, tailWord_321685, baseEnd_321685] using wordTrace_append hprefix tailTrace_321685
  have hstable : (prefixWord ++ tailWord_321685).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_321685).length < 2 ^ (prefixWord ++ tailWord_321685).sum := by decide
  have hdescent : baseEnd_321685 < baseStart_321685 := by decide
  rcases family_descends (prefixWord ++ tailWord_321685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_321761 : List Nat := [1, 2, 3, 1, 3, 1, 10]
def baseStart_321761 : Nat := 118140960795 + 321761 * 2 ^ 59
def prefixEnd_321761 : Nat := 4983230072969 + 3 ^ 40 * 321761 * 2
def baseEnd_321761 : Nat := 8158915993650411965815

theorem tailTrace_321761 : CollatzResearch.WordTrace tailWord_321761 prefixEnd_321761 8158915993650411965815 := by
  unfold tailWord_321761
  simp only [CollatzResearch.WordTrace]
  refine ⟨11735587787322324248925137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7823725191548216165950091 11735587787322324248925137)
  ·
    refine ⟨8801690840491743186693853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11735587787322324248925137 8801690840491743186693853)
    ·
      refine ⟨3300634065184403695010195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8801690840491743186693853 3300634065184403695010195)
      ·
        refine ⟨4950951097776605542515293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3300634065184403695010195 4950951097776605542515293)
        ·
          refine ⟨1856606661666227078443235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4950951097776605542515293 1856606661666227078443235)
          ·
            refine ⟨2784909992499340617664853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1856606661666227078443235 2784909992499340617664853)
            ·
              refine ⟨8158915993650411965815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 2784909992499340617664853 8158915993650411965815)
              ·
                rfl

theorem cell21_321761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 10].length) (baseStart_321761 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_321761 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_321761 prefixEnd_321761 := by exact prefixLift 321761
  have htrace : WordTrace (prefixWord ++ tailWord_321761) baseStart_321761 baseEnd_321761 := by
    simpa [prefixWord, tailWord_321761, baseEnd_321761] using wordTrace_append hprefix tailTrace_321761
  have hstable : (prefixWord ++ tailWord_321761).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_321761).length < 2 ^ (prefixWord ++ tailWord_321761).sum := by decide
  have hdescent : baseEnd_321761 < baseStart_321761 := by decide
  rcases family_descends (prefixWord ++ tailWord_321761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_321792 : List Nat := [2, 1, 1, 2, 1, 1, 6, 2, 5]
def baseStart_321792 : Nat := 118140960795 + 321792 * 2 ^ 59
def prefixEnd_321792 : Nat := 4983230072969 + 3 ^ 40 * 321792 * 2
def baseEnd_321792 : Nat := 73437318565204542675605

theorem tailTrace_321792 : CollatzResearch.WordTrace tailWord_321792 prefixEnd_321792 73437318565204542675605 := by
  unfold tailWord_321792
  simp only [CollatzResearch.WordTrace]
  refine ⟨5868359225105008271651815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7824478966806677695535753 5868359225105008271651815)
  ·
    refine ⟨8802538837657512407477723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5868359225105008271651815 8802538837657512407477723)
    ·
      refine ⟨13203808256486268611216585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8802538837657512407477723 13203808256486268611216585)
      ·
        refine ⟨9902856192364701458412439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13203808256486268611216585 9902856192364701458412439)
        ·
          refine ⟨14854284288547052187618659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9902856192364701458412439 14854284288547052187618659)
          ·
            refine ⟨22281426432820578281427989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14854284288547052187618659 22281426432820578281427989)
            ·
              refine ⟨1044441864038464606941937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 22281426432820578281427989 1044441864038464606941937)
              ·
                refine ⟨783331398028848455206453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1044441864038464606941937 783331398028848455206453)
                ·
                  refine ⟨73437318565204542675605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 783331398028848455206453 73437318565204542675605)
                  ·
                    rfl

theorem cell21_321792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 6, 2, 5].length) (baseStart_321792 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_321792 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_321792 prefixEnd_321792 := by exact prefixLift 321792
  have htrace : WordTrace (prefixWord ++ tailWord_321792) baseStart_321792 baseEnd_321792 := by
    simpa [prefixWord, tailWord_321792, baseEnd_321792] using wordTrace_append hprefix tailTrace_321792
  have hstable : (prefixWord ++ tailWord_321792).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_321792).length < 2 ^ (prefixWord ++ tailWord_321792).sum := by decide
  have hdescent : baseEnd_321792 < baseStart_321792 := by decide
  rcases family_descends (prefixWord ++ tailWord_321792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_321823 : List Nat := [1, 1, 2, 4, 3, 1, 2, 1, 6]
def baseStart_321823 : Nat := 118140960795 + 321823 * 2 ^ 59
def prefixEnd_321823 : Nat := 4983230072969 + 3 ^ 40 * 321823 * 2
def baseEnd_321823 : Nat := 73444393187555377658875

theorem tailTrace_321823 : CollatzResearch.WordTrace tailWord_321823 prefixEnd_321823 73444393187555377658875 := by
  unfold tailWord_321823
  simp only [CollatzResearch.WordTrace]
  refine ⟨11737849113097708837682123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7825232742065139225121415 11737849113097708837682123)
  ·
    refine ⟨17606773669646563256523185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11737849113097708837682123 17606773669646563256523185)
    ·
      refine ⟨13205080252234922442392389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17606773669646563256523185 13205080252234922442392389)
      ·
        refine ⟨2475952547294047957948573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13205080252234922442392389 2475952547294047957948573)
        ·
          refine ⟨928482205235267984230715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2475952547294047957948573 928482205235267984230715)
          ·
            refine ⟨1392723307852901976346073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 928482205235267984230715 1392723307852901976346073)
            ·
              refine ⟨1044542480889676482259555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1392723307852901976346073 1044542480889676482259555)
              ·
                refine ⟨1566813721334514723389333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1044542480889676482259555 1566813721334514723389333)
                ·
                  refine ⟨73444393187555377658875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1566813721334514723389333 73444393187555377658875)
                  ·
                    rfl

theorem cell21_321823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 2, 1, 6].length) (baseStart_321823 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_321823 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_321823 prefixEnd_321823 := by exact prefixLift 321823
  have htrace : WordTrace (prefixWord ++ tailWord_321823) baseStart_321823 baseEnd_321823 := by
    simpa [prefixWord, tailWord_321823, baseEnd_321823] using wordTrace_append hprefix tailTrace_321823
  have hstable : (prefixWord ++ tailWord_321823).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_321823).length < 2 ^ (prefixWord ++ tailWord_321823).sum := by decide
  have hdescent : baseEnd_321823 < baseStart_321823 := by decide
  rcases family_descends (prefixWord ++ tailWord_321823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_321826 : List Nat := [3, 3, 1, 1, 3, 3, 1, 1, 5]
def baseStart_321826 : Nat := 118140960795 + 321826 * 2 ^ 59
def prefixEnd_321826 : Nat := 4983230072969 + 3 ^ 40 * 321826 * 2
def baseEnd_321826 : Nat := 73445077828428039108869

theorem tailTrace_321826 : CollatzResearch.WordTrace tailWord_321826 prefixEnd_321826 73445077828428039108869 := by
  unfold tailWord_321826
  simp only [CollatzResearch.WordTrace]
  refine ⟨2934489633021710087510333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7825305688057893566694221 2934489633021710087510333)
  ·
    refine ⟨1100433612383141282816375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2934489633021710087510333 1100433612383141282816375)
    ·
      refine ⟨1650650418574711924224563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1100433612383141282816375 1650650418574711924224563)
      ·
        refine ⟨2475975627862067886336845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1650650418574711924224563 2475975627862067886336845)
        ·
          refine ⟨928490860448275457376317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2475975627862067886336845 928490860448275457376317)
          ·
            refine ⟨348184072668103296516119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 928490860448275457376317 348184072668103296516119)
            ·
              refine ⟨522276109002154944774179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 348184072668103296516119 522276109002154944774179)
              ·
                refine ⟨783414163503232417161269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 522276109002154944774179 783414163503232417161269)
                ·
                  refine ⟨73445077828428039108869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 783414163503232417161269 73445077828428039108869)
                  ·
                    rfl

theorem cell21_321826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 3, 1, 1, 5].length) (baseStart_321826 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_321826 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_321826 prefixEnd_321826 := by exact prefixLift 321826
  have htrace : WordTrace (prefixWord ++ tailWord_321826) baseStart_321826 baseEnd_321826 := by
    simpa [prefixWord, tailWord_321826, baseEnd_321826] using wordTrace_append hprefix tailTrace_321826
  have hstable : (prefixWord ++ tailWord_321826).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_321826).length < 2 ^ (prefixWord ++ tailWord_321826).sum := by decide
  have hdescent : baseEnd_321826 < baseStart_321826 := by decide
  rcases family_descends (prefixWord ++ tailWord_321826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_321854 : List Nat := [4, 2, 1, 2, 1, 2, 2, 7]
def baseStart_321854 : Nat := 118140960795 + 321854 * 2 ^ 59
def prefixEnd_321854 : Nat := 4983230072969 + 3 ^ 40 * 321854 * 2
def baseEnd_321854 : Nat := 24483822603302070880715

theorem tailTrace_321854 : CollatzResearch.WordTrace tailWord_321854 prefixEnd_321854 24483822603302070880715 := by
  unfold tailWord_321854
  simp only [CollatzResearch.WordTrace]
  refine ⟨1467372471998175141507577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7825986517323600754707077 1467372471998175141507577)
  ·
    refine ⟨1100529353998631356130683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1467372471998175141507577 1100529353998631356130683)
    ·
      refine ⟨1650794030997947034196025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1100529353998631356130683 1650794030997947034196025)
      ·
        refine ⟨1238095523248460275647019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1650794030997947034196025 1238095523248460275647019)
        ·
          refine ⟨1857143284872690413470529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1238095523248460275647019 1857143284872690413470529)
          ·
            refine ⟨1392857463654517810102897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1857143284872690413470529 1392857463654517810102897)
            ·
              refine ⟨1044643097740888357577173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1392857463654517810102897 1044643097740888357577173)
              ·
                refine ⟨24483822603302070880715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1044643097740888357577173 24483822603302070880715)
                ·
                  rfl

theorem cell21_321854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 2, 7].length) (baseStart_321854 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_321854 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_321854 prefixEnd_321854 := by exact prefixLift 321854
  have htrace : WordTrace (prefixWord ++ tailWord_321854) baseStart_321854 baseEnd_321854 := by
    simpa [prefixWord, tailWord_321854, baseEnd_321854] using wordTrace_append hprefix tailTrace_321854
  have hstable : (prefixWord ++ tailWord_321854).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_321854).length < 2 ^ (prefixWord ++ tailWord_321854).sum := by decide
  have hdescent : baseEnd_321854 < baseStart_321854 := by decide
  rcases family_descends (prefixWord ++ tailWord_321854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_321950 : List Nat := [4, 3, 1, 2, 1, 2, 3, 1, 4]
def baseStart_321950 : Nat := 118140960795 + 321950 * 2 ^ 59
def prefixEnd_321950 : Nat := 4983230072969 + 3 ^ 40 * 321950 * 2
def baseEnd_321950 : Nat := 73473376317831379041949

theorem tailTrace_321950 : CollatzResearch.WordTrace tailWord_321950 prefixEnd_321950 73473376317831379041949 := by
  unfold tailWord_321950
  simp only [CollatzResearch.WordTrace]
  refine ⟨1467810147954701190944413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7828320789091739685036869 1467810147954701190944413)
  ·
    refine ⟨550428805483012946604155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1467810147954701190944413 550428805483012946604155)
    ·
      refine ⟨825643208224519419906233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 550428805483012946604155 825643208224519419906233)
      ·
        refine ⟨619232406168389564929675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 825643208224519419906233 619232406168389564929675)
        ·
          refine ⟨928848609252584347394513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 619232406168389564929675 928848609252584347394513)
          ·
            refine ⟨696636456939438260545885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 928848609252584347394513 696636456939438260545885)
            ·
              refine ⟨261238671352289347704707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 696636456939438260545885 261238671352289347704707)
              ·
                refine ⟨391858007028434021557061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 261238671352289347704707 391858007028434021557061)
                ·
                  refine ⟨73473376317831379041949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 391858007028434021557061 73473376317831379041949)
                  ·
                    rfl

theorem cell21_321950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 2, 3, 1, 4].length) (baseStart_321950 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_321950 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_321950 prefixEnd_321950 := by exact prefixLift 321950
  have htrace : WordTrace (prefixWord ++ tailWord_321950) baseStart_321950 baseEnd_321950 := by
    simpa [prefixWord, tailWord_321950, baseEnd_321950] using wordTrace_append hprefix tailTrace_321950
  have hstable : (prefixWord ++ tailWord_321950).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_321950).length < 2 ^ (prefixWord ++ tailWord_321950).sum := by decide
  have hdescent : baseEnd_321950 < baseStart_321950 := by decide
  rcases family_descends (prefixWord ++ tailWord_321950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_322051 : List Nat := [1, 1, 1, 3, 2, 1, 6, 2, 4]
def baseStart_322051 : Nat := 118140960795 + 322051 * 2 ^ 59
def prefixEnd_322051 : Nat := 4983230072969 + 3 ^ 40 * 322051 * 2
def baseEnd_322051 : Nat := 73496425893877647858409

theorem tailTrace_322051 : CollatzResearch.WordTrace tailWord_322051 prefixEnd_322051 73496425893877647858409 := by
  unfold tailWord_322051
  simp only [CollatzResearch.WordTrace]
  refine ⟨11746164956271703776982007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7830776637514469184654671 11746164956271703776982007)
  ·
    refine ⟨17619247434407555665473011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11746164956271703776982007 17619247434407555665473011)
    ·
      refine ⟨26428871151611333498209517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17619247434407555665473011 26428871151611333498209517)
      ·
        refine ⟨9910826681854250061828569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26428871151611333498209517 9910826681854250061828569)
        ·
          refine ⟨7433120011390687546371427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9910826681854250061828569 7433120011390687546371427)
          ·
            refine ⟨11149680017086031319557141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7433120011390687546371427 11149680017086031319557141)
            ·
              refine ⟨522641250800907718104241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 11149680017086031319557141 522641250800907718104241)
              ·
                refine ⟨391980938100680788578181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 522641250800907718104241 391980938100680788578181)
                ·
                  refine ⟨73496425893877647858409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 391980938100680788578181 73496425893877647858409)
                  ·
                    rfl

theorem cell21_322051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 6, 2, 4].length) (baseStart_322051 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_322051 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_322051 prefixEnd_322051 := by exact prefixLift 322051
  have htrace : WordTrace (prefixWord ++ tailWord_322051) baseStart_322051 baseEnd_322051 := by
    simpa [prefixWord, tailWord_322051, baseEnd_322051] using wordTrace_append hprefix tailTrace_322051
  have hstable : (prefixWord ++ tailWord_322051).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_322051).length < 2 ^ (prefixWord ++ tailWord_322051).sum := by decide
  have hdescent : baseEnd_322051 < baseStart_322051 := by decide
  rcases family_descends (prefixWord ++ tailWord_322051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_322113 : List Nat := [1, 2, 5, 1, 1, 3, 2, 1, 5]
def baseStart_322113 : Nat := 118140960795 + 322113 * 2 ^ 59
def prefixEnd_322113 : Nat := 4983230072969 + 3 ^ 40 * 322113 * 2
def baseEnd_322113 : Nat := 73510575138579317824949

theorem tailTrace_322113 : CollatzResearch.WordTrace tailWord_322113 prefixEnd_322113 73510575138579317824949 := by
  unfold tailWord_322113
  simp only [CollatzResearch.WordTrace]
  refine ⟨11748426282047088365738993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7832284188031392243825995 11748426282047088365738993)
  ·
    refine ⟨8811319711535316274304245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11748426282047088365738993 8811319711535316274304245)
    ·
      refine ⟨826061222956435900716023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 8811319711535316274304245 826061222956435900716023)
      ·
        refine ⟨1239091834434653851074035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 826061222956435900716023 1239091834434653851074035)
        ·
          refine ⟨1858637751651980776611053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1239091834434653851074035 1858637751651980776611053)
          ·
            refine ⟨696989156869492791229145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1858637751651980776611053 696989156869492791229145)
            ·
              refine ⟨522741867652119593421859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 696989156869492791229145 522741867652119593421859)
              ·
                refine ⟨784112801478179390132789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 522741867652119593421859 784112801478179390132789)
                ·
                  refine ⟨73510575138579317824949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 784112801478179390132789 73510575138579317824949)
                  ·
                    rfl

theorem cell21_322113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 3, 2, 1, 5].length) (baseStart_322113 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_322113 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_322113 prefixEnd_322113 := by exact prefixLift 322113
  have htrace : WordTrace (prefixWord ++ tailWord_322113) baseStart_322113 baseEnd_322113 := by
    simpa [prefixWord, tailWord_322113, baseEnd_322113] using wordTrace_append hprefix tailTrace_322113
  have hstable : (prefixWord ++ tailWord_322113).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_322113).length < 2 ^ (prefixWord ++ tailWord_322113).sum := by decide
  have hdescent : baseEnd_322113 < baseStart_322113 := by decide
  rcases family_descends (prefixWord ++ tailWord_322113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_322158 : List Nat := [4, 1, 2, 2, 2, 3, 7]
def baseStart_322158 : Nat := 118140960795 + 322158 * 2 ^ 59
def prefixEnd_322158 : Nat := 4983230072969 + 3 ^ 40 * 322158 * 2
def baseEnd_322158 : Nat := 8168982750185471063873

theorem tailTrace_322158 : CollatzResearch.WordTrace tailWord_322158 prefixEnd_322158 8168982750185471063873 := by
  unfold tailWord_322158
  simp only [CollatzResearch.WordTrace]
  refine ⟨1468758445860507631390891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7833378377922707367418085 1468758445860507631390891)
  ·
    refine ⟨2203137668790761447086337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1468758445860507631390891 2203137668790761447086337)
    ·
      refine ⟨1652353251593071085314753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2203137668790761447086337 1652353251593071085314753)
      ·
        refine ⟨1239264938694803313986065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1652353251593071085314753 1239264938694803313986065)
        ·
          refine ⟨929448704021102485489549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1239264938694803313986065 929448704021102485489549)
          ·
            refine ⟨348543264007913432058581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 929448704021102485489549 348543264007913432058581)
            ·
              refine ⟨8168982750185471063873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 348543264007913432058581 8168982750185471063873)
              ·
                rfl

theorem cell21_322158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 3, 7].length) (baseStart_322158 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_322158 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_322158 prefixEnd_322158 := by exact prefixLift 322158
  have htrace : WordTrace (prefixWord ++ tailWord_322158) baseStart_322158 baseEnd_322158 := by
    simpa [prefixWord, tailWord_322158, baseEnd_322158] using wordTrace_append hprefix tailTrace_322158
  have hstable : (prefixWord ++ tailWord_322158).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_322158).length < 2 ^ (prefixWord ++ tailWord_322158).sum := by decide
  have hdescent : baseEnd_322158 < baseStart_322158 := by decide
  rcases family_descends (prefixWord ++ tailWord_322158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_322172 : List Nat := [2, 2, 2, 1, 1, 2, 5, 1, 5]
def baseStart_322172 : Nat := 118140960795 + 322172 * 2 ^ 59
def prefixEnd_322172 : Nat := 4983230072969 + 3 ^ 40 * 322172 * 2
def baseEnd_322172 : Nat := 73524039742408326341495

theorem tailTrace_322172 : CollatzResearch.WordTrace tailWord_322172 prefixEnd_322172 73524039742408326341495 := by
  unfold tailWord_322172
  simp only [CollatzResearch.WordTrace]
  refine ⟨5875289094416670721068385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7833718792555560961424513 5875289094416670721068385)
  ·
    refine ⟨4406466820812503040801289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5875289094416670721068385 4406466820812503040801289)
    ·
      refine ⟨3304850115609377280600967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4406466820812503040801289 3304850115609377280600967)
      ·
        refine ⟨4957275173414065920901451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3304850115609377280600967 4957275173414065920901451)
        ·
          refine ⟨7435912760121098881352177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4957275173414065920901451 7435912760121098881352177)
          ·
            refine ⟨5576934570090824161014133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7435912760121098881352177 5576934570090824161014133)
            ·
              refine ⟨522837615946014765095075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5576934570090824161014133 522837615946014765095075)
              ·
                refine ⟨784256423919022147642613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 522837615946014765095075 784256423919022147642613)
                ·
                  refine ⟨73524039742408326341495, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 784256423919022147642613 73524039742408326341495)
                  ·
                    rfl

theorem cell21_322172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 5, 1, 5].length) (baseStart_322172 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_322172 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_322172 prefixEnd_322172 := by exact prefixLift 322172
  have htrace : WordTrace (prefixWord ++ tailWord_322172) baseStart_322172 baseEnd_322172 := by
    simpa [prefixWord, tailWord_322172, baseEnd_322172] using wordTrace_append hprefix tailTrace_322172
  have hstable : (prefixWord ++ tailWord_322172).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_322172).length < 2 ^ (prefixWord ++ tailWord_322172).sum := by decide
  have hdescent : baseEnd_322172 < baseStart_322172 := by decide
  rcases family_descends (prefixWord ++ tailWord_322172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_322206 : List Nat := [4, 3, 1, 1, 1, 1, 2, 5, 3]
def baseStart_322206 : Nat := 118140960795 + 322206 * 2 ^ 59
def prefixEnd_322206 : Nat := 4983230072969 + 3 ^ 40 * 322206 * 2
def baseEnd_322206 : Nat := 73531799005631822774759

theorem tailTrace_322206 : CollatzResearch.WordTrace tailWord_322206 prefixEnd_322206 73531799005631822774759 := by
  unfold tailWord_322206
  simp only [CollatzResearch.WordTrace]
  refine ⟨1468977283838770656109309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7834545513806776832582981 1468977283838770656109309)
  ·
    refine ⟨550866481439538996040991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1468977283838770656109309 550866481439538996040991)
    ·
      refine ⟨826299722159308494061487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 550866481439538996040991 826299722159308494061487)
      ·
        refine ⟨1239449583238962741092231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 826299722159308494061487 1239449583238962741092231)
        ·
          refine ⟨1859174374858444111638347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1239449583238962741092231 1859174374858444111638347)
          ·
            refine ⟨2788761562287666167457521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1859174374858444111638347 2788761562287666167457521)
            ·
              refine ⟨2091571171715749625593141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2788761562287666167457521 2091571171715749625593141)
              ·
                refine ⟨196084797348351527399357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2091571171715749625593141 196084797348351527399357)
                ·
                  refine ⟨73531799005631822774759, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 196084797348351527399357 73531799005631822774759)
                  ·
                    rfl

theorem cell21_322206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 2, 5, 3].length) (baseStart_322206 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_322206 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_322206 prefixEnd_322206 := by exact prefixLift 322206
  have htrace : WordTrace (prefixWord ++ tailWord_322206) baseStart_322206 baseEnd_322206 := by
    simpa [prefixWord, tailWord_322206, baseEnd_322206] using wordTrace_append hprefix tailTrace_322206
  have hstable : (prefixWord ++ tailWord_322206).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_322206).length < 2 ^ (prefixWord ++ tailWord_322206).sum := by decide
  have hdescent : baseEnd_322206 < baseStart_322206 := by decide
  rcases family_descends (prefixWord ++ tailWord_322206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_322248 : List Nat := [2, 1, 3, 1, 2, 4, 1, 2, 5]
def baseStart_322248 : Nat := 118140960795 + 322248 * 2 ^ 59
def prefixEnd_322248 : Nat := 4983230072969 + 3 ^ 40 * 322248 * 2
def baseEnd_322248 : Nat := 73541383977849083074673

theorem tailTrace_322248 : CollatzResearch.WordTrace tailWord_322248 prefixEnd_322248 73541383977849083074673 := by
  unfold tailWord_322248
  simp only [CollatzResearch.WordTrace]
  refine ⟨5876675068279003210951699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7835566757705337614602265 5876675068279003210951699)
  ·
    refine ⟨8815012602418504816427549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5876675068279003210951699 8815012602418504816427549)
    ·
      refine ⟨3305629725906939306160331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8815012602418504816427549 3305629725906939306160331)
      ·
        refine ⟨4958444588860408959240497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3305629725906939306160331 4958444588860408959240497)
        ·
          refine ⟨3718833441645306719430373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4958444588860408959240497 3718833441645306719430373)
          ·
            refine ⟨697281270308495009893195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3718833441645306719430373 697281270308495009893195)
            ·
              refine ⟨1045921905462742514839793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 697281270308495009893195 1045921905462742514839793)
              ·
                refine ⟨784441429097056886129845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1045921905462742514839793 784441429097056886129845)
                ·
                  refine ⟨73541383977849083074673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 784441429097056886129845 73541383977849083074673)
                  ·
                    rfl

theorem cell21_322248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 4, 1, 2, 5].length) (baseStart_322248 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_322248 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_322248 prefixEnd_322248 := by exact prefixLift 322248
  have htrace : WordTrace (prefixWord ++ tailWord_322248) baseStart_322248 baseEnd_322248 := by
    simpa [prefixWord, tailWord_322248, baseEnd_322248] using wordTrace_append hprefix tailTrace_322248
  have hstable : (prefixWord ++ tailWord_322248).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_322248).length < 2 ^ (prefixWord ++ tailWord_322248).sum := by decide
  have hdescent : baseEnd_322248 < baseStart_322248 := by decide
  rcases family_descends (prefixWord ++ tailWord_322248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_322265 : List Nat := [1, 2, 1, 2, 3, 2, 4, 3, 3]
def baseStart_322265 : Nat := 118140960795 + 322265 * 2 ^ 59
def prefixEnd_322265 : Nat := 4983230072969 + 3 ^ 40 * 322265 * 2
def baseEnd_322265 : Nat := 73545263609460831291305

theorem tailTrace_322265 : CollatzResearch.WordTrace tailWord_322265 prefixEnd_322265 73545263609460831291305 := by
  unfold tailWord_322265
  simp only [CollatzResearch.WordTrace]
  refine ⟨11753970177496418325272249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7835980118330945550181499 11753970177496418325272249)
  ·
    refine ⟨8815477633122313743954187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11753970177496418325272249 8815477633122313743954187)
    ·
      refine ⟨13223216449683470615931281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8815477633122313743954187 13223216449683470615931281)
      ·
        refine ⟨9917412337262602961948461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13223216449683470615931281 9917412337262602961948461)
        ·
          refine ⟨3719029626473476110730673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9917412337262602961948461 3719029626473476110730673)
          ·
            refine ⟨2789272219855107083048005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3719029626473476110730673 2789272219855107083048005)
            ·
              refine ⟨522988541222832578071501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2789272219855107083048005 522988541222832578071501)
              ·
                refine ⟨196120702958562216776813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 522988541222832578071501 196120702958562216776813)
                ·
                  refine ⟨73545263609460831291305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 196120702958562216776813 73545263609460831291305)
                  ·
                    rfl

theorem cell21_322265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 4, 3, 3].length) (baseStart_322265 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_322265 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_322265 prefixEnd_322265 := by exact prefixLift 322265
  have htrace : WordTrace (prefixWord ++ tailWord_322265) baseStart_322265 baseEnd_322265 := by
    simpa [prefixWord, tailWord_322265, baseEnd_322265] using wordTrace_append hprefix tailTrace_322265
  have hstable : (prefixWord ++ tailWord_322265).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_322265).length < 2 ^ (prefixWord ++ tailWord_322265).sum := by decide
  have hdescent : baseEnd_322265 < baseStart_322265 := by decide
  rcases family_descends (prefixWord ++ tailWord_322265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_322355 : List Nat := [1, 1, 1, 2, 6, 2, 1, 3, 4]
def baseStart_322355 : Nat := 118140960795 + 322355 * 2 ^ 59
def prefixEnd_322355 : Nat := 4983230072969 + 3 ^ 40 * 322355 * 2
def baseEnd_322355 : Nat := 73565802835640674791121

theorem tailTrace_322355 : CollatzResearch.WordTrace tailWord_322355 prefixEnd_322355 73565802835640674791121 := by
  unfold tailWord_322355
  simp only [CollatzResearch.WordTrace]
  refine ⟨11757252747170363696048519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7838168498113575797365679 11757252747170363696048519)
  ·
    refine ⟨17635879120755545544072779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11757252747170363696048519 17635879120755545544072779)
    ·
      refine ⟨26453818681133318316109169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17635879120755545544072779 26453818681133318316109169)
      ·
        refine ⟨19840364010849988737081877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26453818681133318316109169 19840364010849988737081877)
        ·
          refine ⟨930017063008593222050713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 19840364010849988737081877 930017063008593222050713)
          ·
            refine ⟨697512797256444916538035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 930017063008593222050713 697512797256444916538035)
            ·
              refine ⟨1046269195884667374807053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 697512797256444916538035 1046269195884667374807053)
              ·
                refine ⟨392350948456750265552645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1046269195884667374807053 392350948456750265552645)
                ·
                  refine ⟨73565802835640674791121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 392350948456750265552645 73565802835640674791121)
                  ·
                    rfl

theorem cell21_322355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 2, 1, 3, 4].length) (baseStart_322355 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_322355 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_322355 prefixEnd_322355 := by exact prefixLift 322355
  have htrace : WordTrace (prefixWord ++ tailWord_322355) baseStart_322355 baseEnd_322355 := by
    simpa [prefixWord, tailWord_322355, baseEnd_322355] using wordTrace_append hprefix tailTrace_322355
  have hstable : (prefixWord ++ tailWord_322355).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_322355).length < 2 ^ (prefixWord ++ tailWord_322355).sum := by decide
  have hdescent : baseEnd_322355 < baseStart_322355 := by decide
  rcases family_descends (prefixWord ++ tailWord_322355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_322428 : List Nat := [2, 2, 2, 1, 1, 1, 1, 11]
def baseStart_322428 : Nat := 118140960795 + 322428 * 2 ^ 59
def prefixEnd_322428 : Nat := 4983230072969 + 3 ^ 40 * 322428 * 2
def baseEnd_322428 : Nat := 24527487476736256691435

theorem tailTrace_322428 : CollatzResearch.WordTrace tailWord_322428 prefixEnd_322428 24527487476736256691435 := by
  unfold tailWord_322428
  simp only [CollatzResearch.WordTrace]
  refine ⟨5879957637952948581727969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7839943517270598108970625 5879957637952948581727969)
  ·
    refine ⟨4409968228464711436295977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5879957637952948581727969 4409968228464711436295977)
    ·
      refine ⟨3307476171348533577221983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4409968228464711436295977 3307476171348533577221983)
      ·
        refine ⟨4961214257022800365832975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3307476171348533577221983 4961214257022800365832975)
        ·
          refine ⟨7441821385534200548749463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4961214257022800365832975 7441821385534200548749463)
          ·
            refine ⟨11162732078301300823124195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7441821385534200548749463 11162732078301300823124195)
            ·
              refine ⟨16744098117451951234686293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11162732078301300823124195 16744098117451951234686293)
              ·
                refine ⟨24527487476736256691435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 16744098117451951234686293 24527487476736256691435)
                ·
                  rfl

theorem cell21_322428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 11].length) (baseStart_322428 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_322428 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_322428 prefixEnd_322428 := by exact prefixLift 322428
  have htrace : WordTrace (prefixWord ++ tailWord_322428) baseStart_322428 baseEnd_322428 := by
    simpa [prefixWord, tailWord_322428, baseEnd_322428] using wordTrace_append hprefix tailTrace_322428
  have hstable : (prefixWord ++ tailWord_322428).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_322428).length < 2 ^ (prefixWord ++ tailWord_322428).sum := by decide
  have hdescent : baseEnd_322428 < baseStart_322428 := by decide
  rcases family_descends (prefixWord ++ tailWord_322428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_322502 : List Nat := [6, 1, 3, 1, 1, 1, 3, 2, 3]
def baseStart_322502 : Nat := 118140960795 + 322502 * 2 ^ 59
def prefixEnd_322502 : Nat := 4983230072969 + 3 ^ 40 * 322502 * 2
def baseEnd_322502 : Nat := 73599350238401085840821

theorem tailTrace_322502 : CollatzResearch.WordTrace tailWord_322502 prefixEnd_322502 73599350238401085840821 := by
  unfold tailWord_322502
  simp only [CollatzResearch.WordTrace]
  refine ⟨367581696176181493801555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 7841742851758538534433173 367581696176181493801555)
  ·
    refine ⟨551372544264272240702333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 367581696176181493801555 551372544264272240702333)
    ·
      refine ⟨206764704099102090263375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 551372544264272240702333 206764704099102090263375)
      ·
        refine ⟨310147056148653135395063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 206764704099102090263375 310147056148653135395063)
        ·
          refine ⟨465220584222979703092595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 310147056148653135395063 465220584222979703092595)
          ·
            refine ⟨697830876334469554638893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 465220584222979703092595 697830876334469554638893)
            ·
              refine ⟨261686578625426082989585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 697830876334469554638893 261686578625426082989585)
              ·
                refine ⟨196264933969069562242189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 261686578625426082989585 196264933969069562242189)
                ·
                  refine ⟨73599350238401085840821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 196264933969069562242189 73599350238401085840821)
                  ·
                    rfl

theorem cell21_322502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 1, 3, 2, 3].length) (baseStart_322502 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_322502 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_322502 prefixEnd_322502 := by exact prefixLift 322502
  have htrace : WordTrace (prefixWord ++ tailWord_322502) baseStart_322502 baseEnd_322502 := by
    simpa [prefixWord, tailWord_322502, baseEnd_322502] using wordTrace_append hprefix tailTrace_322502
  have hstable : (prefixWord ++ tailWord_322502).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_322502).length < 2 ^ (prefixWord ++ tailWord_322502).sum := by decide
  have hdescent : baseEnd_322502 < baseStart_322502 := by decide
  rcases family_descends (prefixWord ++ tailWord_322502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_322510 : List Nat := [4, 1, 1, 1, 2, 4, 3, 2, 3]
def baseStart_322510 : Nat := 118140960795 + 322510 * 2 ^ 59
def prefixEnd_322510 : Nat := 4983230072969 + 3 ^ 40 * 322510 * 2
def baseEnd_322510 : Nat := 73601175947394849707471

theorem tailTrace_322510 : CollatzResearch.WordTrace tailWord_322510 prefixEnd_322510 73601175947394849707471 := by
  unfold tailWord_322510
  simp only [CollatzResearch.WordTrace]
  refine ⟨1470363257701103145992623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7841937374405883445293989 1470363257701103145992623)
  ·
    refine ⟨2205544886551654718988935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1470363257701103145992623 2205544886551654718988935)
    ·
      refine ⟨3308317329827482078483403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2205544886551654718988935 3308317329827482078483403)
      ·
        refine ⟨4962475994741223117725105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3308317329827482078483403 4962475994741223117725105)
        ·
          refine ⟨3721856996055917338293829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4962475994741223117725105 3721856996055917338293829)
          ·
            refine ⟨697848186760484500930093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3721856996055917338293829 697848186760484500930093)
            ·
              refine ⟨261693070035181687848785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 697848186760484500930093 261693070035181687848785)
              ·
                refine ⟨196269802526386265886589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 261693070035181687848785 196269802526386265886589)
                ·
                  refine ⟨73601175947394849707471, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 196269802526386265886589 73601175947394849707471)
                  ·
                    rfl

theorem cell21_322510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 4, 3, 2, 3].length) (baseStart_322510 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_322510 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_322510 prefixEnd_322510 := by exact prefixLift 322510
  have htrace : WordTrace (prefixWord ++ tailWord_322510) baseStart_322510 baseEnd_322510 := by
    simpa [prefixWord, tailWord_322510, baseEnd_322510] using wordTrace_append hprefix tailTrace_322510
  have hstable : (prefixWord ++ tailWord_322510).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_322510).length < 2 ^ (prefixWord ++ tailWord_322510).sum := by decide
  have hdescent : baseEnd_322510 < baseStart_322510 := by decide
  rcases family_descends (prefixWord ++ tailWord_322510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_322521 : List Nat := [1, 2, 1, 2, 5, 2, 2, 6]
def baseStart_322521 : Nat := 118140960795 + 322521 * 2 ^ 59
def prefixEnd_322521 : Nat := 4983230072969 + 3 ^ 40 * 322521 * 2
def baseEnd_322521 : Nat := 24534562099087091674705

theorem tailTrace_322521 : CollatzResearch.WordTrace tailWord_322521 prefixEnd_322521 24534562099087091674705 := by
  unfold tailWord_322521
  simp only [CollatzResearch.WordTrace]
  refine ⟨11763307264568974046591417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7842204843045982697727611 11763307264568974046591417)
  ·
    refine ⟨8822480448426730534943563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11763307264568974046591417 8822480448426730534943563)
    ·
      refine ⟨13233720672640095802415345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8822480448426730534943563 13233720672640095802415345)
      ·
        refine ⟨9925290504480071851811509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13233720672640095802415345 9925290504480071851811509)
        ·
          refine ⟨930495984795006736107329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 9925290504480071851811509 930495984795006736107329)
          ·
            refine ⟨697871988596255052080497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 930495984795006736107329 697871988596255052080497)
            ·
              refine ⟨523403991447191289060373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 697871988596255052080497 523403991447191289060373)
              ·
                refine ⟨24534562099087091674705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 523403991447191289060373 24534562099087091674705)
                ·
                  rfl

theorem cell21_322521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 2, 2, 6].length) (baseStart_322521 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_322521 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_322521 prefixEnd_322521 := by exact prefixLift 322521
  have htrace : WordTrace (prefixWord ++ tailWord_322521) baseStart_322521 baseEnd_322521 := by
    simpa [prefixWord, tailWord_322521, baseEnd_322521] using wordTrace_append hprefix tailTrace_322521
  have hstable : (prefixWord ++ tailWord_322521).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_322521).length < 2 ^ (prefixWord ++ tailWord_322521).sum := by decide
  have hdescent : baseEnd_322521 < baseStart_322521 := by decide
  rcases family_descends (prefixWord ++ tailWord_322521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_322552 : List Nat := [2, 1, 2, 1, 1, 3, 1, 7, 3]
def baseStart_322552 : Nat := 118140960795 + 322552 * 2 ^ 59
def prefixEnd_322552 : Nat := 4983230072969 + 3 ^ 40 * 322552 * 2
def baseEnd_322552 : Nat := 73610760919612110007385

theorem tailTrace_322552 : CollatzResearch.WordTrace tailWord_322552 prefixEnd_322552 73610760919612110007385 := by
  unfold tailWord_322552
  simp only [CollatzResearch.WordTrace]
  refine ⟨5882218963728333170484955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7842958618304444227313273 5882218963728333170484955)
  ·
    refine ⟨8823328445592499755727433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5882218963728333170484955 8823328445592499755727433)
    ·
      refine ⟨6617496334194374816795575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8823328445592499755727433 6617496334194374816795575)
      ·
        refine ⟨9926244501291562225193363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6617496334194374816795575 9926244501291562225193363)
        ·
          refine ⟨14889366751937343337790045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9926244501291562225193363 14889366751937343337790045)
          ·
            refine ⟨5583512531976503751671267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14889366751937343337790045 5583512531976503751671267)
            ·
              refine ⟨8375268797964755627506901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5583512531976503751671267 8375268797964755627506901)
              ·
                refine ⟨196295362452298960019693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 8375268797964755627506901 196295362452298960019693)
                ·
                  refine ⟨73610760919612110007385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 196295362452298960019693 73610760919612110007385)
                  ·
                    rfl

theorem cell21_322552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 7, 3].length) (baseStart_322552 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_322552 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_322552 prefixEnd_322552 := by exact prefixLift 322552
  have htrace : WordTrace (prefixWord ++ tailWord_322552) baseStart_322552 baseEnd_322552 := by
    simpa [prefixWord, tailWord_322552, baseEnd_322552] using wordTrace_append hprefix tailTrace_322552
  have hstable : (prefixWord ++ tailWord_322552).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_322552).length < 2 ^ (prefixWord ++ tailWord_322552).sum := by decide
  have hdescent : baseEnd_322552 < baseStart_322552 := by decide
  rcases family_descends (prefixWord ++ tailWord_322552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_322583 : List Nat := [1, 1, 3, 5, 1, 1, 2, 3, 4]
def baseStart_322583 : Nat := 118140960795 + 322583 * 2 ^ 59
def prefixEnd_322583 : Nat := 4983230072969 + 3 ^ 40 * 322583 * 2
def baseEnd_322583 : Nat := 73617835541962944990655

theorem tailTrace_322583 : CollatzResearch.WordTrace tailWord_322583 prefixEnd_322583 73617835541962944990655 := by
  unfold tailWord_322583
  simp only [CollatzResearch.WordTrace]
  refine ⟨11765568590344358635348403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7843712393562905756898935 11765568590344358635348403)
  ·
    refine ⟨17648352885516537953022605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11765568590344358635348403 17648352885516537953022605)
    ·
      refine ⟨6618132332068701732383477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17648352885516537953022605 6618132332068701732383477)
      ·
        refine ⟨620449906131440787410951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 6618132332068701732383477 620449906131440787410951)
        ·
          refine ⟨930674859197161181116427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 620449906131440787410951 930674859197161181116427)
          ·
            refine ⟨1396012288795741771674641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 930674859197161181116427 1396012288795741771674641)
            ·
              refine ⟨1047009216596806328755981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1396012288795741771674641 1047009216596806328755981)
              ·
                refine ⟨392628456223802373283493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1047009216596806328755981 392628456223802373283493)
                ·
                  refine ⟨73617835541962944990655, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 392628456223802373283493 73617835541962944990655)
                  ·
                    rfl

theorem cell21_322583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 2, 3, 4].length) (baseStart_322583 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_322583 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_322583 prefixEnd_322583 := by exact prefixLift 322583
  have htrace : WordTrace (prefixWord ++ tailWord_322583) baseStart_322583 baseEnd_322583 := by
    simpa [prefixWord, tailWord_322583, baseEnd_322583] using wordTrace_append hprefix tailTrace_322583
  have hstable : (prefixWord ++ tailWord_322583).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_322583).length < 2 ^ (prefixWord ++ tailWord_322583).sum := by decide
  have hdescent : baseEnd_322583 < baseStart_322583 := by decide
  rcases family_descends (prefixWord ++ tailWord_322583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_322597 : List Nat := [1, 3, 1, 2, 2, 2, 5, 5]
def baseStart_322597 : Nat := 118140960795 + 322597 * 2 ^ 59
def prefixEnd_322597 : Nat := 4983230072969 + 3 ^ 40 * 322597 * 2
def baseEnd_322597 : Nat := 24540343510900677252431

theorem tailTrace_322597 : CollatzResearch.WordTrace tailWord_322597 prefixEnd_322597 24540343510900677252431 := by
  unfold tailWord_322597
  simp only [CollatzResearch.WordTrace]
  refine ⟨11766079212293639026358045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7844052808195759350905363 11766079212293639026358045)
  ·
    refine ⟨4412279704610114634884267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11766079212293639026358045 4412279704610114634884267)
    ·
      refine ⟨6618419556915171952326401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4412279704610114634884267 6618419556915171952326401)
      ·
        refine ⟨4963814667686378964244801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6618419556915171952326401 4963814667686378964244801)
        ·
          refine ⟨3722861000764784223183601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4963814667686378964244801 3722861000764784223183601)
          ·
            refine ⟨2792145750573588167387701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3722861000764784223183601 2792145750573588167387701)
            ·
              refine ⟨261763664116273890692597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2792145750573588167387701 261763664116273890692597)
              ·
                refine ⟨24540343510900677252431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 261763664116273890692597 24540343510900677252431)
                ·
                  rfl

theorem cell21_322597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 5, 5].length) (baseStart_322597 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_322597 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_322597 prefixEnd_322597 := by exact prefixLift 322597
  have htrace : WordTrace (prefixWord ++ tailWord_322597) baseStart_322597 baseEnd_322597 := by
    simpa [prefixWord, tailWord_322597, baseEnd_322597] using wordTrace_append hprefix tailTrace_322597
  have hstable : (prefixWord ++ tailWord_322597).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_322597).length < 2 ^ (prefixWord ++ tailWord_322597).sum := by decide
  have hdescent : baseEnd_322597 < baseStart_322597 := by decide
  rcases family_descends (prefixWord ++ tailWord_322597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_322656 : List Nat := [2, 1, 1, 3, 2, 2, 3, 7]
def baseStart_322656 : Nat := 118140960795 + 322656 * 2 ^ 59
def prefixEnd_322656 : Nat := 4983230072969 + 3 ^ 40 * 322656 * 2
def baseEnd_322656 : Nat := 24544831712177013424613

theorem tailTrace_322656 : CollatzResearch.WordTrace tailWord_322656 prefixEnd_322656 24544831712177013424613 := by
  unfold tailWord_322656
  simp only [CollatzResearch.WordTrace]
  refine ⟨5884115559539946051377911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7845487412719928068503881 5884115559539946051377911)
  ·
    refine ⟨8826173339309919077066867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5884115559539946051377911 8826173339309919077066867)
    ·
      refine ⟨13239260008964878615600301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8826173339309919077066867 13239260008964878615600301)
      ·
        refine ⟨4964722503361829480850113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13239260008964878615600301 4964722503361829480850113)
        ·
          refine ⟨3723541877521372110637585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4964722503361829480850113 3723541877521372110637585)
          ·
            refine ⟨2792656408141029082978189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3723541877521372110637585 2792656408141029082978189)
            ·
              refine ⟨1047246153052885906116821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2792656408141029082978189 1047246153052885906116821)
              ·
                refine ⟨24544831712177013424613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1047246153052885906116821 24544831712177013424613)
                ·
                  rfl

theorem cell21_322656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 3, 7].length) (baseStart_322656 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_322656 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_322656 prefixEnd_322656 := by exact prefixLift 322656
  have htrace : WordTrace (prefixWord ++ tailWord_322656) baseStart_322656 baseEnd_322656 := by
    simpa [prefixWord, tailWord_322656, baseEnd_322656] using wordTrace_append hprefix tailTrace_322656
  have hstable : (prefixWord ++ tailWord_322656).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_322656).length < 2 ^ (prefixWord ++ tailWord_322656).sum := by decide
  have hdescent : baseEnd_322656 < baseStart_322656 := by decide
  rcases family_descends (prefixWord ++ tailWord_322656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_322693 : List Nat := [1, 3, 1, 1, 7, 1, 2, 1, 4]
def baseStart_322693 : Nat := 118140960795 + 322693 * 2 ^ 59
def prefixEnd_322693 : Nat := 4983230072969 + 3 ^ 40 * 322693 * 2
def baseEnd_322693 : Nat := 73642939040627198157097

theorem tailTrace_322693 : CollatzResearch.WordTrace tailWord_322693 prefixEnd_322693 73642939040627198157097 := by
  unfold tailWord_322693
  simp only [CollatzResearch.WordTrace]
  refine ⟨11769580619945847421852733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7846387079963898281235155 11769580619945847421852733)
  ·
    refine ⟨4413592732479692783194775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11769580619945847421852733 4413592732479692783194775)
    ·
      refine ⟨6620389098719539174792163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4413592732479692783194775 6620389098719539174792163)
      ·
        refine ⟨9930583648079308762188245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6620389098719539174792163 9930583648079308762188245)
        ·
          refine ⟨232748054251858799113787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 9930583648079308762188245 232748054251858799113787)
          ·
            refine ⟨349122081377788198670681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 232748054251858799113787 349122081377788198670681)
            ·
              refine ⟨261841561033341149003011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 349122081377788198670681 261841561033341149003011)
              ·
                refine ⟨392762341550011723504517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 261841561033341149003011 392762341550011723504517)
                ·
                  refine ⟨73642939040627198157097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 392762341550011723504517 73642939040627198157097)
                  ·
                    rfl

theorem cell21_322693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 7, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 7, 1, 2, 1, 4].length) (baseStart_322693 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_322693 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_322693 prefixEnd_322693 := by exact prefixLift 322693
  have htrace : WordTrace (prefixWord ++ tailWord_322693) baseStart_322693 baseEnd_322693 := by
    simpa [prefixWord, tailWord_322693, baseEnd_322693] using wordTrace_append hprefix tailTrace_322693
  have hstable : (prefixWord ++ tailWord_322693).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_322693).length < 2 ^ (prefixWord ++ tailWord_322693).sum := by decide
  have hdescent : baseEnd_322693 < baseStart_322693 := by decide
  rcases family_descends (prefixWord ++ tailWord_322693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_322738 : List Nat := [3, 2, 1, 1, 1, 6, 2, 2, 3]
def baseStart_322738 : Nat := 118140960795 + 322738 * 2 ^ 59
def prefixEnd_322738 : Nat := 4983230072969 + 3 ^ 40 * 322738 * 2
def baseEnd_322738 : Nat := 73653208653717119907005

theorem tailTrace_322738 : CollatzResearch.WordTrace tailWord_322738 prefixEnd_322738 73653208653717119907005 := by
  unfold tailWord_322738
  simp only [CollatzResearch.WordTrace]
  refine ⟨2942805476195705026810217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7847481269855213404827245 2942805476195705026810217)
  ·
    refine ⟨2207104107146778770107663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2942805476195705026810217 2207104107146778770107663)
    ·
      refine ⟨3310656160720168155161495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2207104107146778770107663 3310656160720168155161495)
      ·
        refine ⟨4965984241080252232742243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3310656160720168155161495 4965984241080252232742243)
        ·
          refine ⟨7448976361620378349113365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4965984241080252232742243 7448976361620378349113365)
          ·
            refine ⟨349170766950955235114689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 7448976361620378349113365 349170766950955235114689)
            ·
              refine ⟨261878075213216426336017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 349170766950955235114689 261878075213216426336017)
              ·
                refine ⟨196408556409912319752013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 261878075213216426336017 196408556409912319752013)
                ·
                  refine ⟨73653208653717119907005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 196408556409912319752013 73653208653717119907005)
                  ·
                    rfl

theorem cell21_322738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 6, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 6, 2, 2, 3].length) (baseStart_322738 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_322738 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_322738 prefixEnd_322738 := by exact prefixLift 322738
  have htrace : WordTrace (prefixWord ++ tailWord_322738) baseStart_322738 baseEnd_322738 := by
    simpa [prefixWord, tailWord_322738, baseEnd_322738] using wordTrace_append hprefix tailTrace_322738
  have hstable : (prefixWord ++ tailWord_322738).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_322738).length < 2 ^ (prefixWord ++ tailWord_322738).sum := by decide
  have hdescent : baseEnd_322738 < baseStart_322738 := by decide
  rcases family_descends (prefixWord ++ tailWord_322738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_322766 : List Nat := [4, 1, 1, 1, 5, 1, 3, 5]
def baseStart_322766 : Nat := 118140960795 + 322766 * 2 ^ 59
def prefixEnd_322766 : Nat := 4983230072969 + 3 ^ 40 * 322766 * 2
def baseEnd_322766 : Nat := 24553199545065097813427

theorem tailTrace_322766 : CollatzResearch.WordTrace tailWord_322766 prefixEnd_322766 24553199545065097813427 := by
  unfold tailWord_322766
  simp only [CollatzResearch.WordTrace]
  refine ⟨1471530393585172611157519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7848162099120920592840101 1471530393585172611157519)
  ·
    refine ⟨2207295590377758916736279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1471530393585172611157519 2207295590377758916736279)
    ·
      refine ⟨3310943385566638375104419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2207295590377758916736279 3310943385566638375104419)
      ·
        refine ⟨4966415078349957562656629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3310943385566638375104419 4966415078349957562656629)
        ·
          refine ⟨465601413595308521499059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 4966415078349957562656629 465601413595308521499059)
          ·
            refine ⟨698402120392962782248589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 465601413595308521499059 698402120392962782248589)
            ·
              refine ⟨261900795147361043343221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 698402120392962782248589 261900795147361043343221)
              ·
                refine ⟨24553199545065097813427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 261900795147361043343221 24553199545065097813427)
                ·
                  rfl

theorem cell21_322766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 1, 3, 5].length) (baseStart_322766 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_322766 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_322766 prefixEnd_322766 := by exact prefixLift 322766
  have htrace : WordTrace (prefixWord ++ tailWord_322766) baseStart_322766 baseEnd_322766 := by
    simpa [prefixWord, tailWord_322766, baseEnd_322766] using wordTrace_append hprefix tailTrace_322766
  have hstable : (prefixWord ++ tailWord_322766).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_322766).length < 2 ^ (prefixWord ++ tailWord_322766).sum := by decide
  have hdescent : baseEnd_322766 < baseStart_322766 := by decide
  rcases family_descends (prefixWord ++ tailWord_322766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_322777 : List Nat := [1, 2, 1, 2, 3, 1, 1, 4, 6]
def baseStart_322777 : Nat := 118140960795 + 322777 * 2 ^ 59
def prefixEnd_322777 : Nat := 4983230072969 + 3 ^ 40 * 322777 * 2
def baseEnd_322777 : Nat := 73662108985061718756925

theorem tailTrace_322777 : CollatzResearch.WordTrace tailWord_322777 prefixEnd_322777 73662108985061718756925 := by
  unfold tailWord_322777
  simp only [CollatzResearch.WordTrace]
  refine ⟨11772644351641529767910585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7848429567761019845273723 11772644351641529767910585)
  ·
    refine ⟨8829483263731147325932939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11772644351641529767910585 8829483263731147325932939)
    ·
      refine ⟨13244224895596720988899409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8829483263731147325932939 13244224895596720988899409)
      ·
        refine ⟨9933168671697540741674557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13244224895596720988899409 9933168671697540741674557)
        ·
          refine ⟨3724938251886577778127959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9933168671697540741674557 3724938251886577778127959)
          ·
            refine ⟨5587407377829866667191939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3724938251886577778127959 5587407377829866667191939)
            ·
              refine ⟨8381111066744800000787909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5587407377829866667191939 8381111066744800000787909)
              ·
                refine ⟨1571458325014650000147733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8381111066744800000787909 1571458325014650000147733)
                ·
                  refine ⟨73662108985061718756925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1571458325014650000147733 73662108985061718756925)
                  ·
                    rfl

theorem cell21_322777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 4, 6].length) (baseStart_322777 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_322777 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_322777 prefixEnd_322777 := by exact prefixLift 322777
  have htrace : WordTrace (prefixWord ++ tailWord_322777) baseStart_322777 baseEnd_322777 := by
    simpa [prefixWord, tailWord_322777, baseEnd_322777] using wordTrace_append hprefix tailTrace_322777
  have hstable : (prefixWord ++ tailWord_322777).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_322777).length < 2 ^ (prefixWord ++ tailWord_322777).sum := by decide
  have hdescent : baseEnd_322777 < baseStart_322777 := by decide
  rcases family_descends (prefixWord ++ tailWord_322777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_322794 : List Nat := [3, 1, 3, 1, 1, 4, 1, 1, 6]
def baseStart_322794 : Nat := 118140960795 + 322794 * 2 ^ 59
def prefixEnd_322794 : Nat := 4983230072969 + 3 ^ 40 * 322794 * 2
def baseEnd_322794 : Nat := 73665988616673466973557

theorem tailTrace_322794 : CollatzResearch.WordTrace tailWord_322794 prefixEnd_322794 73665988616673466973557 := by
  unfold tailWord_322794
  simp only [CollatzResearch.WordTrace]
  refine ⟨2943316098144985417819859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7848842928386627780852957 2943316098144985417819859)
  ·
    refine ⟨4414974147217478126729789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2943316098144985417819859 4414974147217478126729789)
    ·
      refine ⟨1655615305206554297523671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4414974147217478126729789 1655615305206554297523671)
      ·
        refine ⟨2483422957809831446285507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1655615305206554297523671 2483422957809831446285507)
        ·
          refine ⟨3725134436714747169428261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2483422957809831446285507 3725134436714747169428261)
          ·
            refine ⟨698462706884015094267799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3725134436714747169428261 698462706884015094267799)
            ·
              refine ⟨1047694060326022641401699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 698462706884015094267799 1047694060326022641401699)
              ·
                refine ⟨1571541090489033962102549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1047694060326022641401699 1571541090489033962102549)
                ·
                  refine ⟨73665988616673466973557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1571541090489033962102549 73665988616673466973557)
                  ·
                    rfl

theorem cell21_322794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 4, 1, 1, 6].length) (baseStart_322794 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_322794 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_322794 prefixEnd_322794 := by exact prefixLift 322794
  have htrace : WordTrace (prefixWord ++ tailWord_322794) baseStart_322794 baseEnd_322794 := by
    simpa [prefixWord, tailWord_322794, baseEnd_322794] using wordTrace_append hprefix tailTrace_322794
  have hstable : (prefixWord ++ tailWord_322794).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_322794).length < 2 ^ (prefixWord ++ tailWord_322794).sum := by decide
  have hdescent : baseEnd_322794 < baseStart_322794 := by decide
  rcases family_descends (prefixWord ++ tailWord_322794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_322797 : List Nat := [1, 5, 1, 2, 2, 1, 2, 4, 3]
def baseStart_322797 : Nat := 118140960795 + 322797 * 2 ^ 59
def prefixEnd_322797 : Nat := 4983230072969 + 3 ^ 40 * 322797 * 2
def baseEnd_322797 : Nat := 73666673257546128423551

theorem tailTrace_322797 : CollatzResearch.WordTrace tailWord_322797 prefixEnd_322797 73666673257546128423551 := by
  unfold tailWord_322797
  simp only [CollatzResearch.WordTrace]
  refine ⟨11773373811569073183638645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7848915874379382122425763 11773373811569073183638645)
  ·
    refine ⟨1103753794834600610966123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 11773373811569073183638645 1103753794834600610966123)
    ·
      refine ⟨1655630692251900916449185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1103753794834600610966123 1655630692251900916449185)
      ·
        refine ⟨1241723019188925687336889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1655630692251900916449185 1241723019188925687336889)
        ·
          refine ⟨931292264391694265502667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1241723019188925687336889 931292264391694265502667)
          ·
            refine ⟨1396938396587541398254001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 931292264391694265502667 1396938396587541398254001)
            ·
              refine ⟨1047703797440656048690501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1396938396587541398254001 1047703797440656048690501)
              ·
                refine ⟨196444462020123009129469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1047703797440656048690501 196444462020123009129469)
                ·
                  refine ⟨73666673257546128423551, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 196444462020123009129469 73666673257546128423551)
                  ·
                    rfl

theorem cell21_322797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 2, 4, 3].length) (baseStart_322797 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_322797 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_322797 prefixEnd_322797 := by exact prefixLift 322797
  have htrace : WordTrace (prefixWord ++ tailWord_322797) baseStart_322797 baseEnd_322797 := by
    simpa [prefixWord, tailWord_322797, baseEnd_322797] using wordTrace_append hprefix tailTrace_322797
  have hstable : (prefixWord ++ tailWord_322797).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_322797).length < 2 ^ (prefixWord ++ tailWord_322797).sum := by decide
  have hdescent : baseEnd_322797 < baseStart_322797 := by decide
  rcases family_descends (prefixWord ++ tailWord_322797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_322856 : List Nat := [2, 1, 5, 1, 2, 1, 3, 1, 5]
def baseStart_322856 : Nat := 118140960795 + 322856 * 2 ^ 59
def prefixEnd_322856 : Nat := 4983230072969 + 3 ^ 40 * 322856 * 2
def baseEnd_322856 : Nat := 73680137861375136940097

theorem tailTrace_322856 : CollatzResearch.WordTrace tailWord_322856 prefixEnd_322856 73680137861375136940097 := by
  unfold tailWord_322856
  simp only [CollatzResearch.WordTrace]
  refine ⟨5887762859177663130018211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7850350478903550840024281 5887762859177663130018211)
  ·
    refine ⟨8831644288766494695027317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5887762859177663130018211 8831644288766494695027317)
    ·
      refine ⟨827966652071858877658811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 8831644288766494695027317 827966652071858877658811)
      ·
        refine ⟨1241949978107788316488217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 827966652071858877658811 1241949978107788316488217)
        ·
          refine ⟨931462483580841237366163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1241949978107788316488217 931462483580841237366163)
          ·
            refine ⟨1397193725371261856049245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 931462483580841237366163 1397193725371261856049245)
            ·
              refine ⟨523947647014223196018467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1397193725371261856049245 523947647014223196018467)
              ·
                refine ⟨785921470521334794027701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 523947647014223196018467 785921470521334794027701)
                ·
                  refine ⟨73680137861375136940097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 785921470521334794027701 73680137861375136940097)
                  ·
                    rfl

theorem cell21_322856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 3, 1, 5].length) (baseStart_322856 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_322856 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_322856 prefixEnd_322856 := by exact prefixLift 322856
  have htrace : WordTrace (prefixWord ++ tailWord_322856) baseStart_322856 baseEnd_322856 := by
    simpa [prefixWord, tailWord_322856, baseEnd_322856] using wordTrace_append hprefix tailTrace_322856
  have hstable : (prefixWord ++ tailWord_322856).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_322856).length < 2 ^ (prefixWord ++ tailWord_322856).sum := by decide
  have hdescent : baseEnd_322856 < baseStart_322856 := by decide
  rcases family_descends (prefixWord ++ tailWord_322856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_323005 : List Nat := [1, 4, 1, 2, 2, 1, 1, 1, 8]
def baseStart_323005 : Nat := 118140960795 + 323005 * 2 ^ 59
def prefixEnd_323005 : Nat := 4983230072969 + 3 ^ 40 * 323005 * 2
def baseEnd_323005 : Nat := 73714141691383988956459

theorem tailTrace_323005 : CollatzResearch.WordTrace tailWord_323005 prefixEnd_323005 73714141691383988956459 := by
  unfold tailWord_323005
  simp only [CollatzResearch.WordTrace]
  refine ⟨11780960194815524707210469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7853973463210349804806979 11780960194815524707210469)
  ·
    refine ⟨2208930036527910882601963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11780960194815524707210469 2208930036527910882601963)
    ·
      refine ⟨3313395054791866323902945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2208930036527910882601963 3313395054791866323902945)
      ·
        refine ⟨2485046291093899742927209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3313395054791866323902945 2485046291093899742927209)
        ·
          refine ⟨1863784718320424807195407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2485046291093899742927209 1863784718320424807195407)
          ·
            refine ⟨2795677077480637210793111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1863784718320424807195407 2795677077480637210793111)
            ·
              refine ⟨4193515616220955816189667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2795677077480637210793111 4193515616220955816189667)
              ·
                refine ⟨6290273424331433724284501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4193515616220955816189667 6290273424331433724284501)
                ·
                  refine ⟨73714141691383988956459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 6290273424331433724284501 73714141691383988956459)
                  ·
                    rfl

theorem cell21_323005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 1, 1, 8].length) (baseStart_323005 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_323005 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_323005 prefixEnd_323005 := by exact prefixLift 323005
  have htrace : WordTrace (prefixWord ++ tailWord_323005) baseStart_323005 baseEnd_323005 := by
    simpa [prefixWord, tailWord_323005, baseEnd_323005] using wordTrace_append hprefix tailTrace_323005
  have hstable : (prefixWord ++ tailWord_323005).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_323005).length < 2 ^ (prefixWord ++ tailWord_323005).sum := by decide
  have hdescent : baseEnd_323005 < baseStart_323005 := by decide
  rcases family_descends (prefixWord ++ tailWord_323005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_323008 : List Nat := [2, 1, 1, 2, 3, 1, 5, 3, 3]
def baseStart_323008 : Nat := 118140960795 + 323008 * 2 ^ 59
def prefixEnd_323008 : Nat := 4983230072969 + 3 ^ 40 * 323008 * 2
def baseEnd_323008 : Nat := 73714826332256650406453

theorem tailTrace_323008 : CollatzResearch.WordTrace tailWord_323008 prefixEnd_323008 73714826332256650406453 := by
  unfold tailWord_323008
  simp only [CollatzResearch.WordTrace]
  refine ⟨5890534806902328109784839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7854046409203104146379785 5890534806902328109784839)
  ·
    refine ⟨8835802210353492164677259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5890534806902328109784839 8835802210353492164677259)
    ·
      refine ⟨13253703315530238247015889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8835802210353492164677259 13253703315530238247015889)
      ·
        refine ⟨9940277486647678685261917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13253703315530238247015889 9940277486647678685261917)
        ·
          refine ⟨3727604057492879506973219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9940277486647678685261917 3727604057492879506973219)
          ·
            refine ⟨5591406086239319260459829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3727604057492879506973219 5591406086239319260459829)
            ·
              refine ⟨524194320584936180668109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5591406086239319260459829 524194320584936180668109)
              ·
                refine ⟨196572870219351067750541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 524194320584936180668109 196572870219351067750541)
                ·
                  refine ⟨73714826332256650406453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 196572870219351067750541 73714826332256650406453)
                  ·
                    rfl

theorem cell21_323008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 5, 3, 3].length) (baseStart_323008 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_323008 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_323008 prefixEnd_323008 := by exact prefixLift 323008
  have htrace : WordTrace (prefixWord ++ tailWord_323008) baseStart_323008 baseEnd_323008 := by
    simpa [prefixWord, tailWord_323008, baseEnd_323008] using wordTrace_append hprefix tailTrace_323008
  have hstable : (prefixWord ++ tailWord_323008).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_323008).length < 2 ^ (prefixWord ++ tailWord_323008).sum := by decide
  have hdescent : baseEnd_323008 < baseStart_323008 := by decide
  rcases family_descends (prefixWord ++ tailWord_323008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_323019 : List Nat := [1, 1, 1, 1, 3, 3, 11]
def baseStart_323019 : Nat := 118140960795 + 323019 * 2 ^ 59
def prefixEnd_323019 : Nat := 4983230072969 + 3 ^ 40 * 323019 * 2
def baseEnd_323019 : Nat := 8190815186902563969233

theorem tailTrace_323019 : CollatzResearch.WordTrace tailWord_323019 prefixEnd_323019 8190815186902563969233 := by
  unfold tailWord_323019
  simp only [CollatzResearch.WordTrace]
  refine ⟨11781470816764805098220111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7854313877843203398813407 11781470816764805098220111)
  ·
    refine ⟨17672206225147207647330167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11781470816764805098220111 17672206225147207647330167)
    ·
      refine ⟨26508309337720811470995251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17672206225147207647330167 26508309337720811470995251)
      ·
        refine ⟨39762464006581217206492877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26508309337720811470995251 39762464006581217206492877)
        ·
          refine ⟨14910924002467956452434829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39762464006581217206492877 14910924002467956452434829)
          ·
            refine ⟨5591596500925483669663061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14910924002467956452434829 5591596500925483669663061)
            ·
              refine ⟨8190815186902563969233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 5591596500925483669663061 8190815186902563969233)
              ·
                rfl

theorem cell21_323019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 11].length) (baseStart_323019 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_323019 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_323019 prefixEnd_323019 := by exact prefixLift 323019
  have htrace : WordTrace (prefixWord ++ tailWord_323019) baseStart_323019 baseEnd_323019 := by
    simpa [prefixWord, tailWord_323019, baseEnd_323019] using wordTrace_append hprefix tailTrace_323019
  have hstable : (prefixWord ++ tailWord_323019).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_323019).length < 2 ^ (prefixWord ++ tailWord_323019).sum := by decide
  have hdescent : baseEnd_323019 < baseStart_323019 := by decide
  rcases family_descends (prefixWord ++ tailWord_323019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_323070 : List Nat := [4, 2, 2, 3, 2, 8]
def baseStart_323070 : Nat := 118140960795 + 323070 * 2 ^ 59
def prefixEnd_323070 : Nat := 4983230072969 + 3 ^ 40 * 323070 * 2
def baseEnd_323070 : Nat := 2730702799146604458259

theorem tailTrace_323070 : CollatzResearch.WordTrace tailWord_323070 prefixEnd_323070 2730702799146604458259 := by
  unfold tailWord_323070
  simp only [CollatzResearch.WordTrace]
  refine ⟨1472916367447505101040833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7855553959720027205551109 1472916367447505101040833)
  ·
    refine ⟨1104687275585628825780625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1472916367447505101040833 1104687275585628825780625)
    ·
      refine ⟨828515456689221619335469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1104687275585628825780625 828515456689221619335469)
      ·
        refine ⟨310693296258458107250801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 828515456689221619335469 310693296258458107250801)
        ·
          refine ⟨233019972193843580438101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 310693296258458107250801 233019972193843580438101)
          ·
            refine ⟨2730702799146604458259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 233019972193843580438101 2730702799146604458259)
            ·
              rfl

theorem cell21_323070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 2, 8].length) (baseStart_323070 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_323070 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_323070 prefixEnd_323070 := by exact prefixLift 323070
  have htrace : WordTrace (prefixWord ++ tailWord_323070) baseStart_323070 baseEnd_323070 := by
    simpa [prefixWord, tailWord_323070, baseEnd_323070] using wordTrace_append hprefix tailTrace_323070
  have hstable : (prefixWord ++ tailWord_323070).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_323070).length < 2 ^ (prefixWord ++ tailWord_323070).sum := by decide
  have hdescent : baseEnd_323070 < baseStart_323070 := by decide
  rcases family_descends (prefixWord ++ tailWord_323070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_323132 : List Nat := [2, 2, 2, 2, 5, 1, 1, 2, 4]
def baseStart_323132 : Nat := 118140960795 + 323132 * 2 ^ 59
def prefixEnd_323132 : Nat := 4983230072969 + 3 ^ 40 * 323132 * 2
def baseEnd_323132 : Nat := 73743124821659990339533

theorem tailTrace_323132 : CollatzResearch.WordTrace tailWord_323132 prefixEnd_323132 73743124821659990339533 := by
  unfold tailWord_323132
  simp only [CollatzResearch.WordTrace]
  refine ⟨5892796132677712698541825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7857061510236950264722433 5892796132677712698541825)
  ·
    refine ⟨4419597099508284523906369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5892796132677712698541825 4419597099508284523906369)
    ·
      refine ⟨3314697824631213392929777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4419597099508284523906369 3314697824631213392929777)
      ·
        refine ⟨2486023368473410044697333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3314697824631213392929777 2486023368473410044697333)
        ·
          refine ⟨233064690794382191690375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 2486023368473410044697333 233064690794382191690375)
          ·
            refine ⟨349597036191573287535563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 233064690794382191690375 349597036191573287535563)
            ·
              refine ⟨524395554287359931303345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 349597036191573287535563 524395554287359931303345)
              ·
                refine ⟨393296665715519948477509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 524395554287359931303345 393296665715519948477509)
                ·
                  refine ⟨73743124821659990339533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 393296665715519948477509 73743124821659990339533)
                  ·
                    rfl

theorem cell21_323132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 5, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 5, 1, 1, 2, 4].length) (baseStart_323132 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_323132 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_323132 prefixEnd_323132 := by exact prefixLift 323132
  have htrace : WordTrace (prefixWord ++ tailWord_323132) baseStart_323132 baseEnd_323132 := by
    simpa [prefixWord, tailWord_323132, baseEnd_323132] using wordTrace_append hprefix tailTrace_323132
  have hstable : (prefixWord ++ tailWord_323132).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_323132).length < 2 ^ (prefixWord ++ tailWord_323132).sum := by decide
  have hdescent : baseEnd_323132 < baseStart_323132 := by decide
  rcases family_descends (prefixWord ++ tailWord_323132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_323253 : List Nat := [1, 3, 3, 3, 2, 1, 1, 4, 3]
def baseStart_323253 : Nat := 118140960795 + 323253 * 2 ^ 59
def prefixEnd_323253 : Nat := 4983230072969 + 3 ^ 40 * 323253 * 2
def baseEnd_323253 : Nat := 73770738670190668822619

theorem tailTrace_323253 : CollatzResearch.WordTrace tailWord_323253 prefixEnd_323253 73770738670190668822619 := by
  unfold tailWord_323253
  simp only [CollatzResearch.WordTrace]
  refine ⟨11790005497917063062238413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7860003665278042041492275 11790005497917063062238413)
  ·
    refine ⟨4421252061718898648339405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11790005497917063062238413 4421252061718898648339405)
    ·
      refine ⟨1657969523144586993127277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4421252061718898648339405 1657969523144586993127277)
      ·
        refine ⟨621738571179220122422729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1657969523144586993127277 621738571179220122422729)
        ·
          refine ⟨466303928384415091817047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 621738571179220122422729 466303928384415091817047)
          ·
            refine ⟨699455892576622637725571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 466303928384415091817047 699455892576622637725571)
            ·
              refine ⟨1049183838864933956588357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 699455892576622637725571 1049183838864933956588357)
              ·
                refine ⟨196721969787175116860317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1049183838864933956588357 196721969787175116860317)
                ·
                  refine ⟨73770738670190668822619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 196721969787175116860317 73770738670190668822619)
                  ·
                    rfl

theorem cell21_323253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 1, 1, 4, 3].length) (baseStart_323253 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_323253 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_323253 prefixEnd_323253 := by exact prefixLift 323253
  have htrace : WordTrace (prefixWord ++ tailWord_323253) baseStart_323253 baseEnd_323253 := by
    simpa [prefixWord, tailWord_323253, baseEnd_323253] using wordTrace_append hprefix tailTrace_323253
  have hstable : (prefixWord ++ tailWord_323253).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_323253).length < 2 ^ (prefixWord ++ tailWord_323253).sum := by decide
  have hdescent : baseEnd_323253 < baseStart_323253 := by decide
  rcases family_descends (prefixWord ++ tailWord_323253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_323340 : List Nat := [2, 2, 1, 2, 2, 1, 6, 5]
def baseStart_323340 : Nat := 118140960795 + 323340 * 2 ^ 59
def prefixEnd_323340 : Nat := 4983230072969 + 3 ^ 40 * 323340 * 2
def baseEnd_323340 : Nat := 24596864418499283624147

theorem tailTrace_323340 : CollatzResearch.WordTrace tailWord_323340 prefixEnd_323340 24596864418499283624147 := by
  unfold tailWord_323340
  simp only [CollatzResearch.WordTrace]
  refine ⟨5896589324300938460327737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7862119099067917947103649 5896589324300938460327737)
  ·
    refine ⟨4422441993225703845245803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5896589324300938460327737 4422441993225703845245803)
    ·
      refine ⟨6633662989838555767868705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4422441993225703845245803 6633662989838555767868705)
      ·
        refine ⟨4975247242378916825901529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6633662989838555767868705 4975247242378916825901529)
        ·
          refine ⟨3731435431784187619426147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4975247242378916825901529 3731435431784187619426147)
          ·
            refine ⟨5597153147676281429139221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3731435431784187619426147 5597153147676281429139221)
            ·
              refine ⟨262366553797325691990901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 5597153147676281429139221 262366553797325691990901)
              ·
                refine ⟨24596864418499283624147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 262366553797325691990901 24596864418499283624147)
                ·
                  rfl

theorem cell21_323340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 6, 5].length) (baseStart_323340 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_323340 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_323340 prefixEnd_323340 := by exact prefixLift 323340
  have htrace : WordTrace (prefixWord ++ tailWord_323340) baseStart_323340 baseEnd_323340 := by
    simpa [prefixWord, tailWord_323340, baseEnd_323340] using wordTrace_append hprefix tailTrace_323340
  have hstable : (prefixWord ++ tailWord_323340).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_323340).length < 2 ^ (prefixWord ++ tailWord_323340).sum := by decide
  have hdescent : baseEnd_323340 < baseStart_323340 := by decide
  rcases family_descends (prefixWord ++ tailWord_323340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_323346 : List Nat := [3, 2, 4, 1, 1, 3, 1, 3, 3]
def baseStart_323346 : Nat := 118140960795 + 323346 * 2 ^ 59
def prefixEnd_323346 : Nat := 4983230072969 + 3 ^ 40 * 323346 * 2
def baseEnd_323346 : Nat := 73791962537243173772429

theorem tailTrace_323346 : CollatzResearch.WordTrace tailWord_323346 prefixEnd_323346 73791962537243173772429 := by
  unfold tailWord_323346
  simp only [CollatzResearch.WordTrace]
  refine ⟨2948349371645034986343473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7862264991053426630249261 2948349371645034986343473)
  ·
    refine ⟨2211262028733776239757605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2948349371645034986343473 2211262028733776239757605)
    ·
      refine ⟨414611630387583044954551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2211262028733776239757605 414611630387583044954551)
      ·
        refine ⟨621917445581374567431827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 414611630387583044954551 621917445581374567431827)
        ·
          refine ⟨932876168372061851147741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 621917445581374567431827 932876168372061851147741)
          ·
            refine ⟨349828563139523194180403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 932876168372061851147741 349828563139523194180403)
            ·
              refine ⟨524742844709284791270605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 349828563139523194180403 524742844709284791270605)
              ·
                refine ⟨196778566765981796726477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 524742844709284791270605 196778566765981796726477)
                ·
                  refine ⟨73791962537243173772429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 196778566765981796726477 73791962537243173772429)
                  ·
                    rfl

theorem cell21_323346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 3, 1, 3, 3].length) (baseStart_323346 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_323346 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_323346 prefixEnd_323346 := by exact prefixLift 323346
  have htrace : WordTrace (prefixWord ++ tailWord_323346) baseStart_323346 baseEnd_323346 := by
    simpa [prefixWord, tailWord_323346, baseEnd_323346] using wordTrace_append hprefix tailTrace_323346
  have hstable : (prefixWord ++ tailWord_323346).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_323346).length < 2 ^ (prefixWord ++ tailWord_323346).sum := by decide
  have hdescent : baseEnd_323346 < baseStart_323346 := by decide
  rcases family_descends (prefixWord ++ tailWord_323346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_323399 : List Nat := [1, 1, 4, 1, 2, 1, 4, 7]
def baseStart_323399 : Nat := 118140960795 + 323399 * 2 ^ 59
def prefixEnd_323399 : Nat := 4983230072969 + 3 ^ 40 * 323399 * 2
def baseEnd_323399 : Nat := 24601352619775619796329

theorem tailTrace_323399 : CollatzResearch.WordTrace tailWord_323399 prefixEnd_323399 24601352619775619796329 := by
  unfold tailWord_323399
  simp only [CollatzResearch.WordTrace]
  refine ⟨11795330555388129997053251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7863553703592086664702167 11795330555388129997053251)
  ·
    refine ⟨17692995833082194995579877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11795330555388129997053251 17692995833082194995579877)
    ·
      refine ⟨3317436718702911561671227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17692995833082194995579877 3317436718702911561671227)
      ·
        refine ⟨4976155078054367342506841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3317436718702911561671227 4976155078054367342506841)
        ·
          refine ⟨3732116308540775506880131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4976155078054367342506841 3732116308540775506880131)
          ·
            refine ⟨5598174462811163260320197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3732116308540775506880131 5598174462811163260320197)
            ·
              refine ⟨1049657711777093111310037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5598174462811163260320197 1049657711777093111310037)
              ·
                refine ⟨24601352619775619796329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1049657711777093111310037 24601352619775619796329)
                ·
                  rfl

theorem cell21_323399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 4, 7].length) (baseStart_323399 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_323399 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_323399 prefixEnd_323399 := by exact prefixLift 323399
  have htrace : WordTrace (prefixWord ++ tailWord_323399) baseStart_323399 baseEnd_323399 := by
    simpa [prefixWord, tailWord_323399, baseEnd_323399] using wordTrace_append hprefix tailTrace_323399
  have hstable : (prefixWord ++ tailWord_323399).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_323399).length < 2 ^ (prefixWord ++ tailWord_323399).sum := by decide
  have hdescent : baseEnd_323399 < baseStart_323399 := by decide
  rcases family_descends (prefixWord ++ tailWord_323399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_323495 : List Nat := [1, 1, 6, 1, 2, 2, 3, 1, 4]
def baseStart_323495 : Nat := 118140960795 + 323495 * 2 ^ 59
def prefixEnd_323495 : Nat := 4983230072969 + 3 ^ 40 * 323495 * 2
def baseEnd_323495 : Nat := 73825966367252025788791

theorem tailTrace_323495 : CollatzResearch.WordTrace tailWord_323495 prefixEnd_323495 73825966367252025788791 := by
  unfold tailWord_323495
  simp only [CollatzResearch.WordTrace]
  refine ⟨11798831963040338392547939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7865887975360225595031959 11798831963040338392547939)
  ·
    refine ⟨17698247944560507588821909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11798831963040338392547939 17698247944560507588821909)
    ·
      refine ⟨829605372401273793226027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 17698247944560507588821909 829605372401273793226027)
      ·
        refine ⟨1244408058601910689839041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 829605372401273793226027 1244408058601910689839041)
        ·
          refine ⟨933306043951433017379281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1244408058601910689839041 933306043951433017379281)
          ·
            refine ⟨699979532963574763034461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 933306043951433017379281 699979532963574763034461)
            ·
              refine ⟨262492324861340536137923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 699979532963574763034461 262492324861340536137923)
              ·
                refine ⟨393738487292010804206885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 262492324861340536137923 393738487292010804206885)
                ·
                  refine ⟨73825966367252025788791, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 393738487292010804206885 73825966367252025788791)
                  ·
                    rfl

theorem cell21_323495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 2, 3, 1, 4].length) (baseStart_323495 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_323495 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_323495 prefixEnd_323495 := by exact prefixLift 323495
  have htrace : WordTrace (prefixWord ++ tailWord_323495) baseStart_323495 baseEnd_323495 := by
    simpa [prefixWord, tailWord_323495, baseEnd_323495] using wordTrace_append hprefix tailTrace_323495
  have hstable : (prefixWord ++ tailWord_323495).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_323495).length < 2 ^ (prefixWord ++ tailWord_323495).sum := by decide
  have hdescent : baseEnd_323495 < baseStart_323495 := by decide
  rcases family_descends (prefixWord ++ tailWord_323495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_323509 : List Nat := [1, 3, 3, 2, 1, 4, 2, 5]
def baseStart_323509 : Nat := 118140960795 + 323509 * 2 ^ 59
def prefixEnd_323509 : Nat := 4983230072969 + 3 ^ 40 * 323509 * 2
def baseEnd_323509 : Nat := 24609720452663704185143

theorem tailTrace_323509 : CollatzResearch.WordTrace tailWord_323509 prefixEnd_323509 24609720452663704185143 := by
  unfold tailWord_323509
  simp only [CollatzResearch.WordTrace]
  refine ⟨11799342584989618783557581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7866228389993079189038387 11799342584989618783557581)
  ·
    refine ⟨4424753469371107043834093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11799342584989618783557581 4424753469371107043834093)
    ·
      refine ⟨1659282551014165141437785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4424753469371107043834093 1659282551014165141437785)
      ·
        refine ⟨1244461913260623856078339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1659282551014165141437785 1244461913260623856078339)
        ·
          refine ⟨1866692869890935784117509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1244461913260623856078339 1866692869890935784117509)
          ·
            refine ⟨350004913104550459522033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1866692869890935784117509 350004913104550459522033)
            ·
              refine ⟨262503684828412844641525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 350004913104550459522033 262503684828412844641525)
              ·
                refine ⟨24609720452663704185143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 262503684828412844641525 24609720452663704185143)
                ·
                  rfl

theorem cell21_323509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 4, 2, 5].length) (baseStart_323509 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_323509 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_323509 prefixEnd_323509 := by exact prefixLift 323509
  have htrace : WordTrace (prefixWord ++ tailWord_323509) baseStart_323509 baseEnd_323509 := by
    simpa [prefixWord, tailWord_323509, baseEnd_323509] using wordTrace_append hprefix tailTrace_323509
  have hstable : (prefixWord ++ tailWord_323509).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_323509).length < 2 ^ (prefixWord ++ tailWord_323509).sum := by decide
  have hdescent : baseEnd_323509 < baseStart_323509 := by decide
  rcases family_descends (prefixWord ++ tailWord_323509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_323520 : List Nat := [2, 1, 1, 2, 3, 2, 1, 1, 8]
def baseStart_323520 : Nat := 118140960795 + 323520 * 2 ^ 59
def prefixEnd_323520 : Nat := 4983230072969 + 3 ^ 40 * 323520 * 2
def baseEnd_323520 : Nat := 73831671707857537872073

theorem tailTrace_323520 : CollatzResearch.WordTrace tailWord_323520 prefixEnd_323520 73831671707857537872073 := by
  unfold tailWord_323520
  simp only [CollatzResearch.WordTrace]
  refine ⟨5899871893974883831104007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7866495858633178441472009 5899871893974883831104007)
  ·
    refine ⟨8849807840962325746656011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5899871893974883831104007 8849807840962325746656011)
    ·
      refine ⟨13274711761443488619984017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8849807840962325746656011 13274711761443488619984017)
      ·
        refine ⟨9956033821082616464988013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13274711761443488619984017 9956033821082616464988013)
        ·
          refine ⟨3733512682905981174370505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9956033821082616464988013 3733512682905981174370505)
          ·
            refine ⟨2800134512179485880777879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3733512682905981174370505 2800134512179485880777879)
            ·
              refine ⟨4200201768269228821166819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2800134512179485880777879 4200201768269228821166819)
              ·
                refine ⟨6300302652403843231750229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4200201768269228821166819 6300302652403843231750229)
                ·
                  refine ⟨73831671707857537872073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 6300302652403843231750229 73831671707857537872073)
                  ·
                    rfl

theorem cell21_323520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 1, 1, 8].length) (baseStart_323520 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_323520 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_323520 prefixEnd_323520 := by exact prefixLift 323520
  have htrace : WordTrace (prefixWord ++ tailWord_323520) baseStart_323520 baseEnd_323520 := by
    simpa [prefixWord, tailWord_323520, baseEnd_323520] using wordTrace_append hprefix tailTrace_323520
  have hstable : (prefixWord ++ tailWord_323520).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_323520).length < 2 ^ (prefixWord ++ tailWord_323520).sum := by decide
  have hdescent : baseEnd_323520 < baseStart_323520 := by decide
  rcases family_descends (prefixWord ++ tailWord_323520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_323551 : List Nat := [1, 1, 2, 3, 4, 1, 1, 8]
def baseStart_323551 : Nat := 118140960795 + 323551 * 2 ^ 59
def prefixEnd_323551 : Nat := 4983230072969 + 3 ^ 40 * 323551 * 2
def baseEnd_323551 : Nat := 24612915443402790951781

theorem tailTrace_323551 : CollatzResearch.WordTrace tailWord_323551 prefixEnd_323551 24612915443402790951781 := by
  unfold tailWord_323551
  simp only [CollatzResearch.WordTrace]
  refine ⟨11800874450837459956586507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7867249633891639971057671 11800874450837459956586507)
  ·
    refine ⟨17701311676256189934879761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11800874450837459956586507 17701311676256189934879761)
    ·
      refine ⟨13275983757192142451159821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17701311676256189934879761 13275983757192142451159821)
      ·
        refine ⟨4978493908947053419184933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13275983757192142451159821 4978493908947053419184933)
        ·
          refine ⟨933467607927572516097175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4978493908947053419184933 933467607927572516097175)
          ·
            refine ⟨1400201411891358774145763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 933467607927572516097175 1400201411891358774145763)
            ·
              refine ⟨2100302117837038161218645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1400201411891358774145763 2100302117837038161218645)
              ·
                refine ⟨24612915443402790951781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2100302117837038161218645 24612915443402790951781)
                ·
                  rfl

theorem cell21_323551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 1, 8].length) (baseStart_323551 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_323551 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_323551 prefixEnd_323551 := by exact prefixLift 323551
  have htrace : WordTrace (prefixWord ++ tailWord_323551) baseStart_323551 baseEnd_323551 := by
    simpa [prefixWord, tailWord_323551, baseEnd_323551] using wordTrace_append hprefix tailTrace_323551
  have hstable : (prefixWord ++ tailWord_323551).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_323551).length < 2 ^ (prefixWord ++ tailWord_323551).sum := by decide
  have hdescent : baseEnd_323551 < baseStart_323551 := by decide
  rcases family_descends (prefixWord ++ tailWord_323551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_323678 : List Nat := [4, 4, 1, 1, 2, 1, 1, 7]
def baseStart_323678 : Nat := 118140960795 + 323678 * 2 ^ 59
def prefixEnd_323678 : Nat := 4983230072969 + 3 ^ 40 * 323678 * 2
def baseEnd_323678 : Nat := 24622576486828124746139

theorem tailTrace_323678 : CollatzResearch.WordTrace tailWord_323678 prefixEnd_323678 24622576486828124746139 := by
  unfold tailWord_323678
  simp only [CollatzResearch.WordTrace]
  refine ⟨1475688315172170080807461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7870337680918240430973125 1475688315172170080807461)
  ·
    refine ⟨276691559094781890151399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1475688315172170080807461 276691559094781890151399)
    ·
      refine ⟨415037338642172835227099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 276691559094781890151399 415037338642172835227099)
      ·
        refine ⟨622556007963259252840649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 415037338642172835227099 622556007963259252840649)
        ·
          refine ⟨466917005972444439630487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 622556007963259252840649 466917005972444439630487)
          ·
            refine ⟨700375508958666659445731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 466917005972444439630487 700375508958666659445731)
            ·
              refine ⟨1050563263437999989168597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 700375508958666659445731 1050563263437999989168597)
              ·
                refine ⟨24622576486828124746139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1050563263437999989168597 24622576486828124746139)
                ·
                  rfl

theorem cell21_323678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 1, 1, 7].length) (baseStart_323678 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_323678 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_323678 prefixEnd_323678 := by exact prefixLift 323678
  have htrace : WordTrace (prefixWord ++ tailWord_323678) baseStart_323678 baseEnd_323678 := by
    simpa [prefixWord, tailWord_323678, baseEnd_323678] using wordTrace_append hprefix tailTrace_323678
  have hstable : (prefixWord ++ tailWord_323678).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_323678).length < 2 ^ (prefixWord ++ tailWord_323678).sum := by decide
  have hdescent : baseEnd_323678 < baseStart_323678 := by decide
  rcases family_descends (prefixWord ++ tailWord_323678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_323692 : List Nat := [2, 2, 1, 1, 3, 5, 1, 3, 3]
def baseStart_323692 : Nat := 118140960795 + 323692 * 2 ^ 59
def prefixEnd_323692 : Nat := 4983230072969 + 3 ^ 40 * 323692 * 2
def baseEnd_323692 : Nat := 73870924451223461005055

theorem tailTrace_323692 : CollatzResearch.WordTrace tailWord_323692 prefixEnd_323692 73870924451223461005055 := by
  unfold tailWord_323692
  simp only [CollatzResearch.WordTrace]
  refine ⟨5903008571663320518734665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7870678095551094024979553 5903008571663320518734665)
  ·
    refine ⟨4427256428747490389050999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5903008571663320518734665 4427256428747490389050999)
    ·
      refine ⟨6640884643121235583576499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4427256428747490389050999 6640884643121235583576499)
      ·
        refine ⟨9961326964681853375364749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6640884643121235583576499 9961326964681853375364749)
        ·
          refine ⟨3735497611755695015761781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9961326964681853375364749 3735497611755695015761781)
          ·
            refine ⟨350202901102096407727667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 3735497611755695015761781 350202901102096407727667)
            ·
              refine ⟨525304351653144611591501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 350202901102096407727667 525304351653144611591501)
              ·
                refine ⟨196989131869929229346813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 525304351653144611591501 196989131869929229346813)
                ·
                  refine ⟨73870924451223461005055, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 196989131869929229346813 73870924451223461005055)
                  ·
                    rfl

theorem cell21_323692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 5, 1, 3, 3].length) (baseStart_323692 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_323692 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_323692 prefixEnd_323692 := by exact prefixLift 323692
  have htrace : WordTrace (prefixWord ++ tailWord_323692) baseStart_323692 baseEnd_323692 := by
    simpa [prefixWord, tailWord_323692, baseEnd_323692] using wordTrace_append hprefix tailTrace_323692
  have hstable : (prefixWord ++ tailWord_323692).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_323692).length < 2 ^ (prefixWord ++ tailWord_323692).sum := by decide
  have hdescent : baseEnd_323692 < baseStart_323692 := by decide
  rcases family_descends (prefixWord ++ tailWord_323692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_323703 : List Nat := [1, 1, 3, 1, 1, 7, 7]
def baseStart_323703 : Nat := 118140960795 + 323703 * 2 ^ 59
def prefixEnd_323703 : Nat := 4983230072969 + 3 ^ 40 * 323703 * 2
def baseEnd_323703 : Nat := 8208159422343320702411

theorem tailTrace_323703 : CollatzResearch.WordTrace tailWord_323703 prefixEnd_323703 8208159422343320702411 := by
  unfold tailWord_323703
  simp only [CollatzResearch.WordTrace]
  refine ⟨11806418346286789916119763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7870945564191193277413175 11806418346286789916119763)
  ·
    refine ⟨17709627519430184874179645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11806418346286789916119763 17709627519430184874179645)
    ·
      refine ⟨6641110319786319327817367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17709627519430184874179645 6641110319786319327817367)
      ·
        refine ⟨9961665479679478991726051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6641110319786319327817367 9961665479679478991726051)
        ·
          refine ⟨14942498219519218487589077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9961665479679478991726051 14942498219519218487589077)
          ·
            refine ⟨350214802019981683302869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 14942498219519218487589077 350214802019981683302869)
            ·
              refine ⟨8208159422343320702411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 350214802019981683302869 8208159422343320702411)
              ·
                rfl

theorem cell21_323703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 7, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 7, 7].length) (baseStart_323703 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_323703 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_323703 prefixEnd_323703 := by exact prefixLift 323703
  have htrace : WordTrace (prefixWord ++ tailWord_323703) baseStart_323703 baseEnd_323703 := by
    simpa [prefixWord, tailWord_323703, baseEnd_323703] using wordTrace_append hprefix tailTrace_323703
  have hstable : (prefixWord ++ tailWord_323703).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_323703).length < 2 ^ (prefixWord ++ tailWord_323703).sum := by decide
  have hdescent : baseEnd_323703 < baseStart_323703 := by decide
  rcases family_descends (prefixWord ++ tailWord_323703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_323720 : List Nat := [2, 1, 3, 4, 1, 2, 2, 6]
def baseStart_323720 : Nat := 118140960795 + 323720 * 2 ^ 59
def prefixEnd_323720 : Nat := 4983230072969 + 3 ^ 40 * 323720 * 2
def baseEnd_323720 : Nat := 24625771477567211512777

theorem tailTrace_323720 : CollatzResearch.WordTrace tailWord_323720 prefixEnd_323720 24625771477567211512777 := by
  unfold tailWord_323720
  simp only [CollatzResearch.WordTrace]
  refine ⟨5903519193612600909744307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7871358924816801212992409 5903519193612600909744307)
  ·
    refine ⟨8855278790418901364616461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5903519193612600909744307 8855278790418901364616461)
    ·
      refine ⟨3320729546407088011731173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8855278790418901364616461 3320729546407088011731173)
      ·
        refine ⟨622636789951329002199595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3320729546407088011731173 622636789951329002199595)
        ·
          refine ⟨933955184926993503299393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 622636789951329002199595 933955184926993503299393)
          ·
            refine ⟨700466388695245127474545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 933955184926993503299393 700466388695245127474545)
            ·
              refine ⟨525349791521433845605909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 700466388695245127474545 525349791521433845605909)
              ·
                refine ⟨24625771477567211512777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 525349791521433845605909 24625771477567211512777)
                ·
                  rfl

theorem cell21_323720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 2, 2, 6].length) (baseStart_323720 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_323720 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_323720 prefixEnd_323720 := by exact prefixLift 323720
  have htrace : WordTrace (prefixWord ++ tailWord_323720) baseStart_323720 baseEnd_323720 := by
    simpa [prefixWord, tailWord_323720, baseEnd_323720] using wordTrace_append hprefix tailTrace_323720
  have hstable : (prefixWord ++ tailWord_323720).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_323720).length < 2 ^ (prefixWord ++ tailWord_323720).sum := by decide
  have hdescent : baseEnd_323720 < baseStart_323720 := by decide
  rcases family_descends (prefixWord ++ tailWord_323720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_323793 : List Nat := [1, 2, 2, 1, 2, 2, 3, 1, 7]
def baseStart_323793 : Nat := 118140960795 + 323793 * 2 ^ 59
def prefixEnd_323793 : Nat := 4983230072969 + 3 ^ 40 * 323793 * 2
def baseEnd_323793 : Nat := 73893974027269729821515

theorem tailTrace_323793 : CollatzResearch.WordTrace tailWord_323793 prefixEnd_323793 73893974027269729821515 := by
  unfold tailWord_323793
  simp only [CollatzResearch.WordTrace]
  refine ⟨11809700915960735286896033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7873133943973823524597355 11809700915960735286896033)
  ·
    refine ⟨8857275686970551465172025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11809700915960735286896033 8857275686970551465172025)
    ·
      refine ⟨6642956765227913598879019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8857275686970551465172025 6642956765227913598879019)
      ·
        refine ⟨9964435147841870398318529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6642956765227913598879019 9964435147841870398318529)
        ·
          refine ⟨7473326360881402798738897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9964435147841870398318529 7473326360881402798738897)
          ·
            refine ⟨5604994770661052099054173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7473326360881402798738897 5604994770661052099054173)
            ·
              refine ⟨2101873038997894537145315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5604994770661052099054173 2101873038997894537145315)
              ·
                refine ⟨3152809558496841805717973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2101873038997894537145315 3152809558496841805717973)
                ·
                  refine ⟨73893974027269729821515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3152809558496841805717973 73893974027269729821515)
                  ·
                    rfl

theorem cell21_323793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 3, 1, 7].length) (baseStart_323793 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_323793 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_323793 prefixEnd_323793 := by exact prefixLift 323793
  have htrace : WordTrace (prefixWord ++ tailWord_323793) baseStart_323793 baseEnd_323793 := by
    simpa [prefixWord, tailWord_323793, baseEnd_323793] using wordTrace_append hprefix tailTrace_323793
  have hstable : (prefixWord ++ tailWord_323793).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_323793).length < 2 ^ (prefixWord ++ tailWord_323793).sum := by decide
  have hdescent : baseEnd_323793 < baseStart_323793 := by decide
  rcases family_descends (prefixWord ++ tailWord_323793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_323945 : List Nat := [1, 2, 1, 1, 1, 3, 4, 3, 5]
def baseStart_323945 : Nat := 118140960795 + 323945 * 2 ^ 59
def prefixEnd_323945 : Nat := 4983230072969 + 3 ^ 40 * 323945 * 2
def baseEnd_323945 : Nat := 73928662498151243287871

theorem tailTrace_323945 : CollatzResearch.WordTrace tailWord_323945 prefixEnd_323945 73928662498151243287871 := by
  unfold tailWord_323945
  simp only [CollatzResearch.WordTrace]
  refine ⟨11815244811410065246429289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7876829874273376830952859 11815244811410065246429289)
  ·
    refine ⟨8861433608557548934821967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11815244811410065246429289 8861433608557548934821967)
    ·
      refine ⟨13292150412836323402232951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8861433608557548934821967 13292150412836323402232951)
      ·
        refine ⟨19938225619254485103349427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13292150412836323402232951 19938225619254485103349427)
        ·
          refine ⟨29907338428881727655024141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19938225619254485103349427 29907338428881727655024141)
          ·
            refine ⟨11215251910830647870634053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29907338428881727655024141 11215251910830647870634053)
            ·
              refine ⟨2102859733280746475743885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11215251910830647870634053 2102859733280746475743885)
              ·
                refine ⟨788572399980279928403957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2102859733280746475743885 788572399980279928403957)
                ·
                  refine ⟨73928662498151243287871, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 788572399980279928403957 73928662498151243287871)
                  ·
                    rfl

theorem cell21_323945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 4, 3, 5].length) (baseStart_323945 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_323945 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_323945 prefixEnd_323945 := by exact prefixLift 323945
  have htrace : WordTrace (prefixWord ++ tailWord_323945) baseStart_323945 baseEnd_323945 := by
    simpa [prefixWord, tailWord_323945, baseEnd_323945] using wordTrace_append hprefix tailTrace_323945
  have hstable : (prefixWord ++ tailWord_323945).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_323945).length < 2 ^ (prefixWord ++ tailWord_323945).sum := by decide
  have hdescent : baseEnd_323945 < baseStart_323945 := by decide
  rcases family_descends (prefixWord ++ tailWord_323945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_323948 : List Nat := [2, 2, 1, 1, 6, 2, 1, 6]
def baseStart_323948 : Nat := 118140960795 + 323948 * 2 ^ 59
def prefixEnd_323948 : Nat := 4983230072969 + 3 ^ 40 * 323948 * 2
def baseEnd_323948 : Nat := 24643115713007968245955

theorem tailTrace_323948 : CollatzResearch.WordTrace tailWord_323948 prefixEnd_323948 24643115713007968245955 := by
  unfold tailWord_323948
  simp only [CollatzResearch.WordTrace]
  refine ⟨5907677115199598379394249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7876902820266131172525665 5907677115199598379394249)
  ·
    refine ⟨4430757836399698784545687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5907677115199598379394249 4430757836399698784545687)
    ·
      refine ⟨6646136754599548176818531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4430757836399698784545687 6646136754599548176818531)
      ·
        refine ⟨9969205131899322265227797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6646136754599548176818531 9969205131899322265227797)
        ·
          refine ⟨467306490557780731182553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 9969205131899322265227797 467306490557780731182553)
          ·
            refine ⟨350479867918335548386915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 467306490557780731182553 350479867918335548386915)
            ·
              refine ⟨525719801877503322580373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 350479867918335548386915 525719801877503322580373)
              ·
                refine ⟨24643115713007968245955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 525719801877503322580373 24643115713007968245955)
                ·
                  rfl

theorem cell21_323948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 2, 1, 6].length) (baseStart_323948 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_323948 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_323948 prefixEnd_323948 := by exact prefixLift 323948
  have htrace : WordTrace (prefixWord ++ tailWord_323948) baseStart_323948 baseEnd_323948 := by
    simpa [prefixWord, tailWord_323948, baseEnd_323948] using wordTrace_append hprefix tailTrace_323948
  have hstable : (prefixWord ++ tailWord_323948).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_323948).length < 2 ^ (prefixWord ++ tailWord_323948).sum := by decide
  have hdescent : baseEnd_323948 < baseStart_323948 := by decide
  rcases family_descends (prefixWord ++ tailWord_323948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_323976 : List Nat := [2, 1, 3, 3, 1, 1, 2, 2, 6]
def baseStart_323976 : Nat := 118140960795 + 323976 * 2 ^ 59
def prefixEnd_323976 : Nat := 4983230072969 + 3 ^ 40 * 323976 * 2
def baseEnd_323976 : Nat := 73935737120502078271141

theorem tailTrace_323976 : CollatzResearch.WordTrace tailWord_323976 prefixEnd_323976 73935737120502078271141 := by
  unfold tailWord_323976
  simp only [CollatzResearch.WordTrace]
  refine ⟨5908187737148878770403891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7877583649531838360538521 5908187737148878770403891)
  ·
    refine ⟨8862281605723318155605837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5908187737148878770403891 8862281605723318155605837)
    ·
      refine ⟨3323355602146244308352189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8862281605723318155605837 3323355602146244308352189)
      ·
        refine ⟨1246258350804841615632071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3323355602146244308352189 1246258350804841615632071)
        ·
          refine ⟨1869387526207262423448107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1246258350804841615632071 1869387526207262423448107)
          ·
            refine ⟨2804081289310893635172161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1869387526207262423448107 2804081289310893635172161)
            ·
              refine ⟨2103060966983170226379121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2804081289310893635172161 2103060966983170226379121)
              ·
                refine ⟨1577295725237377669784341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2103060966983170226379121 1577295725237377669784341)
                ·
                  refine ⟨73935737120502078271141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1577295725237377669784341 73935737120502078271141)
                  ·
                    rfl

theorem cell21_323976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 2, 2, 6].length) (baseStart_323976 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_323976 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_323976 prefixEnd_323976 := by exact prefixLift 323976
  have htrace : WordTrace (prefixWord ++ tailWord_323976) baseStart_323976 baseEnd_323976 := by
    simpa [prefixWord, tailWord_323976, baseEnd_323976] using wordTrace_append hprefix tailTrace_323976
  have hstable : (prefixWord ++ tailWord_323976).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_323976).length < 2 ^ (prefixWord ++ tailWord_323976).sum := by decide
  have hdescent : baseEnd_323976 < baseStart_323976 := by decide
  rcases family_descends (prefixWord ++ tailWord_323976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_323979 : List Nat := [1, 1, 1, 1, 4, 5, 2, 3, 3]
def baseStart_323979 : Nat := 118140960795 + 323979 * 2 ^ 59
def prefixEnd_323979 : Nat := 4983230072969 + 3 ^ 40 * 323979 * 2
def baseEnd_323979 : Nat := 73936421761374739721135

theorem tailTrace_323979 : CollatzResearch.WordTrace tailWord_323979 prefixEnd_323979 73936421761374739721135 := by
  unfold tailWord_323979
  simp only [CollatzResearch.WordTrace]
  refine ⟨11816484893286889053166991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7877656595524592702111327 11816484893286889053166991)
  ·
    refine ⟨17724727339930333579750487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11816484893286889053166991 17724727339930333579750487)
    ·
      refine ⟨26587091009895500369625731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17724727339930333579750487 26587091009895500369625731)
      ·
        refine ⟨39880636514843250554438597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26587091009895500369625731 39880636514843250554438597)
        ·
          refine ⟨7477619346533109478957237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 39880636514843250554438597 7477619346533109478957237)
          ·
            refine ⟨701026813737479013652241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 7477619346533109478957237 701026813737479013652241)
            ·
              refine ⟨525770110303109260239181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 701026813737479013652241 525770110303109260239181)
              ·
                refine ⟨197163791363665972589693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 525770110303109260239181 197163791363665972589693)
                ·
                  refine ⟨73936421761374739721135, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 197163791363665972589693 73936421761374739721135)
                  ·
                    rfl

theorem cell21_323979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 5, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 5, 2, 3, 3].length) (baseStart_323979 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_323979 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_323979 prefixEnd_323979 := by exact prefixLift 323979
  have htrace : WordTrace (prefixWord ++ tailWord_323979) baseStart_323979 baseEnd_323979 := by
    simpa [prefixWord, tailWord_323979, baseEnd_323979] using wordTrace_append hprefix tailTrace_323979
  have hstable : (prefixWord ++ tailWord_323979).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_323979).length < 2 ^ (prefixWord ++ tailWord_323979).sum := by decide
  have hdescent : baseEnd_323979 < baseStart_323979 := by decide
  rcases family_descends (prefixWord ++ tailWord_323979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_324311 : List Nat := [1, 1, 3, 2, 1, 5, 3, 5]
def baseStart_324311 : Nat := 118140960795 + 324311 * 2 ^ 59
def prefixEnd_324311 : Nat := 4983230072969 + 3 ^ 40 * 324311 * 2
def baseEnd_324311 : Nat := 24670729561538646729041

theorem tailTrace_324311 : CollatzResearch.WordTrace tailWord_324311 prefixEnd_324311 24670729561538646729041 := by
  unfold tailWord_324311
  simp only [CollatzResearch.WordTrace]
  refine ⟨11828593928084109754252787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7885729285389406502835191 11828593928084109754252787)
  ·
    refine ⟨17742890892126164631379181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11828593928084109754252787 17742890892126164631379181)
    ·
      refine ⟨6653584084547311736767193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17742890892126164631379181 6653584084547311736767193)
      ·
        refine ⟨4990188063410483802575395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6653584084547311736767193 4990188063410483802575395)
        ·
          refine ⟨7485282095115725703863093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4990188063410483802575395 7485282095115725703863093)
          ·
            refine ⟨701745196417099284737165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 7485282095115725703863093 701745196417099284737165)
            ·
              refine ⟨263154448656412231776437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 701745196417099284737165 263154448656412231776437)
              ·
                refine ⟨24670729561538646729041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 263154448656412231776437 24670729561538646729041)
                ·
                  rfl

theorem cell21_324311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 5, 3, 5].length) (baseStart_324311 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_324311 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_324311 prefixEnd_324311 := by exact prefixLift 324311
  have htrace : WordTrace (prefixWord ++ tailWord_324311) baseStart_324311 baseEnd_324311 := by
    simpa [prefixWord, tailWord_324311, baseEnd_324311] using wordTrace_append hprefix tailTrace_324311
  have hstable : (prefixWord ++ tailWord_324311).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_324311).length < 2 ^ (prefixWord ++ tailWord_324311).sum := by decide
  have hdescent : baseEnd_324311 < baseStart_324311 := by decide
  rcases family_descends (prefixWord ++ tailWord_324311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_324342 : List Nat := [5, 1, 1, 1, 1, 2, 4, 1, 5]
def baseStart_324342 : Nat := 118140960795 + 324342 * 2 ^ 59
def prefixEnd_324342 : Nat := 4983230072969 + 3 ^ 40 * 324342 * 2
def baseEnd_324342 : Nat := 74019263306966775170393

theorem tailTrace_324342 : CollatzResearch.WordTrace tailWord_324342 prefixEnd_324342 74019263306966775170393 := by
  unfold tailWord_324342
  simp only [CollatzResearch.WordTrace]
  refine ⟨739357786935737628039455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 7886483060647868032420853 739357786935737628039455)
  ·
    refine ⟨1109036680403606442059183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 739357786935737628039455 1109036680403606442059183)
    ·
      refine ⟨1663555020605409663088775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1109036680403606442059183 1663555020605409663088775)
      ·
        refine ⟨2495332530908114494633163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1663555020605409663088775 2495332530908114494633163)
        ·
          refine ⟨3742998796362171741949745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2495332530908114494633163 3742998796362171741949745)
          ·
            refine ⟨2807249097271628806462309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3742998796362171741949745 2807249097271628806462309)
            ·
              refine ⟨526359205738430401211683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2807249097271628806462309 526359205738430401211683)
              ·
                refine ⟨789538808607645601817525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 526359205738430401211683 789538808607645601817525)
                ·
                  refine ⟨74019263306966775170393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 789538808607645601817525 74019263306966775170393)
                  ·
                    rfl

theorem cell21_324342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 4, 1, 5].length) (baseStart_324342 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_324342 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_324342 prefixEnd_324342 := by exact prefixLift 324342
  have htrace : WordTrace (prefixWord ++ tailWord_324342) baseStart_324342 baseEnd_324342 := by
    simpa [prefixWord, tailWord_324342, baseEnd_324342] using wordTrace_append hprefix tailTrace_324342
  have hstable : (prefixWord ++ tailWord_324342).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_324342).length < 2 ^ (prefixWord ++ tailWord_324342).sum := by decide
  have hdescent : baseEnd_324342 < baseStart_324342 := by decide
  rcases family_descends (prefixWord ++ tailWord_324342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_324404 : List Nat := [2, 5, 1, 1, 3, 1, 2, 6]
def baseStart_324404 : Nat := 118140960795 + 324404 * 2 ^ 59
def prefixEnd_324404 : Nat := 4983230072969 + 3 ^ 40 * 324404 * 2
def baseEnd_324404 : Nat := 24677804183889481712311

theorem tailTrace_324404 : CollatzResearch.WordTrace tailWord_324404 prefixEnd_324404 24677804183889481712311 := by
  unfold tailWord_324404
  simp only [CollatzResearch.WordTrace]
  refine ⟨5915992958373593318694133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7887990611164791091592177 5915992958373593318694133)
  ·
    refine ⟨554624339847524373627575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 5915992958373593318694133 554624339847524373627575)
    ·
      refine ⟨831936509771286560441363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 554624339847524373627575 831936509771286560441363)
      ·
        refine ⟨1247904764656929840662045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 831936509771286560441363 1247904764656929840662045)
        ·
          refine ⟨467964286746348690248267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1247904764656929840662045 467964286746348690248267)
          ·
            refine ⟨701946430119523035372401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 467964286746348690248267 701946430119523035372401)
            ·
              refine ⟨526459822589642276529301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 701946430119523035372401 526459822589642276529301)
              ·
                refine ⟨24677804183889481712311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 526459822589642276529301 24677804183889481712311)
                ·
                  rfl

theorem cell21_324404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 1, 2, 6].length) (baseStart_324404 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_324404 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_324404 prefixEnd_324404 := by exact prefixLift 324404
  have htrace : WordTrace (prefixWord ++ tailWord_324404) baseStart_324404 baseEnd_324404 := by
    simpa [prefixWord, tailWord_324404, baseEnd_324404] using wordTrace_append hprefix tailTrace_324404
  have hstable : (prefixWord ++ tailWord_324404).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_324404).length < 2 ^ (prefixWord ++ tailWord_324404).sum := by decide
  have hdescent : baseEnd_324404 < baseStart_324404 := by decide
  rcases family_descends (prefixWord ++ tailWord_324404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_324452 : List Nat := [2, 3, 1, 1, 4, 3, 2, 2, 3]
def baseStart_324452 : Nat := 118140960795 + 324452 * 2 ^ 59
def prefixEnd_324452 : Nat := 4983230072969 + 3 ^ 40 * 324452 * 2
def baseEnd_324452 : Nat := 74044366805631028336835

theorem tailTrace_324452 : CollatzResearch.WordTrace tailWord_324452 prefixEnd_324452 74044366805631028336835 := by
  unfold tailWord_324452
  simp only [CollatzResearch.WordTrace]
  refine ⟨5916868310286645417567805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7889157747048860556757073 5916868310286645417567805)
  ·
    refine ⟨2218825616357492031587927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5916868310286645417567805 2218825616357492031587927)
    ·
      refine ⟨3328238424536238047381891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2218825616357492031587927 3328238424536238047381891)
      ·
        refine ⟨4992357636804357071072837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3328238424536238047381891 4992357636804357071072837)
        ·
          refine ⟨936067056900816950826157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4992357636804357071072837 936067056900816950826157)
          ·
            refine ⟨351025146337806356559809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 936067056900816950826157 351025146337806356559809)
            ·
              refine ⟨263268859753354767419857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 351025146337806356559809 263268859753354767419857)
              ·
                refine ⟨197451644815016075564893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 263268859753354767419857 197451644815016075564893)
                ·
                  refine ⟨74044366805631028336835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 197451644815016075564893 74044366805631028336835)
                  ·
                    rfl

theorem cell21_324452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 3, 2, 2, 3].length) (baseStart_324452 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_324452 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_324452 prefixEnd_324452 := by exact prefixLift 324452
  have htrace : WordTrace (prefixWord ++ tailWord_324452) baseStart_324452 baseEnd_324452 := by
    simpa [prefixWord, tailWord_324452, baseEnd_324452] using wordTrace_append hprefix tailTrace_324452
  have hstable : (prefixWord ++ tailWord_324452).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_324452).length < 2 ^ (prefixWord ++ tailWord_324452).sum := by decide
  have hdescent : baseEnd_324452 < baseStart_324452 := by decide
  rcases family_descends (prefixWord ++ tailWord_324452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_324570 : List Nat := [3, 1, 1, 2, 4, 3, 1, 1, 5]
def baseStart_324570 : Nat := 118140960795 + 324570 * 2 ^ 59
def prefixEnd_324570 : Nat := 4983230072969 + 3 ^ 40 * 324570 * 2
def baseEnd_324570 : Nat := 74071296013289045369927

theorem tailTrace_324570 : CollatzResearch.WordTrace tailWord_324570 prefixEnd_324570 74071296013289045369927 := by
  unfold tailWord_324570
  simp only [CollatzResearch.WordTrace]
  refine ⟨2959510108536449246982791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7892026956097197991954109 2959510108536449246982791)
  ·
    refine ⟨4439265162804673870474187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2959510108536449246982791 4439265162804673870474187)
    ·
      refine ⟨6658897744207010805711281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4439265162804673870474187 6658897744207010805711281)
      ·
        refine ⟨4994173308155258104283461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6658897744207010805711281 4994173308155258104283461)
        ·
          refine ⟨936407495279110894553149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4994173308155258104283461 936407495279110894553149)
          ·
            refine ⟨351152810729666585457431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 936407495279110894553149 351152810729666585457431)
            ·
              refine ⟨526729216094499878186147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 351152810729666585457431 526729216094499878186147)
              ·
                refine ⟨790093824141749817279221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 526729216094499878186147 790093824141749817279221)
                ·
                  refine ⟨74071296013289045369927, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 790093824141749817279221 74071296013289045369927)
                  ·
                    rfl

theorem cell21_324570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 5].length) (baseStart_324570 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_324570 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_324570 prefixEnd_324570 := by exact prefixLift 324570
  have htrace : WordTrace (prefixWord ++ tailWord_324570) baseStart_324570 baseEnd_324570 := by
    simpa [prefixWord, tailWord_324570, baseEnd_324570] using wordTrace_append hprefix tailTrace_324570
  have hstable : (prefixWord ++ tailWord_324570).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_324570).length < 2 ^ (prefixWord ++ tailWord_324570).sum := by decide
  have hdescent : baseEnd_324570 < baseStart_324570 := by decide
  rcases family_descends (prefixWord ++ tailWord_324570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_324750 : List Nat := [4, 1, 1, 3, 2, 1, 1, 8]
def baseStart_324750 : Nat := 118140960795 + 324750 * 2 ^ 59
def prefixEnd_324750 : Nat := 4983230072969 + 3 ^ 40 * 324750 * 2
def baseEnd_324750 : Nat := 24704124821882910789853

theorem tailTrace_324750 : CollatzResearch.WordTrace tailWord_324750 prefixEnd_324750 24704124821882910789853 := by
  unfold tailWord_324750
  simp only [CollatzResearch.WordTrace]
  refine ⟨1480575696686710966185463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7896403715662458486322469 1480575696686710966185463)
  ·
    refine ⟨2220863545030066449278195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1480575696686710966185463 2220863545030066449278195)
    ·
      refine ⟨3331295317545099673917293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2220863545030066449278195 3331295317545099673917293)
      ·
        refine ⟨1249235744079412377718985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3331295317545099673917293 1249235744079412377718985)
        ·
          refine ⟨936926808059559283289239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1249235744079412377718985 936926808059559283289239)
          ·
            refine ⟨1405390212089338924933859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 936926808059559283289239 1405390212089338924933859)
            ·
              refine ⟨2108085318134008387400789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1405390212089338924933859 2108085318134008387400789)
              ·
                refine ⟨24704124821882910789853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2108085318134008387400789 24704124821882910789853)
                ·
                  rfl

theorem cell21_324750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 1, 8].length) (baseStart_324750 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_324750 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_324750 prefixEnd_324750 := by exact prefixLift 324750
  have htrace : WordTrace (prefixWord ++ tailWord_324750) baseStart_324750 baseEnd_324750 := by
    simpa [prefixWord, tailWord_324750, baseEnd_324750] using wordTrace_append hprefix tailTrace_324750
  have hstable : (prefixWord ++ tailWord_324750).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_324750).length < 2 ^ (prefixWord ++ tailWord_324750).sum := by decide
  have hdescent : baseEnd_324750 < baseStart_324750 := by decide
  rcases family_descends (prefixWord ++ tailWord_324750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_324790 : List Nat := [5, 1, 3, 2, 1, 2, 2, 2, 3]
def baseStart_324790 : Nat := 118140960795 + 324790 * 2 ^ 59
def prefixEnd_324790 : Nat := 4983230072969 + 3 ^ 40 * 324790 * 2
def baseEnd_324790 : Nat := 74121503010617551702811

theorem tailTrace_324790 : CollatzResearch.WordTrace tailWord_324790 prefixEnd_324790 74121503010617551702811 := by
  unfold tailWord_324790
  simp only [CollatzResearch.WordTrace]
  refine ⟨740379030834298410058739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 7897376328899183040626549 740379030834298410058739)
  ·
    refine ⟨1110568546251447615088109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 740379030834298410058739 1110568546251447615088109)
    ·
      refine ⟨416463204844292855658041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1110568546251447615088109 416463204844292855658041)
      ·
        refine ⟨312347403633219641743531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 416463204844292855658041 312347403633219641743531)
        ·
          refine ⟨468521105449829462615297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 312347403633219641743531 468521105449829462615297)
          ·
            refine ⟨351390829087372096961473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 468521105449829462615297 351390829087372096961473)
            ·
              refine ⟨263543121815529072721105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 351390829087372096961473 263543121815529072721105)
              ·
                refine ⟨197657341361646804540829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 263543121815529072721105 197657341361646804540829)
                ·
                  refine ⟨74121503010617551702811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 197657341361646804540829 74121503010617551702811)
                  ·
                    rfl

theorem cell21_324790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 2, 2, 2, 3].length) (baseStart_324790 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_324790 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_324790 prefixEnd_324790 := by exact prefixLift 324790
  have htrace : WordTrace (prefixWord ++ tailWord_324790) baseStart_324790 baseEnd_324790 := by
    simpa [prefixWord, tailWord_324790, baseEnd_324790] using wordTrace_append hprefix tailTrace_324790
  have hstable : (prefixWord ++ tailWord_324790).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_324790).length < 2 ^ (prefixWord ++ tailWord_324790).sum := by decide
  have hdescent : baseEnd_324790 < baseStart_324790 := by decide
  rcases family_descends (prefixWord ++ tailWord_324790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_324840 : List Nat := [2, 1, 4, 1, 2, 1, 1, 2, 7]
def baseStart_324840 : Nat := 118140960795 + 324840 * 2 ^ 59
def prefixEnd_324840 : Nat := 4983230072969 + 3 ^ 40 * 324840 * 2
def baseEnd_324840 : Nat := 74132913691828575869375

theorem tailTrace_324840 : CollatzResearch.WordTrace tailWord_324840 prefixEnd_324840 74132913691828575869375 := by
  unfold tailWord_324840
  simp only [CollatzResearch.WordTrace]
  refine ⟨5923944071583816550129987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7898592095445088733506649 5923944071583816550129987)
  ·
    refine ⟨8885916107375724825194981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5923944071583816550129987 8885916107375724825194981)
    ·
      refine ⟨1666109270132948404724059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8885916107375724825194981 1666109270132948404724059)
      ·
        refine ⟨2499163905199422607086089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1666109270132948404724059 2499163905199422607086089)
        ·
          refine ⟨1874372928899566955314567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2499163905199422607086089 1874372928899566955314567)
          ·
            refine ⟨2811559393349350432971851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1874372928899566955314567 2811559393349350432971851)
            ·
              refine ⟨4217339090024025649457777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2811559393349350432971851 4217339090024025649457777)
              ·
                refine ⟨3163004317518019237093333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4217339090024025649457777 3163004317518019237093333)
                ·
                  refine ⟨74132913691828575869375, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3163004317518019237093333 74132913691828575869375)
                  ·
                    rfl

theorem cell21_324840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 1, 2, 7].length) (baseStart_324840 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_324840 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_324840 prefixEnd_324840 := by exact prefixLift 324840
  have htrace : WordTrace (prefixWord ++ tailWord_324840) baseStart_324840 baseEnd_324840 := by
    simpa [prefixWord, tailWord_324840, baseEnd_324840] using wordTrace_append hprefix tailTrace_324840
  have hstable : (prefixWord ++ tailWord_324840).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_324840).length < 2 ^ (prefixWord ++ tailWord_324840).sum := by decide
  have hdescent : baseEnd_324840 < baseStart_324840 := by decide
  rcases family_descends (prefixWord ++ tailWord_324840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_324857 : List Nat := [1, 2, 1, 3, 1, 1, 3, 6, 3]
def baseStart_324857 : Nat := 118140960795 + 324857 * 2 ^ 59
def prefixEnd_324857 : Nat := 4983230072969 + 3 ^ 40 * 324857 * 2
def baseEnd_324857 : Nat := 74136793323440324086007

theorem tailTrace_324857 : CollatzResearch.WordTrace tailWord_324857 prefixEnd_324857 74136793323440324086007 := by
  unfold tailWord_324857
  simp only [CollatzResearch.WordTrace]
  refine ⟨11848508184106045003628825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7899005456070696669085883 11848508184106045003628825)
  ·
    refine ⟨8886381138079533752721619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11848508184106045003628825 8886381138079533752721619)
    ·
      refine ⟨13329571707119300629082429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8886381138079533752721619 13329571707119300629082429)
      ·
        refine ⟨4998589390169737735905911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13329571707119300629082429 4998589390169737735905911)
        ·
          refine ⟨7497884085254606603858867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4998589390169737735905911 7497884085254606603858867)
          ·
            refine ⟨11246826127881909905788301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7497884085254606603858867 11246826127881909905788301)
            ·
              refine ⟨4217559797955716214670613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11246826127881909905788301 4217559797955716214670613)
              ·
                refine ⟨197698115529174197562685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 4217559797955716214670613 197698115529174197562685)
                ·
                  refine ⟨74136793323440324086007, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 197698115529174197562685 74136793323440324086007)
                  ·
                    rfl

theorem cell21_324857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 3, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 3, 6, 3].length) (baseStart_324857 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_324857 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_324857 prefixEnd_324857 := by exact prefixLift 324857
  have htrace : WordTrace (prefixWord ++ tailWord_324857) baseStart_324857 baseEnd_324857 := by
    simpa [prefixWord, tailWord_324857, baseEnd_324857] using wordTrace_append hprefix tailTrace_324857
  have hstable : (prefixWord ++ tailWord_324857).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_324857).length < 2 ^ (prefixWord ++ tailWord_324857).sum := by decide
  have hdescent : baseEnd_324857 < baseStart_324857 := by decide
  rcases family_descends (prefixWord ++ tailWord_324857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_324964 : List Nat := [2, 3, 1, 1, 3, 3, 2, 2, 4]
def baseStart_324964 : Nat := 118140960795 + 324964 * 2 ^ 59
def prefixEnd_324964 : Nat := 4983230072969 + 3 ^ 40 * 324964 * 2
def baseEnd_324964 : Nat := 74161212181231915802455

theorem tailTrace_324964 : CollatzResearch.WordTrace tailWord_324964 prefixEnd_324964 74161212181231915802455 := by
  unfold tailWord_324964
  simp only [CollatzResearch.WordTrace]
  refine ⟨5926205397359201138886973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7901607196478934851849297 5926205397359201138886973)
  ·
    refine ⟨2222327024009700427082615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5926205397359201138886973 2222327024009700427082615)
    ·
      refine ⟨3333490536014550640623923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2222327024009700427082615 3333490536014550640623923)
      ·
        refine ⟨5000235804021825960935885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3333490536014550640623923 5000235804021825960935885)
        ·
          refine ⟨1875088426508184735350957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5000235804021825960935885 1875088426508184735350957)
          ·
            refine ⟨703158159940569275756609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1875088426508184735350957 703158159940569275756609)
            ·
              refine ⟨527368619955426956817457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 703158159940569275756609 527368619955426956817457)
              ·
                refine ⟨395526464966570217613093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 527368619955426956817457 395526464966570217613093)
                ·
                  refine ⟨74161212181231915802455, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 395526464966570217613093 74161212181231915802455)
                  ·
                    rfl

theorem cell21_324964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 3, 2, 2, 4].length) (baseStart_324964 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_324964 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_324964 prefixEnd_324964 := by exact prefixLift 324964
  have htrace : WordTrace (prefixWord ++ tailWord_324964) baseStart_324964 baseEnd_324964 := by
    simpa [prefixWord, tailWord_324964, baseEnd_324964] using wordTrace_append hprefix tailTrace_324964
  have hstable : (prefixWord ++ tailWord_324964).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_324964).length < 2 ^ (prefixWord ++ tailWord_324964).sum := by decide
  have hdescent : baseEnd_324964 < baseStart_324964 := by decide
  rcases family_descends (prefixWord ++ tailWord_324964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_325023 : List Nat := [1, 1, 2, 5, 1, 3, 1, 1, 6]
def baseStart_325023 : Nat := 118140960795 + 325023 * 2 ^ 59
def prefixEnd_325023 : Nat := 4983230072969 + 3 ^ 40 * 325023 * 2
def baseEnd_325023 : Nat := 74174676785060924319001

theorem tailTrace_325023 : CollatzResearch.WordTrace tailWord_325023 prefixEnd_325023 74174676785060924319001 := by
  unfold tailWord_325023
  simp only [CollatzResearch.WordTrace]
  refine ⟨11854562701504655354171723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7903041801003103569447815 11854562701504655354171723)
  ·
    refine ⟨17781844052256983031257585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11854562701504655354171723 17781844052256983031257585)
    ·
      refine ⟨13336383039192737273443189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17781844052256983031257585 13336383039192737273443189)
      ·
        refine ⟨1250285909924319119385299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 13336383039192737273443189 1250285909924319119385299)
        ·
          refine ⟨1875428864886478679077949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1250285909924319119385299 1875428864886478679077949)
          ·
            refine ⟨703285824332429504654231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1875428864886478679077949 703285824332429504654231)
            ·
              refine ⟨1054928736498644256981347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 703285824332429504654231 1054928736498644256981347)
              ·
                refine ⟨1582393104747966385472021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1054928736498644256981347 1582393104747966385472021)
                ·
                  refine ⟨74174676785060924319001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1582393104747966385472021 74174676785060924319001)
                  ·
                    rfl

theorem cell21_325023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 3, 1, 1, 6].length) (baseStart_325023 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_325023 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_325023 prefixEnd_325023 := by exact prefixLift 325023
  have htrace : WordTrace (prefixWord ++ tailWord_325023) baseStart_325023 baseEnd_325023 := by
    simpa [prefixWord, tailWord_325023, baseEnd_325023] using wordTrace_append hprefix tailTrace_325023
  have hstable : (prefixWord ++ tailWord_325023).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_325023).length < 2 ^ (prefixWord ++ tailWord_325023).sum := by decide
  have hdescent : baseEnd_325023 < baseStart_325023 := by decide
  rcases family_descends (prefixWord ++ tailWord_325023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_325026 : List Nat := [3, 3, 1, 2, 1, 2, 2, 4, 3]
def baseStart_325026 : Nat := 118140960795 + 325026 * 2 ^ 59
def prefixEnd_325026 : Nat := 4983230072969 + 3 ^ 40 * 325026 * 2
def baseEnd_325026 : Nat := 74175361425933585768995

theorem tailTrace_325026 : CollatzResearch.WordTrace tailWord_325026 prefixEnd_325026 74175361425933585768995 := by
  unfold tailWord_325026
  simp only [CollatzResearch.WordTrace]
  refine ⟨2963668030123446716632733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7903114746995857911020621 2963668030123446716632733)
  ·
    refine ⟨1111375511296292518737275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2963668030123446716632733 1111375511296292518737275)
    ·
      refine ⟨1667063266944438778105913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1111375511296292518737275 1667063266944438778105913)
      ·
        refine ⟨1250297450208329083579435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1667063266944438778105913 1250297450208329083579435)
        ·
          refine ⟨1875446175312493625369153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1250297450208329083579435 1875446175312493625369153)
          ·
            refine ⟨1406584631484370219026865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1875446175312493625369153 1406584631484370219026865)
            ·
              refine ⟨1054938473613277664270149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1406584631484370219026865 1054938473613277664270149)
              ·
                refine ⟨197800963802489562050653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1054938473613277664270149 197800963802489562050653)
                ·
                  refine ⟨74175361425933585768995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 197800963802489562050653 74175361425933585768995)
                  ·
                    rfl

theorem cell21_325026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 2, 4, 3].length) (baseStart_325026 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_325026 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_325026 prefixEnd_325026 := by exact prefixLift 325026
  have htrace : WordTrace (prefixWord ++ tailWord_325026) baseStart_325026 baseEnd_325026 := by
    simpa [prefixWord, tailWord_325026, baseEnd_325026] using wordTrace_append hprefix tailTrace_325026
  have hstable : (prefixWord ++ tailWord_325026).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_325026).length < 2 ^ (prefixWord ++ tailWord_325026).sum := by decide
  have hdescent : baseEnd_325026 < baseStart_325026 := by decide
  rcases family_descends (prefixWord ++ tailWord_325026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_325085 : List Nat := [1, 4, 3, 1, 1, 2, 3, 1, 5]
def baseStart_325085 : Nat := 118140960795 + 325085 * 2 ^ 59
def prefixEnd_325085 : Nat := 4983230072969 + 3 ^ 40 * 325085 * 2
def baseEnd_325085 : Nat := 74188826029762594285541

theorem tailTrace_325085 : CollatzResearch.WordTrace tailWord_325085 prefixEnd_325085 74188826029762594285541 := by
  unfold tailWord_325085
  simp only [CollatzResearch.WordTrace]
  refine ⟨11856824027280039942928709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7904549351520026628619139 11856824027280039942928709)
  ·
    refine ⟨2223154505115007489299133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11856824027280039942928709 2223154505115007489299133)
    ·
      refine ⟨833682939418127808487175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2223154505115007489299133 833682939418127808487175)
      ·
        refine ⟨1250524409127191712730763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 833682939418127808487175 1250524409127191712730763)
        ·
          refine ⟨1875786613690787569096145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1250524409127191712730763 1875786613690787569096145)
          ·
            refine ⟨1406839960268090676822109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1875786613690787569096145 1406839960268090676822109)
            ·
              refine ⟨527564985100534003808291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1406839960268090676822109 527564985100534003808291)
              ·
                refine ⟨791347477650801005712437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 527564985100534003808291 791347477650801005712437)
                ·
                  refine ⟨74188826029762594285541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 791347477650801005712437 74188826029762594285541)
                  ·
                    rfl

theorem cell21_325085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 3, 1, 5].length) (baseStart_325085 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_325085 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_325085 prefixEnd_325085 := by exact prefixLift 325085
  have htrace : WordTrace (prefixWord ++ tailWord_325085) baseStart_325085 baseEnd_325085 := by
    simpa [prefixWord, tailWord_325085, baseEnd_325085] using wordTrace_append hprefix tailTrace_325085
  have hstable : (prefixWord ++ tailWord_325085).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_325085).length < 2 ^ (prefixWord ++ tailWord_325085).sum := by decide
  have hdescent : baseEnd_325085 < baseStart_325085 := by decide
  rcases family_descends (prefixWord ++ tailWord_325085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_325220 : List Nat := [2, 3, 1, 1, 2, 3, 2, 2, 5]
def baseStart_325220 : Nat := 118140960795 + 325220 * 2 ^ 59
def prefixEnd_325220 : Nat := 4983230072969 + 3 ^ 40 * 325220 * 2
def baseEnd_325220 : Nat := 74219634869032359535265

theorem tailTrace_325220 : CollatzResearch.WordTrace tailWord_325220 prefixEnd_325220 74219634869032359535265 := by
  unfold tailWord_325220
  simp only [CollatzResearch.WordTrace]
  refine ⟨5930873940895478999546557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7907831921193971999395409 5930873940895478999546557)
  ·
    refine ⟨2224077727835804624829959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5930873940895478999546557 2224077727835804624829959)
    ·
      refine ⟨3336116591753706937244939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2224077727835804624829959 3336116591753706937244939)
      ·
        refine ⟨5004174887630560405867409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3336116591753706937244939 5004174887630560405867409)
        ·
          refine ⟨3753131165722920304400557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5004174887630560405867409 3753131165722920304400557)
          ·
            refine ⟨1407424187146095114150209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3753131165722920304400557 1407424187146095114150209)
            ·
              refine ⟨1055568140359571335612657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1407424187146095114150209 1055568140359571335612657)
              ·
                refine ⟨791676105269678501709493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1055568140359571335612657 791676105269678501709493)
                ·
                  refine ⟨74219634869032359535265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 791676105269678501709493 74219634869032359535265)
                  ·
                    rfl

theorem cell21_325220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 2, 2, 5].length) (baseStart_325220 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_325220 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_325220 prefixEnd_325220 := by exact prefixLift 325220
  have htrace : WordTrace (prefixWord ++ tailWord_325220) baseStart_325220 baseEnd_325220 := by
    simpa [prefixWord, tailWord_325220, baseEnd_325220] using wordTrace_append hprefix tailTrace_325220
  have hstable : (prefixWord ++ tailWord_325220).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_325220).length < 2 ^ (prefixWord ++ tailWord_325220).sum := by decide
  have hdescent : baseEnd_325220 < baseStart_325220 := by decide
  rcases family_descends (prefixWord ++ tailWord_325220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_325372 : List Nat := [2, 2, 2, 1, 3, 1, 4, 1, 5]
def baseStart_325372 : Nat := 118140960795 + 325372 * 2 ^ 59
def prefixEnd_325372 : Nat := 4983230072969 + 3 ^ 40 * 325372 * 2
def baseEnd_325372 : Nat := 74254323339913873001621

theorem tailTrace_325372 : CollatzResearch.WordTrace tailWord_325372 prefixEnd_325372 74254323339913873001621 := by
  unfold tailWord_325372
  simp only [CollatzResearch.WordTrace]
  refine ⟨5933645888620143979313185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7911527851493525305750913 5933645888620143979313185)
  ·
    refine ⟨4450234416465107984484889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5933645888620143979313185 4450234416465107984484889)
    ·
      refine ⟨3337675812348830988363667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4450234416465107984484889 3337675812348830988363667)
      ·
        refine ⟨5006513718523246482545501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3337675812348830988363667 5006513718523246482545501)
        ·
          refine ⟨1877442644446217430954563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5006513718523246482545501 1877442644446217430954563)
          ·
            refine ⟨2816163966669326146431845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1877442644446217430954563 2816163966669326146431845)
            ·
              refine ⟨528030743750498652455971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2816163966669326146431845 528030743750498652455971)
              ·
                refine ⟨792046115625747978683957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 528030743750498652455971 792046115625747978683957)
                ·
                  refine ⟨74254323339913873001621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 792046115625747978683957 74254323339913873001621)
                  ·
                    rfl

theorem cell21_325372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 4, 1, 5].length) (baseStart_325372 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_325372 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_325372 prefixEnd_325372 := by exact prefixLift 325372
  have htrace : WordTrace (prefixWord ++ tailWord_325372) baseStart_325372 baseEnd_325372 := by
    simpa [prefixWord, tailWord_325372, baseEnd_325372] using wordTrace_append hprefix tailTrace_325372
  have hstable : (prefixWord ++ tailWord_325372).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_325372).length < 2 ^ (prefixWord ++ tailWord_325372).sum := by decide
  have hdescent : baseEnd_325372 < baseStart_325372 := by decide
  rcases family_descends (prefixWord ++ tailWord_325372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_325431 : List Nat := [1, 1, 3, 1, 2, 1, 2, 5, 5]
def baseStart_325431 : Nat := 118140960795 + 325431 * 2 ^ 59
def prefixEnd_325431 : Nat := 4983230072969 + 3 ^ 40 * 325431 * 2
def baseEnd_325431 : Nat := 74267787943742881518167

theorem tailTrace_325431 : CollatzResearch.WordTrace tailWord_325431 prefixEnd_325431 74267787943742881518167 := by
  unfold tailWord_325431
  simp only [CollatzResearch.WordTrace]
  refine ⟨11869443684026541035024147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7912962456017694023349431 11869443684026541035024147)
  ·
    refine ⟨17804165526039811552536221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11869443684026541035024147 17804165526039811552536221)
    ·
      refine ⟨6676562072264929332201083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17804165526039811552536221 6676562072264929332201083)
      ·
        refine ⟨10014843108397393998301625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6676562072264929332201083 10014843108397393998301625)
        ·
          refine ⟨7511132331298045498726219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10014843108397393998301625 7511132331298045498726219)
          ·
            refine ⟨11266698496947068248089329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7511132331298045498726219 11266698496947068248089329)
            ·
              refine ⟨8450023872710301186066997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11266698496947068248089329 8450023872710301186066997)
              ·
                refine ⟨792189738066590736193781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8450023872710301186066997 792189738066590736193781)
                ·
                  refine ⟨74267787943742881518167, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 792189738066590736193781 74267787943742881518167)
                  ·
                    rfl

theorem cell21_325431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 5, 5].length) (baseStart_325431 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_325431 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_325431 prefixEnd_325431 := by exact prefixLift 325431
  have htrace : WordTrace (prefixWord ++ tailWord_325431) baseStart_325431 baseEnd_325431 := by
    simpa [prefixWord, tailWord_325431, baseEnd_325431] using wordTrace_append hprefix tailTrace_325431
  have hstable : (prefixWord ++ tailWord_325431).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_325431).length < 2 ^ (prefixWord ++ tailWord_325431).sum := by decide
  have hdescent : baseEnd_325431 < baseStart_325431 := by decide
  rcases family_descends (prefixWord ++ tailWord_325431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_325437 : List Nat := [1, 4, 1, 4, 1, 3, 2, 1, 4]
def baseStart_325437 : Nat := 118140960795 + 325437 * 2 ^ 59
def prefixEnd_325437 : Nat := 4983230072969 + 3 ^ 40 * 325437 * 2
def baseEnd_325437 : Nat := 74269157225488204418155

theorem tailTrace_325437 : CollatzResearch.WordTrace tailWord_325437 prefixEnd_325437 74269157225488204418155 := by
  unfold tailWord_325437
  simp only [CollatzResearch.WordTrace]
  refine ⟨11869662522004804059742565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7913108348003202706495043 11869662522004804059742565)
  ·
    refine ⟨2225561722875900761201731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11869662522004804059742565 2225561722875900761201731)
    ·
      refine ⟨3338342584313851141802597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2225561722875900761201731 3338342584313851141802597)
      ·
        refine ⟨625939234558847089087987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3338342584313851141802597 625939234558847089087987)
        ·
          refine ⟨938908851838270633631981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 625939234558847089087987 938908851838270633631981)
          ·
            refine ⟨352090819439351487611993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 938908851838270633631981 352090819439351487611993)
            ·
              refine ⟨264068114579513615708995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 352090819439351487611993 264068114579513615708995)
              ·
                refine ⟨396102171869270423563493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 264068114579513615708995 396102171869270423563493)
                ·
                  refine ⟨74269157225488204418155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 396102171869270423563493 74269157225488204418155)
                  ·
                    rfl

theorem cell21_325437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 3, 2, 1, 4].length) (baseStart_325437 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_325437 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_325437 prefixEnd_325437 := by exact prefixLift 325437
  have htrace : WordTrace (prefixWord ++ tailWord_325437) baseStart_325437 baseEnd_325437 := by
    simpa [prefixWord, tailWord_325437, baseEnd_325437] using wordTrace_append hprefix tailTrace_325437
  have hstable : (prefixWord ++ tailWord_325437).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_325437).length < 2 ^ (prefixWord ++ tailWord_325437).sum := by decide
  have hdescent : baseEnd_325437 < baseStart_325437 := by decide
  rcases family_descends (prefixWord ++ tailWord_325437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_325476 : List Nat := [2, 3, 1, 1, 14]
def baseStart_325476 : Nat := 118140960795 + 325476 * 2 ^ 59
def prefixEnd_325476 : Nat := 4983230072969 + 3 ^ 40 * 325476 * 2
def baseEnd_325476 : Nat := 917013056257195102075

theorem tailTrace_325476 : CollatzResearch.WordTrace tailWord_325476 prefixEnd_325476 917013056257195102075 := by
  unfold tailWord_325476
  simp only [CollatzResearch.WordTrace]
  refine ⟨5935542484431756860206141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7914056645909009146941521 5935542484431756860206141)
  ·
    refine ⟨2225828431661908822577303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5935542484431756860206141 2225828431661908822577303)
    ·
      refine ⟨3338742647492863233865955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2225828431661908822577303 3338742647492863233865955)
      ·
        refine ⟨5008113971239294850798933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3338742647492863233865955 5008113971239294850798933)
        ·
          refine ⟨917013056257195102075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 14 5008113971239294850798933 917013056257195102075)
          ·
            rfl

theorem cell21_325476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 14].length) (baseStart_325476 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_325476 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_325476 prefixEnd_325476 := by exact prefixLift 325476
  have htrace : WordTrace (prefixWord ++ tailWord_325476) baseStart_325476 baseEnd_325476 := by
    simpa [prefixWord, tailWord_325476, baseEnd_325476] using wordTrace_append hprefix tailTrace_325476
  have hstable : (prefixWord ++ tailWord_325476).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_325476).length < 2 ^ (prefixWord ++ tailWord_325476).sum := by decide
  have hdescent : baseEnd_325476 < baseStart_325476 := by decide
  rcases family_descends (prefixWord ++ tailWord_325476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_325479 : List Nat := [1, 1, 5, 1, 2, 1, 4, 2, 4]
def baseStart_325479 : Nat := 118140960795 + 325479 * 2 ^ 59
def prefixEnd_325479 : Nat := 4983230072969 + 3 ^ 40 * 325479 * 2
def baseEnd_325479 : Nat := 74278742197705464718069

theorem tailTrace_325479 : CollatzResearch.WordTrace tailWord_325479 prefixEnd_325479 74278742197705464718069 := by
  unfold tailWord_325479
  simp only [CollatzResearch.WordTrace]
  refine ⟨11871194387852645232771491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7914129591901763488514327 11871194387852645232771491)
  ·
    refine ⟨17806791581778967849157237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11871194387852645232771491 17806791581778967849157237)
    ·
      refine ⟨1669386710791778235858491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 17806791581778967849157237 1669386710791778235858491)
      ·
        refine ⟨2504080066187667353787737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1669386710791778235858491 2504080066187667353787737)
        ·
          refine ⟨1878060049640750515340803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2504080066187667353787737 1878060049640750515340803)
          ·
            refine ⟨2817090074461125773011205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1878060049640750515340803 2817090074461125773011205)
            ·
              refine ⟨528204388961461082439601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2817090074461125773011205 528204388961461082439601)
              ·
                refine ⟨396153291721095811829701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 528204388961461082439601 396153291721095811829701)
                ·
                  refine ⟨74278742197705464718069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 396153291721095811829701 74278742197705464718069)
                  ·
                    rfl

theorem cell21_325479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 4, 2, 4].length) (baseStart_325479 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_325479 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_325479 prefixEnd_325479 := by exact prefixLift 325479
  have htrace : WordTrace (prefixWord ++ tailWord_325479) baseStart_325479 baseEnd_325479 := by
    simpa [prefixWord, tailWord_325479, baseEnd_325479] using wordTrace_append hprefix tailTrace_325479
  have hstable : (prefixWord ++ tailWord_325479).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_325479).length < 2 ^ (prefixWord ++ tailWord_325479).sum := by decide
  have hdescent : baseEnd_325479 < baseStart_325479 := by decide
  rcases family_descends (prefixWord ++ tailWord_325479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_325507 : List Nat := [1, 1, 1, 3, 4, 2, 1, 1, 7]
def baseStart_325507 : Nat := 118140960795 + 325507 * 2 ^ 59
def prefixEnd_325507 : Nat := 4983230072969 + 3 ^ 40 * 325507 * 2
def baseEnd_325507 : Nat := 74285132179183638251345

theorem tailTrace_325507 : CollatzResearch.WordTrace tailWord_325507 prefixEnd_325507 74285132179183638251345 := by
  unfold tailWord_325507
  simp only [CollatzResearch.WordTrace]
  refine ⟨11872215631751206014790775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7914810421167470676527183 11872215631751206014790775)
  ·
    refine ⟨17808323447626809022186163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11872215631751206014790775 17808323447626809022186163)
    ·
      refine ⟨26712485171440213533279245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17808323447626809022186163 26712485171440213533279245)
      ·
        refine ⟨10017181939290080074979717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26712485171440213533279245 10017181939290080074979717)
        ·
          refine ⟨1878221613616890014058697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10017181939290080074979717 1878221613616890014058697)
          ·
            refine ⟨1408666210212667510544023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1878221613616890014058697 1408666210212667510544023)
            ·
              refine ⟨2112999315319001265816035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1408666210212667510544023 2112999315319001265816035)
              ·
                refine ⟨3169498972978501898724053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2112999315319001265816035 3169498972978501898724053)
                ·
                  refine ⟨74285132179183638251345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3169498972978501898724053 74285132179183638251345)
                  ·
                    rfl

theorem cell21_325507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 1, 1, 7].length) (baseStart_325507 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_325507 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_325507 prefixEnd_325507 := by exact prefixLift 325507
  have htrace : WordTrace (prefixWord ++ tailWord_325507) baseStart_325507 baseEnd_325507 := by
    simpa [prefixWord, tailWord_325507, baseEnd_325507] using wordTrace_append hprefix tailTrace_325507
  have hstable : (prefixWord ++ tailWord_325507).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_325507).length < 2 ^ (prefixWord ++ tailWord_325507).sum := by decide
  have hdescent : baseEnd_325507 < baseStart_325507 := by decide
  rcases family_descends (prefixWord ++ tailWord_325507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_325555 : List Nat := [1, 1, 1, 2, 3, 1, 7, 1, 4]
def baseStart_325555 : Nat := 118140960795 + 325555 * 2 ^ 59
def prefixEnd_325555 : Nat := 4983230072969 + 3 ^ 40 * 325555 * 2
def baseEnd_325555 : Nat := 74296086433146221451247

theorem tailTrace_325555 : CollatzResearch.WordTrace tailWord_325555 prefixEnd_325555 74296086433146221451247 := by
  unfold tailWord_325555
  simp only [CollatzResearch.WordTrace]
  refine ⟨11873966335577310212538119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7915977557051540141692079 11873966335577310212538119)
  ·
    refine ⟨17810949503365965318807179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11873966335577310212538119 17810949503365965318807179)
    ·
      refine ⟨26716424255048947978210769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17810949503365965318807179 26716424255048947978210769)
      ·
        refine ⟨20037318191286710983658077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26716424255048947978210769 20037318191286710983658077)
        ·
          refine ⟨7513994321732516618871779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20037318191286710983658077 7513994321732516618871779)
          ·
            refine ⟨11270991482598774928307669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7513994321732516618871779 11270991482598774928307669)
            ·
              refine ⟨264163862873408787382211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 11270991482598774928307669 264163862873408787382211)
              ·
                refine ⟨396245794310113181073317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 264163862873408787382211 396245794310113181073317)
                ·
                  refine ⟨74296086433146221451247, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 396245794310113181073317 74296086433146221451247)
                  ·
                    rfl

theorem cell21_325555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 7, 1, 4].length) (baseStart_325555 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_325555 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_325555 prefixEnd_325555 := by exact prefixLift 325555
  have htrace : WordTrace (prefixWord ++ tailWord_325555) baseStart_325555 baseEnd_325555 := by
    simpa [prefixWord, tailWord_325555, baseEnd_325555] using wordTrace_append hprefix tailTrace_325555
  have hstable : (prefixWord ++ tailWord_325555).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_325555).length < 2 ^ (prefixWord ++ tailWord_325555).sum := by decide
  have hdescent : baseEnd_325555 < baseStart_325555 := by decide
  rcases family_descends (prefixWord ++ tailWord_325555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_325586 : List Nat := [3, 2, 2, 3, 2, 2, 7]
def baseStart_325586 : Nat := 118140960795 + 325586 * 2 ^ 59
def prefixEnd_325586 : Nat := 4983230072969 + 3 ^ 40 * 325586 * 2
def baseEnd_325586 : Nat := 8255906783944117381613

theorem tailTrace_325586 : CollatzResearch.WordTrace tailWord_325586 prefixEnd_325586 8255906783944117381613 := by
  unfold tailWord_325586
  simp only [CollatzResearch.WordTrace]
  refine ⟨2968774249616250626729153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7916731332310001671277741 2968774249616250626729153)
  ·
    refine ⟨2226580687212187970046865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2968774249616250626729153 2226580687212187970046865)
    ·
      refine ⟨1669935515409140977535149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2226580687212187970046865 1669935515409140977535149)
      ·
        refine ⟨626225818278427866575681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1669935515409140977535149 626225818278427866575681)
        ·
          refine ⟨469669363708820899931761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 626225818278427866575681 469669363708820899931761)
          ·
            refine ⟨352252022781615674948821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 469669363708820899931761 352252022781615674948821)
            ·
              refine ⟨8255906783944117381613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 352252022781615674948821 8255906783944117381613)
              ·
                rfl

theorem cell21_325586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 2, 7].length) (baseStart_325586 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_325586 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_325586 prefixEnd_325586 := by exact prefixLift 325586
  have htrace : WordTrace (prefixWord ++ tailWord_325586) baseStart_325586 baseEnd_325586 := by
    simpa [prefixWord, tailWord_325586, baseEnd_325586] using wordTrace_append hprefix tailTrace_325586
  have hstable : (prefixWord ++ tailWord_325586).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_325586).length < 2 ^ (prefixWord ++ tailWord_325586).sum := by decide
  have hdescent : baseEnd_325586 < baseStart_325586 := by decide
  rcases family_descends (prefixWord ++ tailWord_325586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_325600 : List Nat := [2, 1, 1, 3, 1, 1, 1, 8, 3]
def baseStart_325600 : Nat := 118140960795 + 325600 * 2 ^ 59
def prefixEnd_325600 : Nat := 4983230072969 + 3 ^ 40 * 325600 * 2
def baseEnd_325600 : Nat := 74306356046236143201155

theorem tailTrace_325600 : CollatzResearch.WordTrace tailWord_325600 prefixEnd_325600 74306356046236143201155 := by
  unfold tailWord_325600
  simp only [CollatzResearch.WordTrace]
  refine ⟨5937803810207141448963127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7917071746942855265284169 5937803810207141448963127)
  ·
    refine ⟨8906705715310712173444691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5937803810207141448963127 8906705715310712173444691)
    ·
      refine ⟨13360058572966068260167037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8906705715310712173444691 13360058572966068260167037)
      ·
        refine ⟨5010021964862275597562639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13360058572966068260167037 5010021964862275597562639)
        ·
          refine ⟨7515032947293413396343959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5010021964862275597562639 7515032947293413396343959)
          ·
            refine ⟨11272549420940120094515939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7515032947293413396343959 11272549420940120094515939)
            ·
              refine ⟨16908824131410180141773909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11272549420940120094515939 16908824131410180141773909)
              ·
                refine ⟨198150282789963048536413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 16908824131410180141773909 198150282789963048536413)
                ·
                  refine ⟨74306356046236143201155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 198150282789963048536413 74306356046236143201155)
                  ·
                    rfl

theorem cell21_325600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 8, 3].length) (baseStart_325600 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_325600 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_325600 prefixEnd_325600 := by exact prefixLift 325600
  have htrace : WordTrace (prefixWord ++ tailWord_325600) baseStart_325600 baseEnd_325600 := by
    simpa [prefixWord, tailWord_325600, baseEnd_325600] using wordTrace_append hprefix tailTrace_325600
  have hstable : (prefixWord ++ tailWord_325600).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_325600).length < 2 ^ (prefixWord ++ tailWord_325600).sum := by decide
  have hdescent : baseEnd_325600 < baseStart_325600 := by decide
  rcases family_descends (prefixWord ++ tailWord_325600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_325628 : List Nat := [2, 2, 2, 1, 2, 2, 1, 9]
def baseStart_325628 : Nat := 118140960795 + 325628 * 2 ^ 59
def prefixEnd_325628 : Nat := 4983230072969 + 3 ^ 40 * 325628 * 2
def baseEnd_325628 : Nat := 24770915342571438911477

theorem tailTrace_325628 : CollatzResearch.WordTrace tailWord_325628 prefixEnd_325628 24770915342571438911477 := by
  unfold tailWord_325628
  simp only [CollatzResearch.WordTrace]
  refine ⟨5938314432156421839972769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7917752576208562453297025 5938314432156421839972769)
  ·
    refine ⟨4453735824117316379979577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5938314432156421839972769 4453735824117316379979577)
    ·
      refine ⟨3340301868087987284984683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4453735824117316379979577 3340301868087987284984683)
      ·
        refine ⟨5010452802131980927477025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3340301868087987284984683 5010452802131980927477025)
        ·
          refine ⟨3757839601598985695607769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5010452802131980927477025 3757839601598985695607769)
          ·
            refine ⟨2818379701199239271705827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3757839601598985695607769 2818379701199239271705827)
            ·
              refine ⟨4227569551798858907558741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2818379701199239271705827 4227569551798858907558741)
              ·
                refine ⟨24770915342571438911477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 4227569551798858907558741 24770915342571438911477)
                ·
                  rfl

theorem cell21_325628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 1, 9].length) (baseStart_325628 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_325628 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_325628 prefixEnd_325628 := by exact prefixLift 325628
  have htrace : WordTrace (prefixWord ++ tailWord_325628) baseStart_325628 baseEnd_325628 := by
    simpa [prefixWord, tailWord_325628, baseEnd_325628] using wordTrace_append hprefix tailTrace_325628
  have hstable : (prefixWord ++ tailWord_325628).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_325628).length < 2 ^ (prefixWord ++ tailWord_325628).sum := by decide
  have hdescent : baseEnd_325628 < baseStart_325628 := by decide
  rcases family_descends (prefixWord ++ tailWord_325628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan21Incremental
